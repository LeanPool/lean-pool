/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

/- Adapted for Lean Pool from roos-j/lean-trilinearht at
7b4209609e6a7fb9d9935973ee8541495f943660. Imports, names, proof organization and
Mathlib interfaces have been updated; original authorship is retained above. -/

public import LeanPool.TrilinearHilbertTransform.Auto.Sec152bTorusSizeFourierTests.ThreeCoreTest

/-!
# Trilinear Hilbert transform: three_core_noref_side
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
private def ThreeCoreNorefSideHfarallStatement : Prop :=
  ∀ (κ' : LocalKernelClass)
    (c₀ : ℕ)
    (A : ActiveSetup κ' c₀)
    (bf : A.BasicFamilies)
    (fp : bf.FamParams)
    (D : fp.SideInput)
    (_ : (2 : ℝ) ≤ D.S.Dstar)
    (_ : (1 : ℕ) ≤ D.S.Q0)
    (I : ℤ × ℤ)
    (G : bf.Grp)
    (Kt : ℕ)
    (_ : (↑D.S.Q0 : ℝ) * (2 : ℝ) ^ (Kt + (1 : ℕ)) ≤ D.S.Bstar)
    (h : ℕ)
    (l : Fin (4 : ℕ))
    (Fsel : (j : Fin (4 : ℕ)) → Finset ↥((D.Ms j G).alive (ancAt A.G (D.preAt I) (A.blkStart
      D.S.K I.1 - (4 : ℤ) * (↑D.S.K : ℤ)))))
    (a : Fin (4 : ℕ) → ℝ)
    (xs : ℝ)
    (_ : D.threeRefSet G I xs (h - D.SP.Δ) l a = ∅)
    (_ : (0 : ℝ) < dyadicGridLength A.G I.1)
    (_ : (0 : ℝ) < D.S.Dstar)
    (_ : ∀ (i : Fin (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim), (D.Ms (0 : Fin (4 : ℕ)) G).torusξ D.S
      (h - D.SP.Δ) i = (D.Ms (0 : Fin (4 : ℕ)) G).zc.θ i / ((↑D.S.Q0 : ℝ) * (↑((6 : ℕ) ^
      (h - D.SP.Δ)) : ℝ)))
    (nn : (j : Fin (4 : ℕ)) → ↥((D.Ms j G).alive (ancAt A.G (D.preAt I) (A.blkStart D.S.K I.1
      - (4 : ℤ) * (↑D.S.K : ℤ)))) → Fin (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim → ℤ)
    (_ : ∀ (j : Fin (4 : ℕ)), ∀ k ∈ sideOptF l Fsel j, ∀ (i : Fin (D.Ms (0 : Fin (4 : ℕ))
      G).zc.dim), |(↑(sideOptN nn j k i) : ℝ)| ≤ D.S.Dstar * D.S.Eh (h - D.SP.Δ))
    (_ : (6 : ℝ) ≤ D.S.A0)
    (_ : D.S.Bstar ≤ D.S.A0)
    (_ : ((∑ j : Fin (4 : ℕ), (↑(↑j : ℕ) : ℝ) * if j = l then (0 : ℝ) else a j) - (↑(↑l : ℕ)
      : ℝ) * ∑ j : Fin (4 : ℕ), if j = l then (0 : ℝ) else a j) = threeT l a),
  ∀ x ∈ frequencyBox ((D.Ms (0 : Fin (4 : ℕ)) G).zc.dim + (D.Ms (0 : Fin (4 : ℕ))
    G).zc.dim) ((2 : ℕ) ^ (Kt + (1 : ℕ))) ×ˢ Fintype.piFinset fun (j : Fin (4 : ℕ)) =>
    frequencyBox (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim ((2 : ℕ) ^ (Kt + (1 : ℕ))) ×ˢ
    sideOptF l Fsel j, D.U0 ≤ |dyadicGridLength A.G I.1 * ((∑ j : Fin (4 : ℕ), (↑(↑j :
    ℕ) : ℝ) * if j = l then (0 : ℝ) else a j) + ∑ i : Fin (D.Ms (0 : Fin (4 : ℕ))
    G).zc.dim, (↑(expP2 ((6 : ℕ) ^ (h - D.SP.Δ)) (D.S.Q0 * (6 : ℕ) ^ (h - D.SP.Δ))
    (sideOptN nn) x i) : ℝ) * ((D.Ms (0 : Fin (4 : ℕ)) G).zc.θ i / ((↑D.S.Q0 : ℝ) *
    (↑((6 : ℕ) ^ (h - D.SP.Δ)) : ℝ))) - (↑(↑l : ℕ) : ℝ) * ((∑ j : Fin (4 : ℕ), if j =
    l then (0 : ℝ) else a j) + ∑ i : Fin (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim, (↑(expP1
    ((6 : ℕ) ^ (h - D.SP.Δ)) (D.S.Q0 * (6 : ℕ) ^ (h - D.SP.Δ)) (sideOptN nn) x i) : ℝ)
    * ((D.Ms (0 : Fin (4 : ℕ)) G).zc.θ i / ((↑D.S.Q0 : ℝ) * (↑((6 : ℕ) ^ (h - D.SP.Δ))
    : ℝ)))))|

open scoped Classical in
private def ThreeCoreNorefSideConclusion9Statement : Prop :=
  ∀ (κ' : LocalKernelClass)
    (c₀ : ℕ)
    (A : ActiveSetup κ' c₀)
    (bf : A.BasicFamilies)
    (fp : bf.FamParams)
    (D : fp.SideInput)
    (_ : (1 : ℕ) ≤ D.S.Q0)
    (I : ℤ × ℤ)
    (_ : I ∈ A.cells)
    (G : bf.Grp)
    (δ : ℝ)
    (_ : (0 : ℝ) < δ)
    (_ : δ ≤ (1 / 8 : ℝ))
    (Cm : ℝ)
    (_ : (0 : ℝ) ≤ Cm)
    (δ'' : ℝ)
    (_ : (0 : ℝ) < δ'')
    (Kt : ℕ)
    (J : ℕ)
    (h : ℕ)
    (l : Fin (4 : ℕ))
    (Fsel : (j : Fin (4 : ℕ)) → Finset ↥((D.Ms j G).alive (ancAt A.G (D.preAt I) (A.blkStart
      D.S.K I.1 - (4 : ℤ) * (↑D.S.K : ℤ)))))
    (xs : ℝ)
    (X : ↥(ColumnL2 (bf.Lab ⊕ Fin fp.Mc)))
    (Aw : ℕ)
    (_ : (0 : ℝ) < dyadicGridLength A.G I.1)
    (_ : IsAdmissibleLocalKernel κ' (dyadicGridLeft A.G I.1 I.2) (dyadicGridLength A.G I.1)
      (A.w I))
    (f : (j : Fin (4 : ℕ)) → j ≠ l → ℝ → ℂ)
    (_ : ∀ (j : Fin (4 : ℕ)) (hj : j ≠ l), (Set.Ico (dyadicGridLeft A.G I.1 I.2)
      (dyadicGridLeft A.G I.1 I.2 + dyadicGridLength A.G I.1)).indicator (f j hj) =
      (Set.Ico (dyadicGridLeft A.G I.1 I.2) (dyadicGridLeft A.G I.1 I.2 +
      dyadicGridLength A.G I.1)).indicator fun (y : ℝ) => ∑ x ∈ Fsel j, D.c j G
      (A.blkStart D.S.K I.1) (D.preAt I) (↑x : (D.Ms j G).Md) * (D.Ms j G).wave (↑x :
      (D.Ms j G).Md) y)
    (ρc : Fin (4 : ℕ) → Fin (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim → ℝ)
    (nn : (j : Fin (4 : ℕ)) → ↥((D.Ms j G).alive (ancAt A.G (D.preAt I) (A.blkStart D.S.K I.1
      - (4 : ℤ) * (↑D.S.K : ℤ)))) → Fin (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim → ℤ)
    (fv : Fin (4 : ℕ) → ℝ → ℂ)
    (_ : fv l = augPhys X)
    (_ : ∀ (j : Fin (4 : ℕ)) (hj : j ≠ l), fv j = f j hj)
    (cα : (j : Fin (4 : ℕ)) → ↥((D.Ms j G).alive (ancAt A.G (D.preAt I) (A.blkStart D.S.K I.1
      - (4 : ℤ) * (↑D.S.K : ℤ)))) → ℂ)
    (_ : ∀ (j : Fin (4 : ℕ)) (x : ↥((D.Ms j G).alive (ancAt A.G (D.preAt I) (A.blkStart D.S.K
      I.1 - (4 : ℤ) * (↑D.S.K : ℤ))))), cα j x = D.c j G (A.blkStart D.S.K I.1) (D.preAt
      I) (↑x : (D.Ms j G).Md) * (↑((𝐞 : ℝ → Circle) ((D.Ms j G).phase (↑x : (D.Ms j
      G).Md) xs)) : ℂ))
    (_ : ∀ (j : Fin (4 : ℕ)), j ≠ l → sideOptF l Fsel j = Finset.map Function.Embedding.some
      (Fsel j))
    (cc0 : Fin (4 : ℕ) → (Fin (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim → ℤ) → ℂ)
    (_ : ∀ (j : Fin (4 : ℕ)) (w : Fin (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim → ℝ), ‖cutoffP δ (ρc
      j) w - ∑ v ∈ frequencyBox (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim ((2 : ℕ) ^ (Kt + (1 :
      ℕ))), cc0 j v * (↑((𝐞 : ℝ → Circle) (∑ i : Fin (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim,
      (↑(v i) : ℝ) * w i)) : ℂ)‖ ≤ cutTail (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim δ Kt)
    (_ : (4 : ℝ) ≤ D.U0)
    (_ : ‖localProgressionForm (dyadicGridLength A.G I.1) (A.w I) fv‖ ≤ (2 : ℝ) * ((2 : ℝ) *
      localKernelSupBound κ' * (((4 : ℝ) * (D.S.Dstar ^ (150 : ℕ))⁻¹ + (gaugeErr (D.Ms
      (0 : Fin (4 : ℕ)) G).zc.dim δ δ'' + (4 : ℝ) * ((1 : ℝ) + cutTail (D.Ms (0 : Fin (4
      : ℕ)) G).zc.dim δ Kt) ^ (3 : ℕ) * cutTail (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim δ Kt +
      ((1 : ℝ) + cutTail (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim δ Kt) ^ (4 : ℕ) * multTail
      (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim δ'' D.S.Q0 Cm Kt)) * ∏ j : Fin (4 : ℕ), ∑ k ∈
      sideOptF l Fsel j, ‖sideOptC cα j k‖) * ((dyadicGridLength A.G I.1)⁻¹ * ∫ (y : ℝ)
      in Set.Icc (dyadicGridLeft A.G I.1 I.2) (dyadicGridLeft A.G I.1 I.2 +
      dyadicGridLength A.G I.1), ‖fv l y‖) + (4 : ℝ) * ((dyadicGridLength A.G I.1)⁻¹ *
      (entryCU κ' J Aw * (D.U0 ^ J)⁻¹) * (2 : ℝ) ^ (Aw + (4 : ℕ)) * ((((1 : ℝ) +
      multTail (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim δ'' D.S.Q0 Cm Kt) * ((1 : ℝ) + cutTail
      (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim δ Kt) * ∏ i ∈ Finset.univ.erase l, (eLpNorm (fun
      (u : ↥(torusAnnihilator (rationalIntegerIntersection (d := (D.Ms 0 G).zc.dim) ⊥)))
      => coreG (D.S.Q0 * (6 : ℕ) ^ (h - D.SP.Δ)) ((2 : ℕ) ^ (Kt + (1 : ℕ))) (sideOptF l
      Fsel) (sideOptC cα) (sideOptN nn) (fun (j : Fin (4 : ℕ)) (v : Fin (D.Ms (0 : Fin
      (4 : ℕ)) G).zc.dim → ℤ) => cc0 j v * (↑((𝐞 : ℝ → Circle) (∑ i : Fin (D.Ms (0 : Fin
      (4 : ℕ)) G).zc.dim, (↑(v i) : ℝ) * ((D.Ms (0 : Fin (4 : ℕ)) G).zc.θ i * xs))) :
      ℂ)) i (↑u : StandardTorus (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim)) (2 : ℝ≥0∞)
      (torusAnnihilatorHaar (rationalIntegerIntersection (d := (D.Ms 0 G).zc.dim)
      ⊥))).toReal) * √(dyadicGridLength A.G I.1 * ∫ (y : ℝ) in dyadicGridLeft A.G I.1
      I.2..dyadicGridLeft A.G I.1 I.2 + dyadicGridLength A.G I.1, ‖fv l y‖ ^ (2 : ℕ))))
      + (multNorm (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim δ'' D.S.Q0 Cm * ∏ j : Fin (4 : ℕ),
      cutNorm (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim δ * ∑ k ∈ sideOptF l Fsel j, ‖sideOptC
      cα j k‖) * (((dyadicGridLength A.G I.1)⁻¹ * ∫ (y : ℝ) in Set.Ico (dyadicGridLeft
      A.G I.1 I.2) (dyadicGridLeft A.G I.1 I.2 + dyadicGridLength A.G I.1), ‖fv l y‖) *
      ((12 : ℝ) * (kerC κ' J * ((4 : ℝ) / D.U0) ^ (J - (2 : ℕ))))))),
  ‖(fp.Λc I : (Fin (4 : ℕ) → ↥(ColumnL2 (bf.Lab ⊕ Fin fp.Mc))) → ℂ)
        (Function.update
          (fun (j : Fin (4 : ℕ)) =>
            D.compSub j G I (Finset.map { toFun := Subtype.val, inj' := Subtype.val_injective }
              (Fsel j)))
          l X)‖ ≤
    (2 : ℝ) *
      ((2 : ℝ) * localKernelSupBound κ' *
              (((4 : ℝ) * (D.S.Dstar ^ (150 : ℕ))⁻¹ +
                  (gaugeErr (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim δ δ'' +
                      (4 : ℝ) * ((1 : ℝ) + cutTail (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim δ Kt) ^ (3
                        : ℕ) *
                        cutTail (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim δ Kt +
                    ((1 : ℝ) + cutTail (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim δ Kt) ^ (4 : ℕ) *
                      multTail (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim δ'' D.S.Q0 Cm Kt)) *
                ∏ j ∈ Finset.univ.erase l, D.coefSum G I j (Fsel j)) *
            ((dyadicGridLength A.G I.1)⁻¹ *
              ∫ (y : ℝ) in Set.Icc (dyadicGridLeft A.G I.1 I.2) (dyadicGridLeft A.G I.1 I.2 +
                dyadicGridLength A.G I.1),
                ‖augPhys X y‖) +
          (4 : ℝ) *
            ((dyadicGridLength A.G I.1)⁻¹ * (entryCU κ' J Aw * (D.U0 ^ J)⁻¹) * (2 : ℝ) ^ (Aw +
              (4 : ℕ)) *
              ((((1 : ℝ) + multTail (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim δ'' D.S.Q0 Cm Kt) *
                    ((1 : ℝ) + cutTail (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim δ Kt) *
                  ∏ j ∈ Finset.univ.erase l,
                    ((1 : ℝ) + cutTail (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim δ Kt) * D.coefSum G I j
                      (Fsel j)) *
                √(dyadicGridLength A.G I.1 *
                    ∫ (y : ℝ) in dyadicGridLeft A.G I.1 I.2..dyadicGridLeft A.G I.1 I.2 +
                      dyadicGridLength A.G I.1,
                      ‖augPhys X y‖ ^ (2 : ℕ)))) +
        multNorm (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim δ'' D.S.Q0 Cm *
            (cutNorm (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim δ *
              ∏ j ∈ Finset.univ.erase l, cutNorm (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim δ * D.coefSum
                G I j (Fsel j)) *
          (((dyadicGridLength A.G I.1)⁻¹ *
              ∫ (y : ℝ) in Set.Ico (dyadicGridLeft A.G I.1 I.2) (dyadicGridLeft A.G I.1 I.2 +
                dyadicGridLength A.G I.1),
                ‖augPhys X y‖) *
            ((12 : ℝ) * (kerC κ' J * ((4 : ℝ) / D.U0) ^ (J - (2 : ℕ))))))

open scoped Classical in
private def ThreeCoreNorefSideStage1Statement : Prop :=
  ∀ (κ' : LocalKernelClass)
    (c₀ : ℕ)
    (A : ActiveSetup κ' c₀)
    (bf : A.BasicFamilies)
    (fp : bf.FamParams)
    (D : fp.SideInput)
    (_ : (2 : ℝ) ≤ D.S.Dstar)
    (_ : (1 : ℕ) ≤ D.S.Q0)
    (I : ℤ × ℤ)
    (_ : I ∈ A.cells)
    (G : bf.Grp)
    (δ : ℝ)
    (_ : (0 : ℝ) < δ)
    (_ : (8 : ℝ) * (↑(D.Ms (0 : Fin (4 : ℕ)) G).zc.dim : ℝ) * δ ≤ (1 : ℝ))
    (_ : δ ≤ (1 / 8 : ℝ))
    (_ : ∀ (j : Fin (4 : ℕ)), (D.Ms j G).δc = δ)
    (_ : ∀ (j : Fin (4 : ℕ)), (D.Ms j G).cl = slotCoeff j)
    (_ : ∀ (a b : Fin (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim), ∃ (k : ℤ), (↑D.S.Q0 : ℝ) * (↑((D.Ms
      (0 : Fin (4 : ℕ)) G).zc.C a b) : ℝ) = (↑k : ℝ))
    (Cm : ℝ)
    (_ : (0 : ℝ) ≤ Cm)
    (_ : ∀ (a b : Fin (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim), |(↑((D.Ms (0 : Fin (4 : ℕ)) G).zc.C
      a b) : ℝ)| ≤ Cm)
    (δ'' : ℝ)
    (_ : (0 : ℝ) < δ'')
    (Kt : ℕ)
    (_ : (↑D.S.Q0 : ℝ) * (2 : ℝ) ^ (Kt + (1 : ℕ)) ≤ D.S.Bstar)
    (J : ℕ)
    (_ : (2 : ℕ) ≤ J)
    (h : ℕ)
    (l : Fin (4 : ℕ))
    (Fsel : (j : Fin (4 : ℕ)) → Finset ↥((D.Ms j G).alive (ancAt A.G (D.preAt I) (A.blkStart
      D.S.K I.1 - (4 : ℤ) * (↑D.S.K : ℤ)))))
    (a : Fin (4 : ℕ) → ℝ)
    (xs : ℝ)
    (_ : xs ∈ dyadicGridCell A.G I.1 I.2)
    (_ : D.threeRefSet G I xs (h - D.SP.Δ) l a = ∅)
    (X : ↥(ColumnL2 (bf.Lab ⊕ Fin fp.Mc)))
    (Aw : ℕ)
    (_ : (1 : ℕ) ≤ Aw)
    (_ : (0 : ℝ) < dyadicGridLength A.G I.1)
    (_ : IsAdmissibleLocalKernel κ' (dyadicGridLeft A.G I.1 I.2) (dyadicGridLength A.G I.1)
      (A.w I))
    (_ : (0 : ℝ) < D.S.Dstar)
    (_ : (0 : ℕ) < D.S.Q0)
    (_ : (0 : ℝ) ≤ (D.S.Dstar ^ (150 : ℕ))⁻¹)
    (_ : ∀ (i : Fin (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim), (D.Ms (0 : Fin (4 : ℕ)) G).torusξ D.S
      (h - D.SP.Δ) i = (D.Ms (0 : Fin (4 : ℕ)) G).zc.θ i / ((↑D.S.Q0 : ℝ) * (↑((6 : ℕ) ^
      (h - D.SP.Δ)) : ℝ)))
    (ρ' : (j : Fin (4 : ℕ)) → j ≠ l → Fin (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim → ℝ)
    (n' : (j : Fin (4 : ℕ)) → j ≠ l → ↥((D.Ms j G).alive (ancAt A.G (D.preAt I) (A.blkStart
      D.S.K I.1 - (4 : ℤ) * (↑D.S.K : ℤ)))) → Fin (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim → ℤ)
    (f : (j : Fin (4 : ℕ)) → j ≠ l → ℝ → ℂ)
    (_ : ∀ (j : Fin (4 : ℕ)) (hj : j ≠ l), ∀ y ∈ Set.Icc (dyadicGridLeft A.G I.1 I.2)
      (dyadicGridLeft A.G I.1 I.2 + dyadicGridLength A.G I.1), ‖f j hj y - (↑(centerCut
      (D.Ms (0 : Fin (4 : ℕ)) G).zc (D.Ms j G).δc (ρ' j hj) y) : ℂ) * (↑((𝐞 : ℝ →
      Circle) ((↑(D.Ms j G).cl : ℝ) * centerPhase (D.Ms (0 : Fin (4 : ℕ)) G).zc (ρ' j
      hj) y)) : ℂ) * ((↑((𝐞 : ℝ → Circle) (a j * (y - xs))) : ℂ) * ∑ x ∈ Fsel j, D.c j G
      (A.blkStart D.S.K I.1) (D.preAt I) (↑x : (D.Ms j G).Md) * (↑((𝐞 : ℝ → Circle)
      ((D.Ms j G).phase (↑x : (D.Ms j G).Md) xs)) : ℂ) * torusCharacter (n' j hj x)
      (torusMk fun (i : Fin (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim) => (D.Ms (0 : Fin (4 :
      ℕ)) G).zc.θ i / ((↑D.S.Q0 : ℝ) * (↑((6 : ℕ) ^ (h - D.SP.Δ)) : ℝ)) * (y - xs)))‖ ≤
      (D.S.Dstar ^ (150 : ℕ))⁻¹ * ∑ x ∈ Fsel j, ‖D.c j G (A.blkStart D.S.K I.1) (D.preAt
      I) (↑x : (D.Ms j G).Md) * (↑((𝐞 : ℝ → Circle) ((D.Ms j G).phase (↑x : (D.Ms j
      G).Md) xs)) : ℂ)‖)
    (_ : ∀ (j : Fin (4 : ℕ)) (hj : j ≠ l), ∀ y ∈ Set.Icc (dyadicGridLeft A.G I.1 I.2)
      (dyadicGridLeft A.G I.1 I.2 + dyadicGridLength A.G I.1), ‖f j hj y‖ ≤ ∑ x ∈ Fsel
      j, ‖D.c j G (A.blkStart D.S.K I.1) (D.preAt I) (↑x : (D.Ms j G).Md) * (↑((𝐞 : ℝ →
      Circle) ((D.Ms j G).phase (↑x : (D.Ms j G).Md) xs)) : ℂ)‖)
    (_ : ∀ (j : Fin (4 : ℕ)) (hj : j ≠ l), (Set.Ico (dyadicGridLeft A.G I.1 I.2)
      (dyadicGridLeft A.G I.1 I.2 + dyadicGridLength A.G I.1)).indicator (f j hj) =
      (Set.Ico (dyadicGridLeft A.G I.1 I.2) (dyadicGridLeft A.G I.1 I.2 +
      dyadicGridLength A.G I.1)).indicator fun (y : ℝ) => ∑ x ∈ Fsel j, D.c j G
      (A.blkStart D.S.K I.1) (D.preAt I) (↑x : (D.Ms j G).Md) * (D.Ms j G).wave (↑x :
      (D.Ms j G).Md) y)
    (ρc : Fin (4 : ℕ) → Fin (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim → ℝ)
    (_ : ∀ (j : Fin (4 : ℕ)) (k : Fin (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim), ρc j k ∈ Set.Icc (0
      : ℝ) (1 : ℝ))
    (_ : ∀ (j : Fin (4 : ℕ)) (hj : j ≠ l), ρc j = ρ' j hj)
    (nn : (j : Fin (4 : ℕ)) → ↥((D.Ms j G).alive (ancAt A.G (D.preAt I) (A.blkStart D.S.K I.1
      - (4 : ℤ) * (↑D.S.K : ℤ)))) → Fin (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim → ℤ)
    (_ : ∀ (j : Fin (4 : ℕ)) (hj : j ≠ l) (x : ↥((D.Ms j G).alive (ancAt A.G (D.preAt I)
      (A.blkStart D.S.K I.1 - (4 : ℤ) * (↑D.S.K : ℤ))))), nn j x = n' j hj x)
    (fv : Fin (4 : ℕ) → ℝ → ℂ)
    (_ : fv l = augPhys X)
    (_ : ∀ (j : Fin (4 : ℕ)) (hj : j ≠ l), fv j = f j hj)
    (cα : (j : Fin (4 : ℕ)) → ↥((D.Ms j G).alive (ancAt A.G (D.preAt I) (A.blkStart D.S.K I.1
      - (4 : ℤ) * (↑D.S.K : ℤ)))) → ℂ)
    (_ : ∀ (j : Fin (4 : ℕ)) (x : ↥((D.Ms j G).alive (ancAt A.G (D.preAt I) (A.blkStart D.S.K
      I.1 - (4 : ℤ) * (↑D.S.K : ℤ))))), cα j x = D.c j G (A.blkStart D.S.K I.1) (D.preAt
      I) (↑x : (D.Ms j G).Md) * (↑((𝐞 : ℝ → Circle) ((D.Ms j G).phase (↑x : (D.Ms j
      G).Md) xs)) : ℂ))
    (_ : ∀ (j : Fin (4 : ℕ)), j ≠ l → sideOptF l Fsel j = Finset.map Function.Embedding.some
      (Fsel j))
    (_ : Measurable (augPhys X))
    (_ : MemLp (augPhys X) (2 : ℝ≥0∞) (volume.restrict (Set.Ioc (dyadicGridLeft A.G I.1 I.2)
      (dyadicGridLeft A.G I.1 I.2 + dyadicGridLength A.G I.1))))
    (_ : Integrable (fun (zz : ℝ × ℝ) => A.w I zz * ∏ j : Fin (4 : ℕ), fv j
      (realProgressionCoordinate j zz)) volume)
    (_ : ∀ (ρ'' : Fin (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim → ℝ), Integrable (fun (zz : ℝ × ℝ) =>
      A.w I zz * ∏ j : Fin (4 : ℕ), Function.update fv l (fun (y : ℝ) => (↑(centerCut
      (D.Ms (0 : Fin (4 : ℕ)) G).zc δ ρ'' y) : ℂ) * fv l y) j (realProgressionCoordinate
      j zz)) volume)
    (cc0 : Fin (4 : ℕ) → (Fin (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim → ℤ) → ℂ)
    (_ : ∀ (j : Fin (4 : ℕ)) (v : Fin (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim → ℤ), ‖cc0 j v‖ ≤ (1
      : ℝ))
    (_ : ∀ (j : Fin (4 : ℕ)) (s : Finset (Fin (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim → ℤ)), ∑ v ∈
      s, ‖cc0 j v‖ ≤ cutNorm (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim δ)
    (_ : ∀ (j : Fin (4 : ℕ)) (w : Fin (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim → ℝ), ‖cutoffP δ (ρc
      j) w - ∑ v ∈ frequencyBox (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim ((2 : ℕ) ^ (Kt + (1 :
      ℕ))), cc0 j v * (↑((𝐞 : ℝ → Circle) (∑ i : Fin (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim,
      (↑(v i) : ℝ) * w i)) : ℂ)‖ ≤ cutTail (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim δ Kt)
    (_ : ∀ (j : Fin (4 : ℕ)), ∀ k ∈ sideOptF l Fsel j, ∀ (i : Fin (D.Ms (0 : Fin (4 : ℕ))
      G).zc.dim), |(↑(sideOptN nn j k i) : ℝ)| ≤ D.S.Dstar * D.S.Eh (h - D.SP.Δ))
    (_ : (6 : ℝ) ≤ D.S.A0)
    (_ : D.S.Bstar ≤ D.S.A0)
    (_ : ((∑ j : Fin (4 : ℕ), (↑(↑j : ℕ) : ℝ) * if j = l then (0 : ℝ) else a j) - (↑(↑l : ℕ)
      : ℝ) * ∑ j : Fin (4 : ℕ), if j = l then (0 : ℝ) else a j) = threeT l a),
  ‖(fp.Λc I : (Fin (4 : ℕ) → ↥(ColumnL2 (bf.Lab ⊕ Fin fp.Mc))) → ℂ)
        (Function.update
          (fun (j : Fin (4 : ℕ)) =>
            D.compSub j G I (Finset.map { toFun := Subtype.val, inj' := Subtype.val_injective }
              (Fsel j)))
          l X)‖ ≤
    (2 : ℝ) *
      ((2 : ℝ) * localKernelSupBound κ' *
              (((4 : ℝ) * (D.S.Dstar ^ (150 : ℕ))⁻¹ +
                  (gaugeErr (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim δ δ'' +
                      (4 : ℝ) * ((1 : ℝ) + cutTail (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim δ Kt) ^ (3
                        : ℕ) *
                        cutTail (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim δ Kt +
                    ((1 : ℝ) + cutTail (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim δ Kt) ^ (4 : ℕ) *
                      multTail (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim δ'' D.S.Q0 Cm Kt)) *
                ∏ j ∈ Finset.univ.erase l, D.coefSum G I j (Fsel j)) *
            ((dyadicGridLength A.G I.1)⁻¹ *
              ∫ (y : ℝ) in Set.Icc (dyadicGridLeft A.G I.1 I.2) (dyadicGridLeft A.G I.1 I.2 +
                dyadicGridLength A.G I.1),
                ‖augPhys X y‖) +
          (4 : ℝ) *
            ((dyadicGridLength A.G I.1)⁻¹ * (entryCU κ' J Aw * (D.U0 ^ J)⁻¹) * (2 : ℝ) ^ (Aw +
              (4 : ℕ)) *
              ((((1 : ℝ) + multTail (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim δ'' D.S.Q0 Cm Kt) *
                    ((1 : ℝ) + cutTail (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim δ Kt) *
                  ∏ j ∈ Finset.univ.erase l,
                    ((1 : ℝ) + cutTail (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim δ Kt) * D.coefSum G I j
                      (Fsel j)) *
                √(dyadicGridLength A.G I.1 *
                    ∫ (y : ℝ) in dyadicGridLeft A.G I.1 I.2..dyadicGridLeft A.G I.1 I.2 +
                      dyadicGridLength A.G I.1,
                      ‖augPhys X y‖ ^ (2 : ℕ)))) +
        multNorm (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim δ'' D.S.Q0 Cm *
            (cutNorm (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim δ *
              ∏ j ∈ Finset.univ.erase l, cutNorm (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim δ * D.coefSum
                G I j (Fsel j)) *
          (((dyadicGridLength A.G I.1)⁻¹ *
              ∫ (y : ℝ) in Set.Ico (dyadicGridLeft A.G I.1 I.2) (dyadicGridLeft A.G I.1 I.2 +
                dyadicGridLength A.G I.1),
                ‖augPhys X y‖) *
            ((12 : ℝ) * (kerC κ' J * ((4 : ℝ) / D.U0) ^ (J - (2 : ℕ))))))

private theorem three_core_noref_side_hfarall : ThreeCoreNorefSideHfarallStatement := by
  classical
  intro κ' c₀ A bf fp D hD hQ I G Kt hQB h l Fsel a xs hnoref hr hDp hξ nn hnn hA6 hBA hγT x hx
  by_contra hlt
  push Not at hlt
  have hb := fun i => expP_fullBox D.S hA6 hBA hD hQ hQB (sideOptF l Fsel) (sideOptN nn) hnn x
    hx l i
  have hmem : expP2 (6 ^ (h - D.SP.Δ)) (D.S.Q0 * 6 ^ (h - D.SP.Δ)) (sideOptN nn) x -
      ((l : ℕ) : ℤ) • expP1 (6 ^ (h - D.SP.Δ)) (D.S.Q0 * 6 ^ (h - D.SP.Δ)) (sideOptN nn) x ∈
      D.threeRefSet G I xs (h - D.SP.Δ) l a := by
    unfold threeRefSet
    refine Finset.mem_filter.mpr ⟨(D.mem_fullBox hDp.le).mpr fun i => (hb i).2, ?_⟩
    have e : threeT l a + ∑ i, ((expP2 (6 ^ (h - D.SP.Δ)) (D.S.Q0 * 6 ^ (h - D.SP.Δ))
        (sideOptN nn) x - ((l : ℕ) : ℤ) • expP1 (6 ^ (h - D.SP.Δ))
          (D.S.Q0 * 6 ^ (h - D.SP.Δ)) (sideOptN nn) x) i : ℝ) *
        (D.Ms 0 G).torusξ D.S (h - D.SP.Δ) i =
        (∑ j : Fin 4, ((j : ℕ) : ℝ) * (if j = l then 0 else a j) +
          ∑ i, (expP2 (6 ^ (h - D.SP.Δ)) (D.S.Q0 * 6 ^ (h - D.SP.Δ)) (sideOptN nn) x i : ℝ) *
            ((D.Ms 0 G).zc.θ i / (D.S.Q0 * (6 ^ (h - D.SP.Δ) : ℕ)))) -
        ((l : ℕ) : ℝ) * (∑ j, (if j = l then 0 else a j) +
          ∑ i, (expP1 (6 ^ (h - D.SP.Δ)) (D.S.Q0 * 6 ^ (h - D.SP.Δ)) (sideOptN nn) x i : ℝ) *
            ((D.Ms 0 G).zc.θ i / (D.S.Q0 * (6 ^ (h - D.SP.Δ) : ℕ)))) := by
      rw [← hγT]
      simp only [hξ, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Int.cast_sub, Int.cast_mul,
        Int.cast_natCast, sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]
      ring
    rw [e]
    have := hlt.le
    rw [abs_mul, abs_of_pos hr] at this
    exact this
  rw [hnoref] at hmem
  exact Finset.notMem_empty _ hmem

private theorem three_core_noref_side_conclusion_9 : ThreeCoreNorefSideConclusion9Statement := by
  classical
  intro κ' c₀ A bf fp D hQ I hI G δ hδ hδ8 Cm hCm0 δ'' hδ'' Kt J h l Fsel xs X Aw hr hw f hind ρc
    nn fv hfvl hfvj cα hcα hFj cc0 hccT hU4 key
  -- the cell form is the local form of the transported inputs
  have hΛc : fp.Λc I (Function.update (fun j => D.compSub j G I
      ((Fsel j).map ⟨Subtype.val, Subtype.val_injective⟩)) l X) =
      localProgressionForm (dyadicGridLength A.G I.1) (A.w I) fv := by
    rw [fp.Λc_apply hI]
    have e1 : ∀ j, augPhys (Function.update (fun j => D.compSub j G I
        ((Fsel j).map ⟨Subtype.val, Subtype.val_injective⟩)) l X j) =ᵐ[volume]
        Function.update (fun j => (Set.Ico (dyadicGridLeft A.G I.1 I.2)
          (dyadicGridLeft A.G I.1 I.2 + dyadicGridLength A.G I.1)).indicator
          (fun y => ∑ x ∈ Fsel j, D.c j G (A.blkStart D.S.K I.1) (D.preAt I) x.1 *
            (D.Ms j G).wave x.1 y)) l (augPhys X) j := fun j => by
      rw [apply_update_augPhys]
      by_cases hj : j = l
      · rw [hj, Function.update_self, Function.update_self]
      · rw [Function.update_of_ne hj, Function.update_of_ne hj]
        refine (D.augPhys_compSub j G I _).trans (Filter.EventuallyEq.of_eq ?_)
        congr 1
        funext y
        exact Finset.sum_map _ _ _
    rw [localProgressionForm_congr_ae _ _ e1, ← form_indicator_cell hr hw fv,
      ← form_indicator_cell hr hw (Function.update _ l (augPhys X))]
    congr 1
    funext j
    by_cases hj : j = l
    · rw [hj, Function.update_self, hfvl]
    · rw [Function.update_of_ne hj, hfvj j hj, Set.indicator_indicator, Set.inter_self]
      exact (hind j hj).symm
  -- the coefficient sums with the side term `1`
  have hsum1 : ∀ j, j ≠ l → ∑ k ∈ sideOptF l Fsel j, ‖sideOptC cα j k‖ =
      ∑ x ∈ Fsel j, ‖D.c j G (A.blkStart D.S.K I.1) (D.preAt I) x.1‖ := fun j hj => by
    rw [hFj j hj, Finset.sum_map]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [Function.Embedding.some_apply, sideOptC, Option.elim, hcα, norm_mul,
      Circle.norm_coe, mul_one]
  have hsuml : ∑ k ∈ sideOptF l Fsel l, ‖sideOptC cα l k‖ = 1 := by
    simp [sideOptF, sideOptC]
  have hPS : ∏ j, ∑ k ∈ sideOptF l Fsel j, ‖sideOptC cα j k‖ = ∏ j ∈ Finset.univ.erase l,
      ∑ x ∈ Fsel j, ‖D.c j G (A.blkStart D.S.K I.1) (D.preAt I) x.1‖ := by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ l), hsuml, one_mul]
    exact Finset.prod_congr rfl fun j hj => hsum1 j (Finset.ne_of_mem_erase hj)
  have hPN : ∏ j, (cutNorm (D.Ms 0 G).zc.dim δ * ∑ k ∈ sideOptF l Fsel j,
      ‖sideOptC cα j k‖) = cutNorm (D.Ms 0 G).zc.dim δ * ∏ j ∈ Finset.univ.erase l,
        (cutNorm (D.Ms 0 G).zc.dim δ *
          ∑ x ∈ Fsel j, ‖D.c j G (A.blkStart D.S.K I.1) (D.preAt I) x.1‖) := by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ l), hsuml, mul_one]
    congr 1
    exact Finset.prod_congr rfl fun j hj => by rw [hsum1 j (Finset.ne_of_mem_erase hj)]
  -- the truncated core torus sizes on the full torus
  have hG : ∀ j ∈ Finset.univ.erase l, (eLpNorm (fun u : torusAnnihilator
      (rationalIntegerIntersection (⊥ : Submodule ℚ (Fin (D.Ms 0 G).zc.dim → ℚ))) =>
      coreG (D.S.Q0 * 6 ^ (h - D.SP.Δ)) (2 ^ (Kt + 1)) (sideOptF l Fsel) (sideOptC cα)
        (sideOptN nn) (fun j v => cc0 j v *
          (Real.fourierChar (∑ i, (v i : ℝ) * ((D.Ms 0 G).zc.θ i * xs)) : ℂ)) j u) 2
      (torusAnnihilatorHaar (rationalIntegerIntersection
        (⊥ : Submodule ℚ (Fin (D.Ms 0 G).zc.dim → ℚ))))).toReal ≤
      (1 + cutTail (D.Ms 0 G).zc.dim δ Kt) *
        ∑ x ∈ Fsel j, ‖D.c j G (A.blkStart D.S.K I.1) (D.preAt I) x.1‖ := fun j hj' => by
    have hj := Finset.ne_of_mem_erase hj'
    have hτ0 := cutTail_nonneg (D.Ms 0 G).zc.dim hδ Kt
    have h1 := coreG_eLpNorm_le (⊥ : Submodule ℚ (Fin (D.Ms 0 G).zc.dim → ℚ))
      (D.S.Q0 * 6 ^ (h - D.SP.Δ)) (2 ^ (Kt + 1)) (sideOptF l Fsel) (sideOptC cα) (sideOptN nn)
      (fun j v => cc0 j v *
        (Real.fourierChar (∑ i, (v i : ℝ) * ((D.Ms 0 G).zc.θ i * xs)) : ℂ)) j
      (M := 1 + cutTail (D.Ms 0 G).zc.dim δ Kt) (by linarith only [hτ0])
      (trunc_cut_sup (ρc j) Kt (cc0 j) (hccT j) (D.Ms 0 G).zc.θ xs
        (D.S.Q0 * 6 ^ (h - D.SP.Δ)))
    have h2 := eLpNorm_charSum_le (⊥ : Submodule ℚ (Fin (D.Ms 0 G).zc.dim → ℚ))
      (sideOptF l Fsel j) (sideOptC cα j) (sideOptN nn j)
    rw [hsum1 j hj] at h2
    exact h1.trans (mul_le_mul_of_nonneg_left h2 (by linarith only [hτ0]))
  have hτ0 := cutTail_nonneg (D.Ms 0 G).zc.dim hδ Kt
  have hτm0 : 0 ≤ multTail (D.Ms 0 G).zc.dim δ'' D.S.Q0 Cm Kt := by
    unfold multTail
    have := profR_nonneg hδ'' ((D.Ms 0 G).zc.dim + (D.Ms 0 G).zc.dim + 1)
    positivity
  have hW0 : (0 : ℝ) ≤ (1 + multTail (D.Ms 0 G).zc.dim δ'' D.S.Q0 Cm Kt) *
      (1 + cutTail (D.Ms 0 G).zc.dim δ Kt) := mul_nonneg (by linarith only [hτm0]) (by linarith)
  have hQW := mul_le_mul_of_nonneg_left
    (Finset.prod_le_prod₀ (fun _ _ => ENNReal.toReal_nonneg) hG) hW0
  rw [hfvl, hPS, hPN] at key
  rw [hΛc]
  refine key.trans (mul_le_mul_of_nonneg_left (add_le_add (add_le_add le_rfl ?_) le_rfl)
    (by norm_num))
  have hc : 0 ≤ (dyadicGridLength A.G I.1)⁻¹ * (entryCU κ' J Aw * (D.U0 ^ J)⁻¹) *
      2 ^ (Aw + 4) := by
    have := entryCU_nonneg hr hw J Aw
    have : 0 < D.U0 ^ J := pow_pos (by linarith) _
    have := inv_nonneg.mpr hr.le
    positivity
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hQW (Real.sqrt_nonneg _)) hc) (by norm_num)

private theorem three_core_noref_side_stage_1 : ThreeCoreNorefSideStage1Statement := by
  classical
  intro κ' c₀ A bf fp D hD hQ I hI G δ hδ hdδ hδ8 hδc hcl hQC Cm hCm0 hCm δ'' hδ'' Kt hQB J hJ h l
    Fsel a xs hxs hnoref X Aw hAw hr hw hDp hQ0 hη hξ ρ' n' f hfa hfb hind ρc hρc hρcj nn hnnj fv
    hfvl hfvj cα hcα hFj hXm hL2X hfi hfiρ cc0 hcc0 hccN hccT hnn hA6 hBA hγT
  have hfarall : ∀ x ∈ frequencyBox ((D.Ms 0 G).zc.dim + (D.Ms 0 G).zc.dim) (2 ^ (Kt + 1)) ×ˢ
      Fintype.piFinset (fun j => frequencyBox (D.Ms 0 G).zc.dim (2 ^ (Kt + 1)) ×ˢ
        sideOptF l Fsel j),
      D.U0 ≤ |dyadicGridLength A.G I.1 * ((∑ j : Fin 4, ((j : ℕ) : ℝ) *
          (if j = l then 0 else a j) +
          ∑ i, (expP2 (6 ^ (h - D.SP.Δ)) (D.S.Q0 * 6 ^ (h - D.SP.Δ)) (sideOptN nn) x i : ℝ) *
            ((D.Ms 0 G).zc.θ i / (D.S.Q0 * (6 ^ (h - D.SP.Δ) : ℕ)))) -
        ((l : ℕ) : ℝ) * (∑ j, (if j = l then 0 else a j) +
          ∑ i, (expP1 (6 ^ (h - D.SP.Δ)) (D.S.Q0 * 6 ^ (h - D.SP.Δ)) (sideOptN nn) x i : ℝ) *
            ((D.Ms 0 G).zc.θ i / (D.S.Q0 * (6 ^ (h - D.SP.Δ) : ℕ)))))| := by
    expose_names
    exact @three_core_noref_side_hfarall κ' c₀ A bf fp D hD hQ I G Kt hQB h l Fsel a xs hnoref hr
      hDp hξ nn hnn hA6 hBA hγT
  have hU4 : 4 ≤ D.U0 := by
    unfold U0
    calc (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ D.S.Dstar ^ 2 := pow_le_pow_left₀ (by norm_num) hD 2
      _ ≤ D.S.Dstar ^ 250 := pow_le_pow_right₀ (by linarith) (by norm_num)
  have key := three_core_noref_of hr hw (D.Ms 0 G).zc hδ hδ'' hdδ hδ8 ρc hρc hQ0 hQC hCm0 hCm
    (L := 6 ^ (h - D.SP.Δ)) (pow_pos (by norm_num) _) Kt ⟨hxs.1, hxs.2.le⟩ l
    (fun j => if j = l then 0 else a j) (by simp)
    (sideOptF l Fsel) (sideOptC cα) (sideOptN nn) (k₀ := none) (by simp [sideOptF]) rfl rfl fv
    (by rw [hfvl]; exact hXm) (by rw [hfvl]; exact hL2X) hfi hfiρ hη
    (fun j hj y hy => ?_) (fun j hj y hy => ?_) cc0 hcc0 hccN (fun j _ w => hccT j w) hU4
    hfarall hJ Aw hAw
  · expose_names
    exact @three_core_noref_side_conclusion_9 κ' c₀ A bf fp D hQ I hI G δ hδ hδ8 Cm hCm0 δ'' hδ''
      Kt J h l Fsel xs X Aw hr hw f hind ρc nn fv hfvl hfvj cα hcα hFj cc0 hccT hU4 key
  · rw [hfvj j hj, hρcj j hj, hFj j hj, Finset.sum_map, Finset.sum_map]
    simp only [Function.Embedding.some_apply, sideOptC, sideOptN, Option.elim, hnnj j hj, hcα,
      hj, ↓reduceIte]
    have h1 := hfa j hj y hy
    rw [hδc j, hcl j] at h1
    exact h1
  · rw [hfvj j hj, hFj j hj, Finset.sum_map]
    simp only [Function.Embedding.some_apply, sideOptC, Option.elim, hcα]
    exact hfb j hj y hy

open Classical in
/-- Blueprint lines 2540 and 2562-2567 on a leaf cell of the side states (three cores, side role
`l`, no reference: the tuple is discarded). When no reference lies in the full box (`threeRefSet`
empty), every anchored expansion frequency `T_l + (P₂ - l P₁)·ξ` of the transported core inputs has
`r |·| > U₀` (its integer part lies in the full box, `expP_fullBox`), so the cell form with the side
`X` in slot `l` is at most twice the torus-form and gauge errors, plus
`4 r⁻¹ C_{J,A} U₀^{-J} 2^{A+4} W Π_{j ≠ l} ((1 + τ_c) Σ_{F_j} |α|) (r ∫_I |S_phys|²)^{1/2}`,
plus the far tails
`multNorm cutNorm Π_{j ≠ l} (cutNorm Σ_{F_j} |α|) r⁻¹ ∫_I |S_phys| 12 C_J (4/U₀)^{J-2}`
(`three_core_noref_of`). -/
theorem three_core_noref_side {Cj CA CT CK : ℕ} {δs W : ℝ} (hV : D.S.Valid Cj CA CT CK δs W)
    (hCA : 1 ≤ CA) (hd2 : 2 ≤ D.S.dmax) (hD : 2 ≤ D.S.Dstar)
    (hB : 2 ≤ D.S.Bstar) (hQ : 1 ≤ D.S.Q0) {I : ℤ × ℤ}
    (hI : I ∈ A.cells) (G : bf.Grp) (hz : ∀ j, (D.Ms j G).zc = (D.Ms 0 G).zc)
    {δ : ℝ} (hδ : 0 < δ)
    (hdδ : 8 * (D.Ms 0 G).zc.dim * δ ≤ 1) (hδ8 : δ ≤ 1 / 8) (hδc : ∀ j, (D.Ms j G).δc = δ)
    (hcl : ∀ j, (D.Ms j G).cl = slotCoeff j) (hρ : ∀ j k, (D.Ms j G).ρ k ∈ Set.Icc (0 : ℝ) 1)
    (hQC : ∀ a b, ∃ k : ℤ, (D.S.Q0 : ℝ) * ((D.Ms 0 G).zc.C a b : ℝ) = k) {Cm : ℝ}
    (hCm0 : 0 ≤ Cm) (hCm : ∀ a b, |((D.Ms 0 G).zc.C a b : ℝ)| ≤ Cm) {δ'' : ℝ} (hδ'' : 0 < δ'')
    {Kt : ℕ} (hQB : (D.S.Q0 : ℝ) * 2 ^ (Kt + 1) ≤ D.S.Bstar) {J : ℕ} (hJ : 2 ≤ J) (h : ℕ)
    (l : Fin 4)
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
    (hnoref : D.threeRefSet G I xs (h - D.SP.Δ) l a = ∅)
    (X : ColumnL2 (bf.Lab ⊕ Fin fp.Mc))
    (Aw : ℕ) (hAw : 1 ≤ Aw) :
    ‖fp.Λc I (Function.update (fun j => D.compSub j G I
        ((Fsel j).map ⟨Subtype.val, Subtype.val_injective⟩)) l X)‖ ≤ 2 * (
      2 * localKernelSupBound κ' * ((4 * (D.S.Dstar ^ 150)⁻¹ +
          (gaugeErr (D.Ms 0 G).zc.dim δ δ'' +
            4 * (1 + cutTail (D.Ms 0 G).zc.dim δ Kt) ^ 3 * cutTail (D.Ms 0 G).zc.dim δ Kt +
            (1 + cutTail (D.Ms 0 G).zc.dim δ Kt) ^ 4 *
              multTail (D.Ms 0 G).zc.dim δ'' D.S.Q0 Cm Kt)) *
        ∏ j ∈ Finset.univ.erase l,
          D.coefSum G I j (Fsel j)) *
        ((dyadicGridLength A.G I.1)⁻¹ * ∫ y in Set.Icc (dyadicGridLeft A.G I.1 I.2)
          (dyadicGridLeft A.G I.1 I.2 + dyadicGridLength A.G I.1), ‖augPhys X y‖) +
      4 * ((dyadicGridLength A.G I.1)⁻¹ * (entryCU κ' J Aw * (D.U0 ^ J)⁻¹) * 2 ^ (Aw + 4) *
        (((1 + multTail (D.Ms 0 G).zc.dim δ'' D.S.Q0 Cm Kt) *
            (1 + cutTail (D.Ms 0 G).zc.dim δ Kt) * ∏ j ∈ Finset.univ.erase l,
            ((1 + cutTail (D.Ms 0 G).zc.dim δ Kt) *
              D.coefSum G I j (Fsel j))) *
          Real.sqrt (dyadicGridLength A.G I.1 * ∫ y in (dyadicGridLeft A.G I.1 I.2)..
            dyadicGridLeft A.G I.1 I.2 + dyadicGridLength A.G I.1, ‖augPhys X y‖ ^ 2))) +
      (multNorm (D.Ms 0 G).zc.dim δ'' D.S.Q0 Cm * (cutNorm (D.Ms 0 G).zc.dim δ *
          ∏ j ∈ Finset.univ.erase l, (cutNorm (D.Ms 0 G).zc.dim δ *
            D.coefSum G I j (Fsel j)))) *
        ((dyadicGridLength A.G I.1)⁻¹ * (∫ y in Set.Ico (dyadicGridLeft A.G I.1 I.2)
          (dyadicGridLeft A.G I.1 I.2 + dyadicGridLength A.G I.1), ‖augPhys X y‖) *
          (12 * (kerC κ' J * (4 / D.U0) ^ (J - 2))))):= by
  have hr : 0 < dyadicGridLength A.G I.1 := dyadicGridLength_pos A.G I.1
  have hw := A.adm I hI
  have hDp : 0 < D.S.Dstar := by linarith
  have hQ0 : 0 < D.S.Q0 := hQ
  have hE0 : 0 ≤ D.S.Eh (h - D.SP.Δ) := pow_nonneg (by linarith [D.hA]) _
  have hLh : 0 < ModeSchedule.Lh (h - D.SP.Δ) := pow_pos (by norm_num) _
  have hη : (0 : ℝ) ≤ (D.S.Dstar ^ 150)⁻¹ := by positivity
  have hξ : ∀ i, (D.Ms 0 G).torusξ D.S (h - D.SP.Δ) i =
      (D.Ms 0 G).zc.θ i / (D.S.Q0 * (6 ^ (h - D.SP.Δ) : ℕ)) := fun i => by
    unfold ModeSystem.torusξ ModeSchedule.Lh; push_cast; ring
  -- the core roles in the chart of role `0`
  have hrole := fun j (hj : j ≠ l) => (D.Ms j G).role_four_input D.S (D.Ms 0 G).zc (hz j)
    ((hδc j).symm ▸ hδ) hQ0 (h - D.SP.Δ) xs (Fsel j)
    (fun x => D.c j G (A.blkStart D.S.K I.1) (D.preAt I) x.1) (n j) Kt D.SP.Hn
    (D.SP.Tt⁻¹ / dyadicGridLength A.G (A.blkStart D.S.K I.1 - 2 * D.S.K))
    (a₀ := dyadicGridLeft A.G I.1 I.2) (r := dyadicGridLength A.G I.1) hη
    (a j) (hform j hj)
  choose ρ' n' f hρ'e hn'e hfm hfa hfb hind hnorm using hrole
  obtain ⟨ρc, hρc, hρcj⟩ : ∃ ρc : Fin 4 → Fin (D.Ms 0 G).zc.dim → ℝ,
      (∀ j k, ρc j k ∈ Set.Icc (0 : ℝ) 1) ∧ ∀ j (hj : j ≠ l), ρc j = ρ' j hj := by
    refine ⟨fun j => if hj : j = l then fun _ => 0 else ρ' j hj, fun j k => ?_,
      fun j hj => by simp only [hj, ↓reduceDIte]⟩
    by_cases hj : j = l
    · simp only [hj, ↓reduceDIte]; exact ⟨le_rfl, zero_le_one⟩
    · simp only [hj, ↓reduceDIte]
      obtain ⟨k', hk'⟩ := hρ'e j hj k
      rw [hk']; exact hρ j k'
  obtain ⟨nn, hnnj⟩ : ∃ nn : ∀ j, (D.Ms j G).alive (ancAt A.G (D.preAt I)
      (A.blkStart D.S.K I.1 - 4 * D.S.K)) → Fin (D.Ms 0 G).zc.dim → ℤ,
      ∀ j (hj : j ≠ l) x, nn j x = n' j hj x :=
    ⟨fun j => if hj : j = l then fun _ _ => 0 else n' j hj, fun j hj x => by
      simp only [hj, ↓reduceDIte]⟩
  obtain ⟨fv, hfvl, hfvj⟩ : ∃ fv : Fin 4 → ℝ → ℂ, fv l = augPhys X ∧
      ∀ j (hj : j ≠ l), fv j = f j hj :=
    ⟨fun j => if hj : j = l then augPhys X else f j hj, by simp only [↓reduceDIte],
      fun j hj => by simp only [hj, ↓reduceDIte]⟩
  obtain ⟨cα, hcα⟩ : ∃ cα : ∀ j, (D.Ms j G).alive (ancAt A.G (D.preAt I)
      (A.blkStart D.S.K I.1 - 4 * D.S.K)) → ℂ, ∀ j x,
      cα j x = D.c j G (A.blkStart D.S.K I.1) (D.preAt I) x.1 *
        (Real.fourierChar ((D.Ms j G).phase x.1 xs) : ℂ) := ⟨_, fun _ _ => rfl⟩
  have hFj : ∀ j, j ≠ l → sideOptF l Fsel j = (Fsel j).map Function.Embedding.some :=
    fun j hj => by simp [sideOptF, hj]
  -- the side and the integrability of the forms
  have hXm : Measurable (augPhys X) := columnPhys_measurable X
  have hL2X : MemLp (augPhys X) 2 (volume.restrict (Set.Ioc (dyadicGridLeft A.G I.1 I.2)
      (dyadicGridLeft A.G I.1 I.2 + dyadicGridLength A.G I.1))) :=
    (memLp_column_coord X none).restrict _
  have := normalizedIntervalMeasure_probability (dyadicGridLeft A.G I.1 I.2) hr
  have hXfin := (columnPhys_memLp_normalized X (dyadicGridLeft A.G I.1 I.2)
    (dyadicGridLength A.G I.1)).eLpNorm_ne_top
  have hcfin : ∀ j (hj : j ≠ l), eLpNorm (f j hj) 2 (normalizedIntervalMeasure
      (dyadicGridLeft A.G I.1 I.2) (dyadicGridLength A.G I.1)) ≠ ⊤ := fun j hj =>
    (MemLp.of_bound (hfm j hj).aestronglyMeasurable _ (by
      unfold normalizedIntervalMeasure
      exact Measure.ae_smul_measure (ae_restrict_of_forall_mem measurableSet_Icc
        fun y hy => hfb j hj y hy) _)).eLpNorm_ne_top
  have hfi : Integrable (fun zz : ℝ × ℝ => A.w I zz *
      ∏ j, fv j (realProgressionCoordinate j zz)) := by
    refine integrable_localProgression_two hr hw _ (fun j => ?_) fun j => ?_
    · by_cases hj : j = l
      · rw [hj, hfvl]; exact hXm
      · rw [hfvj j hj]; exact hfm j hj
    · by_cases hj : j = l
      · rw [hj, hfvl]; exact hXfin
      · rw [hfvj j hj]; exact hcfin j hj
  have hfiρ : ∀ ρ'' : Fin (D.Ms 0 G).zc.dim → ℝ, Integrable (fun zz : ℝ × ℝ => A.w I zz *
      ∏ j, Function.update fv l (fun y => (centerCut (D.Ms 0 G).zc δ ρ'' y : ℂ) * fv l y) j
        (realProgressionCoordinate j zz)) := by
    intro ρ''
    have hcut : Measurable fun y => (centerCut (D.Ms 0 G).zc δ ρ'' y : ℂ) * augPhys X y :=
      (Complex.measurable_ofReal.comp (centerCut_measurable _ δ ρ'')).mul hXm
    refine integrable_localProgression_two hr hw _ (fun j => ?_) fun j => ?_
    · by_cases hj : j = l
      · rw [hj, Function.update_self, hfvl]; exact hcut
      · rw [Function.update_of_ne hj, hfvj j hj]; exact hfm j hj
    · by_cases hj : j = l
      · rw [hj, Function.update_self, hfvl]
        refine ne_top_of_le_ne_top hXfin (eLpNorm_mono hcut.aestronglyMeasurable fun y => ?_)
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (centerCut_mem _ δ ρ'' y).1]
        exact mul_le_of_le_one_left (norm_nonneg _) (centerCut_mem _ δ ρ'' y).2
      · rw [Function.update_of_ne hj, hfvj j hj]; exact hcfin j hj
  -- the truncations of the core cutoffs
  have hcut := fun j => cutoffP_truncate_all hδ (ρc j) Kt
  choose cc0 hcc0 hccN hccT using hcut
  -- the cosets
  have hnn : ∀ j, ∀ k ∈ sideOptF l Fsel j, ∀ i,
      |(sideOptN nn j k i : ℝ)| ≤ D.S.Dstar * D.S.Eh (h - D.SP.Δ) := by
    intro j k hk i
    by_cases hj : j = l
    · have hk' : k = none := by simpa [sideOptF, hj] using hk
      subst hk'
      simp only [sideOptN, Option.elim, Pi.zero_apply, Int.cast_zero, abs_zero]
      exact mul_nonneg hDp.le hE0
    · rw [hFj j hj, Finset.mem_map] at hk
      obtain ⟨x, hx, rfl⟩ := hk
      simp only [Function.Embedding.some_apply, sideOptN, Option.elim, hnnj j hj]
      obtain ⟨k', hk'⟩ := hn'e j hj x i
      rw [hk']; exact hn j hj x hx k'
  -- no reference: every anchored expansion frequency is far
  have hA6 : 6 ≤ D.S.A0 := D.hA
  have hBA := hV.Bstar_le_A0 hCA hd2 hD hB
  have hγT : ∑ j : Fin 4, ((j : ℕ) : ℝ) * (if j = l then 0 else a j) -
      ((l : ℕ) : ℝ) * ∑ j, (if j = l then 0 else a j) =
      threeT l a := by
    unfold threeT
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.add_sum_erase _ _ (Finset.mem_univ l)]
    simp only [↓reduceIte, mul_zero, sub_zero, zero_add]
    refine Finset.sum_congr rfl fun j hj => ?_
    simp only [Finset.ne_of_mem_erase hj, ↓reduceIte]
    ring
  expose_names
  exact @three_core_noref_side_stage_1 κ' c₀ A bf fp D hD hQ I hI G δ hδ hdδ hδ8 hδc hcl hQC Cm
      hCm0 hCm δ'' hδ'' Kt hQB J hJ h l Fsel a xs hxs hnoref X Aw hAw hr hw hDp hQ0 hη hξ
      ρ' n' f hfa hfb hind ρc hρc hρcj nn hnnj fv hfvl hfvj cα hcα hFj hXm hL2X hfi hfiρ
      cc0 hcc0 hccN hccT hnn hA6 hBA hγT

end SideInput

end ActiveSetup.BasicFamilies.FamParams

/-- The dyadic window weights sum to at most two: `Σ_{i ≤ I} 2^{-i(A+1)} ≤ 2`. -/
theorem sum_range_inv_pow_le (A I : ℕ) :
    ∑ i ∈ Finset.range (I + 1), ((2 : ℝ) ^ i)⁻¹ ^ (A + 1) ≤ 2 := by
  refine le_trans (Finset.sum_le_sum fun i _ => ?_) (sum_geometric_two_le (I + 1))
  have h0 : (0 : ℝ) ≤ ((2 : ℝ) ^ i)⁻¹ := by positivity
  have h1 : ((2 : ℝ) ^ i)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  calc ((2 : ℝ) ^ i)⁻¹ ^ (A + 1) ≤ ((2 : ℝ) ^ i)⁻¹ ^ 1 :=
        pow_le_pow_of_le_one h0 h1 (by omega)
    _ = (1 / 2 : ℝ) ^ i := by rw [pow_one, one_div, inv_pow]

/-- The absolute Fourier costs of a three-core expansion: with full Fourier norms at most `D_*`,
`multNorm (cutNorm Π_{j ∈ s} (cutNorm S_j)) ≤ D_*^{|s| + 2} Π_{j ∈ s} S_j`. -/
theorem norm_prod_le_pow' {ι : Type*} (s : Finset ι) {D MN CN : ℝ} {S : ι → ℝ}
    (hS : ∀ j ∈ s, 0 ≤ S j) (hMN : MN ≤ D) (hCN0 : 0 ≤ CN) (hCN : CN ≤ D) :
    MN * (CN * ∏ j ∈ s, (CN * S j)) ≤ D ^ (s.card + 2) * ∏ j ∈ s, S j := by
  have hP0 : 0 ≤ ∏ j ∈ s, S j := Finset.prod_nonneg hS
  have hD0 : 0 ≤ D := hCN0.trans hCN
  rw [Finset.prod_mul_distrib, Finset.prod_const]
  calc MN * (CN * (CN ^ s.card * ∏ j ∈ s, S j)) ≤ D * (D * (D ^ s.card * ∏ j ∈ s, S j)) := by
        refine mul_le_mul hMN (mul_le_mul hCN (mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ hCN0 hCN _) hP0) (mul_nonneg (pow_nonneg hCN0 _) hP0) hD0)
          (mul_nonneg hCN0 (mul_nonneg (pow_nonneg hCN0 _) hP0)) hD0
    _ = D ^ (s.card + 2) * ∏ j ∈ s, S j := by ring

/-- The window split of a three-core tuple (blueprint `eq:core-numerical`): if the core factor
`W Π (a'_j + τ_c S_j)` is at most `P_a + 31 u P` and every window energy root is at most `R`, the
window sum is at most the principal window sum with the true torus sizes `P_a`, plus
`31 u P R Σ_i c_i`. -/
theorem window_split {I : ℕ} {c ω : ℕ → ℝ} {Wf Pa P u R : ℝ} (hc : ∀ i, 0 ≤ c i)
    (hω0 : ∀ i, 0 ≤ ω i) (hω : ∀ i, ω i ≤ R) (hWf : Wf ≤ Pa + 31 * u * P) (hu : 0 ≤ u)
    (hP : 0 ≤ P) :
    ∑ i ∈ Finset.range (I + 1), (c i * Wf) * ω i ≤
      ∑ i ∈ Finset.range (I + 1), (c i * Pa) * ω i +
        31 * u * P * R * ∑ i ∈ Finset.range (I + 1), c i := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have h1 : (c i * Wf) * ω i ≤ (c i * (Pa + 31 * u * P)) * ω i :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hWf (hc i)) (hω0 i)
  have h2 : 31 * u * P * (c i * ω i) ≤ 31 * u * P * (c i * R) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hω i) (hc i)) (by positivity)
  calc (c i * Wf) * ω i ≤ (c i * (Pa + 31 * u * P)) * ω i := h1
    _ = (c i * Pa) * ω i + 31 * u * P * (c i * ω i) := by ring
    _ ≤ (c i * Pa) * ω i + 31 * u * P * (c i * R) := by linarith
    _ = (c i * Pa) * ω i + 31 * u * P * R * c i := by ring

/-- The coset replacement and tail errors of a three-core tuple (blueprint `eq:core-numerical`):
with full Fourier norms at most `D_*`, replacement precision `ε ≤ D_*^{-999}` (near error
`N ≤ C √ε`), far separation `H ≥ D_*^{999}`, `J ≥ 3`, and normalized `L¹` side size at most `σ`,
`multNorm (cutNorm Π_{j ∈ s} (cutNorm S_j)) L¹ (N + 12 C_J (4/H)^{J-2}) ≤
(C + 48 C_J) D_*^{-100} Π_{j ∈ s} S_j σ` for three roles. -/
theorem three_coset_err_le {ι : Type*} (s : Finset ι) (hs : s.card = 3)
    {D ε H nC kJ MN CN L1 σ NB : ℝ} {J : ℕ} {S : ι → ℝ} (hJ : 3 ≤ J) (hD : 2 ≤ D)
    (hS : ∀ j ∈ s, 0 ≤ S j) (hMN : MN ≤ D) (hCN0 : 0 ≤ CN) (hCN : CN ≤ D) (hnC : 0 ≤ nC)
    (hkJ : 0 ≤ kJ) (hε : ε ≤ (D ^ 999)⁻¹) (hH : D ^ 999 ≤ H) (hL1 : 0 ≤ L1) (hL1σ : L1 ≤ σ)
    (hNB0 : 0 ≤ NB) (hNB : NB ≤ nC * Real.sqrt ε) :
    (MN * (CN * ∏ j ∈ s, (CN * S j))) * (L1 * (NB + 12 * (kJ * (4 / H) ^ (J - 2)))) ≤
      (nC + 48 * kJ) * (D ^ 100)⁻¹ * (∏ j ∈ s, S j) * σ := by
  have hD1 : (1 : ℝ) ≤ D := by linarith
  have h9 : (0 : ℝ) < D ^ 999 := by positivity
  have hP0 : 0 ≤ ∏ j ∈ s, S j := Finset.prod_nonneg hS
  have hMNP := norm_prod_le_pow' s hS hMN hCN0 hCN
  rw [hs] at hMNP
  have hsq : Real.sqrt ε ≤ (D ^ 499)⁻¹ := by
    have e : (D ^ 499)⁻¹ = Real.sqrt (((D ^ 499)⁻¹) ^ 2) := (Real.sqrt_sq (by positivity)).symm
    rw [e]
    refine Real.sqrt_le_sqrt (hε.trans ?_)
    rw [inv_pow, ← pow_mul]
    exact inv_anti₀ (by positivity) (pow_le_pow_right₀ hD1 (by norm_num))
  have hH4 : 4 ≤ H := by
    have : (4 : ℝ) ≤ D ^ 999 :=
      calc (4 : ℝ) = 2 ^ 2 := by norm_num
        _ ≤ D ^ 2 := pow_le_pow_left₀ (by norm_num) hD 2
        _ ≤ D ^ 999 := pow_le_pow_right₀ hD1 (by norm_num)
    linarith
  have hH0 : 0 < H := by linarith
  have hq0 : 0 ≤ 4 / H := by positivity
  have hq1 : 4 / H ≤ 1 := by rw [div_le_one hH0]; exact hH4
  have hq : 4 / H ≤ 4 * (D ^ 999)⁻¹ := by
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left (inv_anti₀ h9 hH) (by norm_num)
  have hpw : (4 / H) ^ (J - 2) ≤ 4 / H := pow_le_of_le_one hq0 hq1 (by omega)
  have hfar : 12 * (kJ * (4 / H) ^ (J - 2)) ≤ 48 * kJ * (D ^ 499)⁻¹ := by
    have h1 := mul_le_mul_of_nonneg_left (hpw.trans hq) hkJ
    have h2 : 48 * kJ * (D ^ 999)⁻¹ ≤ 48 * kJ * (D ^ 499)⁻¹ :=
      mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity)
        (pow_le_pow_right₀ hD1 (by norm_num))) (by positivity)
    linarith only [h1, h2]
  have hfar0 : 0 ≤ 12 * (kJ * (4 / H) ^ (J - 2)) := by positivity
  have hsum : NB + 12 * (kJ * (4 / H) ^ (J - 2)) ≤ (nC + 48 * kJ) * (D ^ 499)⁻¹ := by
    have h1 := mul_le_mul_of_nonneg_left hsq hnC
    linarith only [hNB, hfar, h1]
  have h499 := inv_pow_mul_pow5_le hD1 (k := 499) (by norm_num)
  have hσ0 : 0 ≤ σ := hL1.trans hL1σ
  calc (MN * (CN * ∏ j ∈ s, (CN * S j))) * (L1 * (NB + 12 * (kJ * (4 / H) ^ (J - 2)))) ≤
        (D ^ (3 + 2) * ∏ j ∈ s, S j) * (σ * ((nC + 48 * kJ) * (D ^ 499)⁻¹)) :=
        mul_le_mul hMNP (mul_le_mul hL1σ hsum (add_nonneg hNB0 hfar0) (hL1.trans hL1σ))
          (mul_nonneg hL1 (add_nonneg hNB0 hfar0)) (by positivity)
    _ = (nC + 48 * kJ) * ((D ^ 499)⁻¹ * D ^ 5) * (∏ j ∈ s, S j) * σ := by ring
    _ ≤ (nC + 48 * kJ) * (D ^ 100)⁻¹ * (∏ j ∈ s, S j) * σ := by
        have : 0 ≤ (nC + 48 * kJ) := by positivity
        gcongr

/-- The absolute constant of the numerical errors of a three-core tuple (blueprint
`eq:core-numerical`, with the local side size as an extra factor): torus-form and gauge errors,
truncation parts of the core sizes, coset replacement and tail errors, shells above `U₀`, and
discarded tuples. -/
noncomputable def threeErrC (κ : LocalKernelClass) (J A : ℕ) : ℝ :=
  208 * localKernelSupBound κ + 2 ^ (A + 12) * entryCU κ J A + 2 * nearBC κ + 96 * kerC κ J

namespace ActiveSetup.BasicFamilies.FamParams
variable {κ' : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ' c₀} {bf : A.BasicFamilies}
  {fp : bf.FamParams}

namespace SideInput
variable (D : fp.SideInput)

/-- The principal quantity of a three-core tuple with side role `l` (blueprint `eq:side-windows`):
`2 Σ_{Λ = 2^i ≤ 2^{I_w}} r⁻¹ C_{J,A} μ ν^{-J} 2^{A+4} Λ^{-(A+1)} (Π_{j ≠ l} a'_j) b_Λ` with the true
torus sizes `a'_j` and the offset-averaged window energies `b_Λ` of the side `X` in the
mask-independent windows `threeWin(Λ)`. -/
noncomputable def threePrin (G : bf.Grp) (I : ℤ × ℤ) (xs : ℝ) (h' : ℕ) (l : Fin 4)
    (a : Fin 4 → ℝ)
    (Fsel : ∀ j, Finset ((D.Ms j G).alive (ancAt A.G (D.preAt I)
      (A.blkStart D.S.K I.1 - 4 * D.S.K))))
    (n : ∀ j, (D.Ms j G).alive (ancAt A.G (D.preAt I) (A.blkStart D.S.K I.1 - 4 * D.S.K)) →
      Fin (D.Ms j G).zc.dim → ℤ)
    (X : ColumnL2 (bf.Lab ⊕ Fin fp.Mc)) (J Aw Iw : ℕ) : ℝ :=
  2 * ∑ i ∈ Finset.range (Iw + 1), ((dyadicGridLength A.G I.1)⁻¹ *
      entryC κ' J Aw (D.threeBeta G I xs h' l a) * 2 ^ (Aw + 4) * ((2 : ℝ) ^ i)⁻¹ ^ (Aw + 1) *
      ∏ j ∈ Finset.univ.erase l, D.coreSize G I xs h' j (Fsel j) (n j)) *
    Real.sqrt (∫ ρ', sideWinE (D.Ms 0 G).zc l (augPhys X) (dyadicGridLeft A.G I.1 I.2)
      (dyadicGridLength A.G I.1) (D.threeWin G I xs h' l a (2 ^ i)) ρ'
      ∂offsetMeasure (D.Ms 0 G).zc.dim)

/-- The window energies of a side on a cell are at most `r ∫_I |S_phys|²` (Bessel for each offset,
averaged over the offsets). -/
theorem window_root_le (z : ChartTag) (l : Fin 4) (X : ColumnL2 (bf.Lab ⊕ Fin fp.Mc))
    (I : ℤ × ℤ) (K : Finset ℤ) :
    Real.sqrt (∫ ρ', sideWinE z l (augPhys X) (dyadicGridLeft A.G I.1 I.2)
      (dyadicGridLength A.G I.1) K ρ' ∂offsetMeasure z.dim) ≤
    Real.sqrt (dyadicGridLength A.G I.1 * ∫ y in (dyadicGridLeft A.G I.1 I.2)..
      dyadicGridLeft A.G I.1 I.2 + dyadicGridLength A.G I.1, ‖augPhys X y‖ ^ 2) := by
  have hr := dyadicGridLength_pos A.G I.1
  have hL2X : MemLp (augPhys X) 2 (volume.restrict (Set.Ioc (dyadicGridLeft A.G I.1 I.2)
      (dyadicGridLeft A.G I.1 I.2 + dyadicGridLength A.G I.1))) :=
    (memLp_column_coord X none).restrict _
  have hXm : Measurable (augPhys X) := columnPhys_measurable X
  have hwe := window_energy_integrable z l hXm hr hL2X K
  refine Real.sqrt_le_sqrt ?_
  calc ∫ ρ', sideWinE z l (augPhys X) (dyadicGridLeft A.G I.1 I.2) (dyadicGridLength A.G I.1) K
        ρ' ∂offsetMeasure z.dim ≤ ∫ _ρ', (dyadicGridLength A.G I.1 *
          ∫ y in (dyadicGridLeft A.G I.1 I.2)..dyadicGridLeft A.G I.1 I.2 +
            dyadicGridLength A.G I.1, ‖augPhys X y‖ ^ 2) ∂offsetMeasure z.dim :=
        integral_mono hwe.1 (integrable_const _) fun ρ' => hwe.2 ρ'
    _ = _ := by simp

end SideInput
end ActiveSetup.BasicFamilies.FamParams
end TrilinearHT.Auto
end
