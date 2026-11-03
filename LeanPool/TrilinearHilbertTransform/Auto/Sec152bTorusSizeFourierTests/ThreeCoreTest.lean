/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

/- Adapted for Lean Pool from roos-j/lean-trilinearht at
7b4209609e6a7fb9d9935973ee8541495f943660. Imports, names, proof organization and
Mathlib interfaces have been updated; original authorship is retained above. -/

public import LeanPool.TrilinearHilbertTransform.Auto.Sec152bTorusSizeFourierTests.Setup

/-!
# Trilinear Hilbert transform: three_core_test
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
private def ThreeCoreTestConclusion9Statement : Prop :=
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
    (_ : ∀ (j : Fin (4 : ℕ)), (D.Ms j G).δc = δ)
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
    (n : (j : Fin (4 : ℕ)) → ↥((D.Ms j G).alive (ancAt A.G (D.preAt I) (A.blkStart D.S.K I.1
      - (4 : ℤ) * (↑D.S.K : ℤ)))) → Fin (D.Ms j G).zc.dim → ℤ)
    (a : Fin (4 : ℕ) → ℝ)
    (xs : ℝ)
    (X : ↥(ColumnL2 (bf.Lab ⊕ Fin fp.Mc)))
    (Aw : ℕ)
    (Iw : ℕ)
    (_ : (0 : ℝ) < dyadicGridLength A.G I.1)
    (_ : IsAdmissibleLocalKernel κ' (dyadicGridLeft A.G I.1 I.2) (dyadicGridLength A.G I.1)
      (A.w I))
    (_ : (0 : ℝ) < D.S.Dstar)
    (_ : ∀ (i : Fin (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim), (D.Ms (0 : Fin (4 : ℕ)) G).torusξ D.S
      (h - D.SP.Δ) i = (D.Ms (0 : Fin (4 : ℕ)) G).zc.θ i / ((↑D.S.Q0 : ℝ) * (↑((6 : ℕ) ^
      (h - D.SP.Δ)) : ℝ)))
    (ρ' : (j : Fin (4 : ℕ)) → j ≠ l → Fin (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim → ℝ)
    (n' : (j : Fin (4 : ℕ)) → j ≠ l → ↥((D.Ms j G).alive (ancAt A.G (D.preAt I) (A.blkStart
      D.S.K I.1 - (4 : ℤ) * (↑D.S.K : ℤ)))) → Fin (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim → ℤ)
    (f : (j : Fin (4 : ℕ)) → j ≠ l → ℝ → ℂ)
    (_ : ∀ (j : Fin (4 : ℕ)) (hj : j ≠ l), (Set.Ico (dyadicGridLeft A.G I.1 I.2)
      (dyadicGridLeft A.G I.1 I.2 + dyadicGridLength A.G I.1)).indicator (f j hj) =
      (Set.Ico (dyadicGridLeft A.G I.1 I.2) (dyadicGridLeft A.G I.1 I.2 +
      dyadicGridLength A.G I.1)).indicator fun (y : ℝ) => ∑ x ∈ Fsel j, D.c j G
      (A.blkStart D.S.K I.1) (D.preAt I) (↑x : (D.Ms j G).Md) * (D.Ms j G).wave (↑x :
      (D.Ms j G).Md) y)
    (_ : ∀ (j : Fin (4 : ℕ)) (hj : j ≠ l) (cc0 : (Fin (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim → ℤ)
      → ℂ), (∀ (w : Fin (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim → ℝ), ‖cutoffP (D.Ms j G).δc
      (ρ' j hj) w - ∑ v ∈ frequencyBox (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim ((2 : ℕ) ^ (Kt
      + (1 : ℕ))), cc0 v * (↑((𝐞 : ℝ → Circle) (∑ i : Fin (D.Ms (0 : Fin (4 : ℕ))
      G).zc.dim, (↑(v i) : ℝ) * w i)) : ℂ)‖ ≤ cutTail (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim
      (D.Ms j G).δc Kt) → (eLpNorm (fun (u : ↥(torusAnnihilator
      (rationalIntegerIntersection (tinySpan (fun (i : Fin (D.Ms (0 : Fin (4 : ℕ))
      G).zc.dim) => (D.Ms (0 : Fin (4 : ℕ)) G).zc.θ i / (↑D.S.Q0 : ℝ)) D.SP.Hn
      (D.SP.Tt⁻¹ / dyadicGridLength A.G (A.blkStart D.S.K I.1 - (2 : ℤ) * (↑D.S.K :
      ℤ))))))) => ∑ p ∈ frequencyBox (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim ((2 : ℕ) ^ (Kt +
      (1 : ℕ))) ×ˢ Fsel j, cc0 p.1 * (↑((𝐞 : ℝ → Circle) (∑ i : Fin (D.Ms (0 : Fin (4 :
      ℕ)) G).zc.dim, (↑(p.1 i) : ℝ) * ((D.Ms (0 : Fin (4 : ℕ)) G).zc.θ i * xs))) : ℂ) *
      (D.c j G (A.blkStart D.S.K I.1) (D.preAt I) (↑p.2 : (D.Ms j G).Md) * (↑((𝐞 : ℝ →
      Circle) ((D.Ms j G).phase (↑p.2 : (D.Ms j G).Md) xs)) : ℂ)) * torusCharacter
      ((↑(D.S.Q0 * (6 : ℕ) ^ (h - D.SP.Δ)) : ℤ) • p.1 + n' j hj p.2) (↑u : StandardTorus
      (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim)) (2 : ℝ≥0∞) (torusAnnihilatorHaar
      (rationalIntegerIntersection (tinySpan (fun (i : Fin (D.Ms (0 : Fin (4 : ℕ))
      G).zc.dim) => (D.Ms (0 : Fin (4 : ℕ)) G).zc.θ i / (↑D.S.Q0 : ℝ)) D.SP.Hn
      (D.SP.Tt⁻¹ / dyadicGridLength A.G (A.blkStart D.S.K I.1 - (2 : ℤ) * (↑D.S.K :
      ℤ))))))).toReal ≤ (eLpNorm (fun (u : ↥(torusAnnihilator
      (rationalIntegerIntersection (tinySpan (fun (i : Fin (D.Ms j G).zc.dim) => (D.Ms j
      G).zc.θ i / (↑D.S.Q0 : ℝ)) D.SP.Hn (D.SP.Tt⁻¹ / dyadicGridLength A.G (A.blkStart
      D.S.K I.1 - (2 : ℤ) * (↑D.S.K : ℤ))))))) => (D.Ms j G).torusGT D.S (h - D.SP.Δ) xs
      (Fsel j) (fun (x : ↥((D.Ms j G).alive (ancAt A.G (D.preAt I) (A.blkStart D.S.K I.1
      - (4 : ℤ) * (↑D.S.K : ℤ))))) => D.c j G (A.blkStart D.S.K I.1) (D.preAt I) (↑x :
      (D.Ms j G).Md)) (n j) (↑u : StandardTorus (D.Ms j G).zc.dim)) (2 : ℝ≥0∞)
      (torusAnnihilatorHaar (rationalIntegerIntersection (tinySpan (fun (i : Fin (D.Ms j
      G).zc.dim) => (D.Ms j G).zc.θ i / (↑D.S.Q0 : ℝ)) D.SP.Hn (D.SP.Tt⁻¹ /
      dyadicGridLength A.G (A.blkStart D.S.K I.1 - (2 : ℤ) * (↑D.S.K : ℤ))))))).toReal +
      cutTail (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim (D.Ms j G).δc Kt * ∑ x ∈ Fsel j, ‖D.c j
      G (A.blkStart D.S.K I.1) (D.preAt I) (↑x : (D.Ms j G).Md)‖)
    (ρc : Fin (4 : ℕ) → Fin (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim → ℝ)
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
    (cc0 : Fin (4 : ℕ) → (Fin (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim → ℤ) → ℂ)
    (_ : ∀ (j : Fin (4 : ℕ)) (w : Fin (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim → ℝ), ‖cutoffP δ (ρc
      j) w - ∑ v ∈ frequencyBox (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim ((2 : ℕ) ^ (Kt + (1 :
      ℕ))), cc0 j v * (↑((𝐞 : ℝ → Circle) (∑ i : Fin (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim,
      (↑(v i) : ℝ) * w i)) : ℂ)‖ ≤ cutTail (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim δ Kt)
    (N : Finset (Fin (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim → ℤ))
    (_ : ∀ n ∈ N, ∀ (i : Fin (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim), |(↑(n i) : ℝ)| ≤ (16 : ℝ) *
      (D.S.Dstar ^ (5 : ℕ) * D.S.Eh (h - D.SP.Δ)))
    (_ : ‖localProgressionForm (dyadicGridLength A.G I.1) (A.w I) fv‖ ≤ (2 : ℝ) * ((2 : ℝ) *
      localKernelSupBound κ' * (((4 : ℝ) * (D.S.Dstar ^ (150 : ℕ))⁻¹ + (gaugeErr (D.Ms
      (0 : Fin (4 : ℕ)) G).zc.dim δ δ'' + (4 : ℝ) * ((1 : ℝ) + cutTail (D.Ms (0 : Fin (4
      : ℕ)) G).zc.dim δ Kt) ^ (3 : ℕ) * cutTail (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim δ Kt +
      ((1 : ℝ) + cutTail (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim δ Kt) ^ (4 : ℕ) * multTail
      (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim δ'' D.S.Q0 Cm Kt)) * ∏ j : Fin (4 : ℕ), ∑ k ∈
      sideOptF l Fsel j, ‖sideOptC cα j k‖) * ((dyadicGridLength A.G I.1)⁻¹ * ∫ (y : ℝ)
      in Set.Icc (dyadicGridLeft A.G I.1 I.2) (dyadicGridLeft A.G I.1 I.2 +
      dyadicGridLength A.G I.1), ‖fv l y‖) + (dyadicGridLength A.G I.1)⁻¹ * entryC κ' J
      Aw (dyadicGridLength A.G I.1 * (D.threeBeta G I xs (h - D.SP.Δ) l a /
      dyadicGridLength A.G I.1)) * (2 : ℝ) ^ (Aw + (4 : ℕ)) * ((2 : ℝ) * ((2 : ℝ) ^ (Iw
      + (1 : ℕ)))⁻¹ ^ (Aw + (1 : ℕ))) * ((((1 : ℝ) + multTail (D.Ms (0 : Fin (4 : ℕ))
      G).zc.dim δ'' D.S.Q0 Cm Kt) * ((1 : ℝ) + cutTail (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim
      δ Kt) * ∏ i ∈ Finset.univ.erase l, (eLpNorm (fun (u : ↥(torusAnnihilator
      (rationalIntegerIntersection (tinySpan (fun (i : Fin (D.Ms (0 : Fin (4 : ℕ))
      G).zc.dim) => (D.Ms (0 : Fin (4 : ℕ)) G).zc.θ i / (↑D.S.Q0 : ℝ)) D.SP.Hn
      (D.SP.Tt⁻¹ / dyadicGridLength A.G (A.blkStart D.S.K I.1 - (2 : ℤ) * (↑D.S.K :
      ℤ))))))) => coreG (D.S.Q0 * (6 : ℕ) ^ (h - D.SP.Δ)) ((2 : ℕ) ^ (Kt + (1 : ℕ)))
      (sideOptF l Fsel) (sideOptC cα) (sideOptN nn) (fun (j : Fin (4 : ℕ)) (v : Fin
      (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim → ℤ) => cc0 j v * (↑((𝐞 : ℝ → Circle) (∑ i : Fin
      (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim, (↑(v i) : ℝ) * ((D.Ms (0 : Fin (4 : ℕ)) G).zc.θ
      i * xs))) : ℂ)) i (↑u : StandardTorus (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim)) (2 :
      ℝ≥0∞) (torusAnnihilatorHaar (rationalIntegerIntersection (tinySpan (fun (i : Fin
      (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim) => (D.Ms (0 : Fin (4 : ℕ)) G).zc.θ i / (↑D.S.Q0
      : ℝ)) D.SP.Hn (D.SP.Tt⁻¹ / dyadicGridLength A.G (A.blkStart D.S.K I.1 - (2 : ℤ) *
      (↑D.S.K : ℤ))))))).toReal) * √(dyadicGridLength A.G I.1 * ∫ (y : ℝ) in
      dyadicGridLeft A.G I.1 I.2..dyadicGridLeft A.G I.1 I.2 + dyadicGridLength A.G I.1,
      ‖fv l y‖ ^ (2 : ℕ))) + (multNorm (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim δ'' D.S.Q0 Cm *
      ∏ j : Fin (4 : ℕ), cutNorm (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim δ * ∑ k ∈ sideOptF l
      Fsel j, ‖sideOptC cα j k‖) * (((dyadicGridLength A.G I.1)⁻¹ * ∫ (y : ℝ) in Set.Ico
      (dyadicGridLeft A.G I.1 I.2) (dyadicGridLeft A.G I.1 I.2 + dyadicGridLength A.G
      I.1), ‖fv l y‖) * (nearB κ' (D.SP.Tt⁻¹ / ModeSchedule.Lh (h - D.SP.Δ)) + (12 : ℝ)
      * (kerC κ' J * ((4 : ℝ) / (D.SP.Tt / ModeSchedule.Lh (h - D.SP.Δ) - D.U0)) ^ (J -
      (2 : ℕ))))) + ∑ i ∈ Finset.range (Iw + (1 : ℕ)), (dyadicGridLength A.G I.1)⁻¹ *
      entryC κ' J Aw (dyadicGridLength A.G I.1 * (D.threeBeta G I xs (h - D.SP.Δ) l a /
      dyadicGridLength A.G I.1)) * (2 : ℝ) ^ (Aw + (4 : ℕ)) * ((2 : ℝ) ^ i)⁻¹ ^ (Aw + (1
      : ℕ)) * (((1 : ℝ) + multTail (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim δ'' D.S.Q0 Cm Kt) *
      ((1 : ℝ) + cutTail (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim δ Kt) * ∏ i ∈
      Finset.univ.erase l, (eLpNorm (fun (u : ↥(torusAnnihilator
      (rationalIntegerIntersection (tinySpan (fun (i : Fin (D.Ms (0 : Fin (4 : ℕ))
      G).zc.dim) => (D.Ms (0 : Fin (4 : ℕ)) G).zc.θ i / (↑D.S.Q0 : ℝ)) D.SP.Hn
      (D.SP.Tt⁻¹ / dyadicGridLength A.G (A.blkStart D.S.K I.1 - (2 : ℤ) * (↑D.S.K :
      ℤ))))))) => coreG (D.S.Q0 * (6 : ℕ) ^ (h - D.SP.Δ)) ((2 : ℕ) ^ (Kt + (1 : ℕ)))
      (sideOptF l Fsel) (sideOptC cα) (sideOptN nn) (fun (j : Fin (4 : ℕ)) (v : Fin
      (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim → ℤ) => cc0 j v * (↑((𝐞 : ℝ → Circle) (∑ i : Fin
      (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim, (↑(v i) : ℝ) * ((D.Ms (0 : Fin (4 : ℕ)) G).zc.θ
      i * xs))) : ℂ)) i (↑u : StandardTorus (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim)) (2 :
      ℝ≥0∞) (torusAnnihilatorHaar (rationalIntegerIntersection (tinySpan (fun (i : Fin
      (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim) => (D.Ms (0 : Fin (4 : ℕ)) G).zc.θ i / (↑D.S.Q0
      : ℝ)) D.SP.Hn (D.SP.Tt⁻¹ / dyadicGridLength A.G (A.blkStart D.S.K I.1 - (2 : ℤ) *
      (↑D.S.K : ℤ))))))).toReal) * √(∫ (ρ' : Fin (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim → ℝ),
      sideWinE (D.Ms (0 : Fin (4 : ℕ)) G).zc l (fv l) (dyadicGridLeft A.G I.1 I.2)
      (dyadicGridLength A.G I.1) ({k ∈ windowSet N (fun (n : Fin (D.Ms (0 : Fin (4 : ℕ))
      G).zc.dim → ℤ) => dyadicGridLength A.G I.1 * ((∑ j : Fin (4 : ℕ), if j = l then (0
      : ℝ) else a j) + ∑ i : Fin (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim, (↑(n i) : ℝ) *
      ((D.Ms (0 : Fin (4 : ℕ)) G).zc.θ i / ((↑D.S.Q0 : ℝ) * (↑((6 : ℕ) ^ (h - D.SP.Δ)) :
      ℝ))))) Iw | ∃ n ∈ N, |(↑k : ℝ) + -(dyadicGridLength A.G I.1 * ((∑ j : Fin (4 : ℕ),
      if j = l then (0 : ℝ) else a j) + ∑ i : Fin (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim,
      (↑(n i) : ℝ) * ((D.Ms (0 : Fin (4 : ℕ)) G).zc.θ i / ((↑D.S.Q0 : ℝ) * (↑((6 : ℕ) ^
      (h - D.SP.Δ)) : ℝ)))))| ≤ (2 : ℝ) ^ i}) ρ' ∂offsetMeasure (D.Ms (0 : Fin (4 : ℕ))
      G).zc.dim))),
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
                        (4 : ℝ) * ((1 : ℝ) + cutTail (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim δ Kt) ^
                          (3 : ℕ) *
                          cutTail (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim δ Kt +
                      ((1 : ℝ) + cutTail (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim δ Kt) ^ (4 : ℕ) *
                        multTail (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim δ'' D.S.Q0 Cm Kt)) *
                  ∏ j ∈ Finset.univ.erase l,
                    ∑ x ∈ Fsel j, ‖D.c j G (A.blkStart D.S.K I.1) (D.preAt I) (↑x : (D.Ms j
                      G).Md)‖) *
              ((dyadicGridLength A.G I.1)⁻¹ *
                ∫ (y : ℝ) in Set.Icc (dyadicGridLeft A.G I.1 I.2) (dyadicGridLeft A.G I.1 I.2 +
                  dyadicGridLength A.G I.1),
                  ‖augPhys X y‖) +
            (dyadicGridLength A.G I.1)⁻¹ * entryC κ' J Aw (D.threeBeta G I xs (h - D.SP.Δ) l a) *
                  (2 : ℝ) ^ (Aw + (4 : ℕ)) *
                ((2 : ℝ) * ((2 : ℝ) ^ (Iw + (1 : ℕ)))⁻¹ ^ (Aw + (1 : ℕ))) *
              ((((1 : ℝ) + multTail (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim δ'' D.S.Q0 Cm Kt) *
                    ((1 : ℝ) + cutTail (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim δ Kt) *
                  ∏ j ∈ Finset.univ.erase l,
                    ((eLpNorm
                          (fun
                              (u :
                                ↥(torusAnnihilator
                                    (rationalIntegerIntersection
                                      (tinySpan (fun (i : Fin (D.Ms j G).zc.dim) => (D.Ms j
                                        G).zc.θ i / (↑D.S.Q0 : ℝ))
                                        D.SP.Hn
                                        (D.SP.Tt⁻¹ /
                                          dyadicGridLength A.G (A.blkStart D.S.K I.1 - (2 : ℤ) *
                                            (↑D.S.K : ℤ))))))) =>
                            (D.Ms j G).torusGT D.S (h - D.SP.Δ) xs (Fsel j)
                              (fun
                                  (x :
                                    ↥((D.Ms j G).alive
                                        (ancAt A.G (D.preAt I) (A.blkStart D.S.K I.1 - (4 : ℤ) *
                                          (↑D.S.K : ℤ))))) =>
                                D.c j G (A.blkStart D.S.K I.1) (D.preAt I) (↑x : (D.Ms j G).Md))
                              (n j) (↑u : StandardTorus (D.Ms j G).zc.dim))
                          (2 : ℝ≥0∞)
                          (torusAnnihilatorHaar
                            (rationalIntegerIntersection
                              (tinySpan (fun (i : Fin (D.Ms j G).zc.dim) => (D.Ms j G).zc.θ i /
                                (↑D.S.Q0 : ℝ)) D.SP.Hn
                                (D.SP.Tt⁻¹ /
                                  dyadicGridLength A.G (A.blkStart D.S.K I.1 - (2 : ℤ) * (↑D.S.K
                                    : ℤ))))))).toReal +
                      cutTail (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim δ Kt *
                        ∑ x ∈ Fsel j, ‖D.c j G (A.blkStart D.S.K I.1) (D.preAt I) (↑x : (D.Ms j
                          G).Md)‖)) *
                √(dyadicGridLength A.G I.1 *
                    ∫ (y : ℝ) in dyadicGridLeft A.G I.1 I.2..dyadicGridLeft A.G I.1 I.2 +
                      dyadicGridLength A.G I.1,
                      ‖augPhys X y‖ ^ (2 : ℕ))) +
          multNorm (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim δ'' D.S.Q0 Cm *
              (cutNorm (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim δ *
                ∏ j ∈ Finset.univ.erase l,
                  cutNorm (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim δ *
                    ∑ x ∈ Fsel j, ‖D.c j G (A.blkStart D.S.K I.1) (D.preAt I) (↑x : (D.Ms j
                      G).Md)‖) *
            (((dyadicGridLength A.G I.1)⁻¹ *
                ∫ (y : ℝ) in Set.Ico (dyadicGridLeft A.G I.1 I.2) (dyadicGridLeft A.G I.1 I.2 +
                  dyadicGridLength A.G I.1),
                  ‖augPhys X y‖) *
              (nearB κ' (D.SP.Tt⁻¹ / ModeSchedule.Lh (h - D.SP.Δ)) +
                (12 : ℝ) * (kerC κ' J * ((4 : ℝ) / (D.SP.Tt / ModeSchedule.Lh (h - D.SP.Δ) -
                  D.U0)) ^ (J - (2 : ℕ))))) +
        ∑ i ∈ Finset.range (Iw + (1 : ℕ)),
          (dyadicGridLength A.G I.1)⁻¹ * entryC κ' J Aw (D.threeBeta G I xs (h - D.SP.Δ) l a) *
            (2 : ℝ) ^ (Aw + (4 : ℕ)) *
                ((2 : ℝ) ^ i)⁻¹ ^ (Aw + (1 : ℕ)) *
              (((1 : ℝ) + multTail (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim δ'' D.S.Q0 Cm Kt) *
                  ((1 : ℝ) + cutTail (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim δ Kt) *
                ∏ j ∈ Finset.univ.erase l,
                  ((eLpNorm
                        (fun
                            (u :
                              ↥(torusAnnihilator
                                  (rationalIntegerIntersection
                                    (tinySpan (fun (i : Fin (D.Ms j G).zc.dim) => (D.Ms j
                                      G).zc.θ i / (↑D.S.Q0 : ℝ))
                                      D.SP.Hn
                                      (D.SP.Tt⁻¹ /
                                        dyadicGridLength A.G (A.blkStart D.S.K I.1 - (2 : ℤ) *
                                          (↑D.S.K : ℤ))))))) =>
                          (D.Ms j G).torusGT D.S (h - D.SP.Δ) xs (Fsel j)
                            (fun
                                (x :
                                  ↥((D.Ms j G).alive
                                      (ancAt A.G (D.preAt I) (A.blkStart D.S.K I.1 - (4 : ℤ) *
                                        (↑D.S.K : ℤ))))) =>
                              D.c j G (A.blkStart D.S.K I.1) (D.preAt I) (↑x : (D.Ms j G).Md))
                            (n j) (↑u : StandardTorus (D.Ms j G).zc.dim))
                        (2 : ℝ≥0∞)
                        (torusAnnihilatorHaar
                          (rationalIntegerIntersection
                            (tinySpan (fun (i : Fin (D.Ms j G).zc.dim) => (D.Ms j G).zc.θ i /
                              (↑D.S.Q0 : ℝ)) D.SP.Hn
                              (D.SP.Tt⁻¹ /
                                dyadicGridLength A.G (A.blkStart D.S.K I.1 - (2 : ℤ) * (↑D.S.K :
                                  ℤ))))))).toReal +
                    cutTail (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim δ Kt *
                      ∑ x ∈ Fsel j, ‖D.c j G (A.blkStart D.S.K I.1) (D.preAt I) (↑x : (D.Ms j
                        G).Md)‖)) *
            √(∫ (ρ' : Fin (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim → ℝ),
                sideWinE (D.Ms (0 : Fin (4 : ℕ)) G).zc l (augPhys X) (dyadicGridLeft A.G I.1 I.2)
                  (dyadicGridLength A.G I.1) (D.threeWin G I xs (h - D.SP.Δ) l a ((2 : ℝ) ^ i))
                  ρ' ∂offsetMeasure (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim))


open scoped Classical in
private def ThreeCoreTestStage1Statement : Prop :=
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
    (J : ℕ)
    (_ : (2 : ℕ) ≤ J)
    (h : ℕ)
    (l : Fin (4 : ℕ))
    (Fsel : (j : Fin (4 : ℕ)) → Finset ↥((D.Ms j G).alive (ancAt A.G (D.preAt I) (A.blkStart
      D.S.K I.1 - (4 : ℤ) * (↑D.S.K : ℤ)))))
    (n : (j : Fin (4 : ℕ)) → ↥((D.Ms j G).alive (ancAt A.G (D.preAt I) (A.blkStart D.S.K I.1
      - (4 : ℤ) * (↑D.S.K : ℤ)))) → Fin (D.Ms j G).zc.dim → ℤ)
    (a : Fin (4 : ℕ) → ℝ)
    (xs : ℝ)
    (_ : xs ∈ dyadicGridCell A.G I.1 I.2)
    (X : ↥(ColumnL2 (bf.Lab ⊕ Fin fp.Mc)))
    (Aw : ℕ)
    (Iw : ℕ)
    (_ : (1 : ℕ) ≤ Aw)
    (_ : (0 : ℝ) < dyadicGridLength A.G I.1)
    (_ : IsAdmissibleLocalKernel κ' (dyadicGridLeft A.G I.1 I.2) (dyadicGridLength A.G I.1)
      (A.w I))
    (_ : (0 : ℝ) < D.S.Dstar)
    (_ : (0 : ℕ) < D.S.Q0)
    (_ : (0 : ℝ) < ModeSchedule.Lh (h - D.SP.Δ))
    (_ : (0 : ℝ) < D.SP.Tt)
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
    (_ : ∀ (j : Fin (4 : ℕ)) (hj : j ≠ l) (cc0 : (Fin (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim → ℤ)
      → ℂ), (∀ (w : Fin (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim → ℝ), ‖cutoffP (D.Ms j G).δc
      (ρ' j hj) w - ∑ v ∈ frequencyBox (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim ((2 : ℕ) ^ (Kt
      + (1 : ℕ))), cc0 v * (↑((𝐞 : ℝ → Circle) (∑ i : Fin (D.Ms (0 : Fin (4 : ℕ))
      G).zc.dim, (↑(v i) : ℝ) * w i)) : ℂ)‖ ≤ cutTail (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim
      (D.Ms j G).δc Kt) → (eLpNorm (fun (u : ↥(torusAnnihilator
      (rationalIntegerIntersection (tinySpan (fun (i : Fin (D.Ms (0 : Fin (4 : ℕ))
      G).zc.dim) => (D.Ms (0 : Fin (4 : ℕ)) G).zc.θ i / (↑D.S.Q0 : ℝ)) D.SP.Hn
      (D.SP.Tt⁻¹ / dyadicGridLength A.G (A.blkStart D.S.K I.1 - (2 : ℤ) * (↑D.S.K :
      ℤ))))))) => ∑ p ∈ frequencyBox (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim ((2 : ℕ) ^ (Kt +
      (1 : ℕ))) ×ˢ Fsel j, cc0 p.1 * (↑((𝐞 : ℝ → Circle) (∑ i : Fin (D.Ms (0 : Fin (4 :
      ℕ)) G).zc.dim, (↑(p.1 i) : ℝ) * ((D.Ms (0 : Fin (4 : ℕ)) G).zc.θ i * xs))) : ℂ) *
      (D.c j G (A.blkStart D.S.K I.1) (D.preAt I) (↑p.2 : (D.Ms j G).Md) * (↑((𝐞 : ℝ →
      Circle) ((D.Ms j G).phase (↑p.2 : (D.Ms j G).Md) xs)) : ℂ)) * torusCharacter
      ((↑(D.S.Q0 * (6 : ℕ) ^ (h - D.SP.Δ)) : ℤ) • p.1 + n' j hj p.2) (↑u : StandardTorus
      (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim)) (2 : ℝ≥0∞) (torusAnnihilatorHaar
      (rationalIntegerIntersection (tinySpan (fun (i : Fin (D.Ms (0 : Fin (4 : ℕ))
      G).zc.dim) => (D.Ms (0 : Fin (4 : ℕ)) G).zc.θ i / (↑D.S.Q0 : ℝ)) D.SP.Hn
      (D.SP.Tt⁻¹ / dyadicGridLength A.G (A.blkStart D.S.K I.1 - (2 : ℤ) * (↑D.S.K :
      ℤ))))))).toReal ≤ (eLpNorm (fun (u : ↥(torusAnnihilator
      (rationalIntegerIntersection (tinySpan (fun (i : Fin (D.Ms j G).zc.dim) => (D.Ms j
      G).zc.θ i / (↑D.S.Q0 : ℝ)) D.SP.Hn (D.SP.Tt⁻¹ / dyadicGridLength A.G (A.blkStart
      D.S.K I.1 - (2 : ℤ) * (↑D.S.K : ℤ))))))) => (D.Ms j G).torusGT D.S (h - D.SP.Δ) xs
      (Fsel j) (fun (x : ↥((D.Ms j G).alive (ancAt A.G (D.preAt I) (A.blkStart D.S.K I.1
      - (4 : ℤ) * (↑D.S.K : ℤ))))) => D.c j G (A.blkStart D.S.K I.1) (D.preAt I) (↑x :
      (D.Ms j G).Md)) (n j) (↑u : StandardTorus (D.Ms j G).zc.dim)) (2 : ℝ≥0∞)
      (torusAnnihilatorHaar (rationalIntegerIntersection (tinySpan (fun (i : Fin (D.Ms j
      G).zc.dim) => (D.Ms j G).zc.θ i / (↑D.S.Q0 : ℝ)) D.SP.Hn (D.SP.Tt⁻¹ /
      dyadicGridLength A.G (A.blkStart D.S.K I.1 - (2 : ℤ) * (↑D.S.K : ℤ))))))).toReal +
      cutTail (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim (D.Ms j G).δc Kt * ∑ x ∈ Fsel j, ‖D.c j
      G (A.blkStart D.S.K I.1) (D.preAt I) (↑x : (D.Ms j G).Md)‖)
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
    (N : Finset (Fin (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim → ℤ))
    (nref : (Fin ((D.Ms (0 : Fin (4 : ℕ)) G).zc.dim + (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim) → ℤ) ×
      ((j : Fin (4 : ℕ)) → (Fin (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim → ℤ) × Option ↥((D.Ms
      j G).alive (ancAt A.G (D.preAt I) (A.blkStart D.S.K I.1 - (4 : ℤ) * (↑D.S.K :
      ℤ))))) → Fin (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim → ℤ)
    (_ : ∀ n ∈ N, ∀ (i : Fin (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim), |(↑(n i) : ℝ)| ≤ (16 : ℝ) *
      (D.S.Dstar ^ (5 : ℕ) * D.S.Eh (h - D.SP.Δ)))
    (_ : ∀ n ∈ N, ∀ n' ∈ N, n ≠ n' → n - n' ∉ rationalIntegerIntersection (tinySpan (fun (i :
      Fin (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim) => (D.Ms (0 : Fin (4 : ℕ)) G).zc.θ i /
      (↑D.S.Q0 : ℝ)) D.SP.Hn (D.SP.Tt⁻¹ / dyadicGridLength A.G (A.blkStart D.S.K I.1 -
      (2 : ℤ) * (↑D.S.K : ℤ)))))
    (_ : ∀ n ∈ N, ∀ n' ∈ N, n ≠ n' → (1 : ℝ) ≤ |-(dyadicGridLength A.G I.1 * ((∑ j : Fin (4 :
      ℕ), if j = l then (0 : ℝ) else a j) + ∑ i : Fin (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim,
      (↑(n i) : ℝ) * ((D.Ms (0 : Fin (4 : ℕ)) G).zc.θ i / ((↑D.S.Q0 : ℝ) * (↑((6 : ℕ) ^
      (h - D.SP.Δ)) : ℝ))))) - -(dyadicGridLength A.G I.1 * ((∑ j : Fin (4 : ℕ), if j =
      l then (0 : ℝ) else a j) + ∑ i : Fin (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim, (↑(n' i) :
      ℝ) * ((D.Ms (0 : Fin (4 : ℕ)) G).zc.θ i / ((↑D.S.Q0 : ℝ) * (↑((6 : ℕ) ^ (h -
      D.SP.Δ)) : ℝ)))))|)
    (_ : ∀ x ∈ frequencyBox ((D.Ms (0 : Fin (4 : ℕ)) G).zc.dim + (D.Ms (0 : Fin (4 : ℕ))
      G).zc.dim) ((2 : ℕ) ^ (Kt + (1 : ℕ))) ×ˢ Fintype.piFinset fun (j : Fin (4 : ℕ)) =>
      frequencyBox (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim ((2 : ℕ) ^ (Kt + (1 : ℕ))) ×ˢ
      sideOptF l Fsel j, expP2 ((6 : ℕ) ^ (h - D.SP.Δ)) (D.S.Q0 * (6 : ℕ) ^ (h -
      D.SP.Δ)) (sideOptN nn) x - (↑(↑l : ℕ) : ℤ) • expP1 ((6 : ℕ) ^ (h - D.SP.Δ))
      (D.S.Q0 * (6 : ℕ) ^ (h - D.SP.Δ)) (sideOptN nn) x - D.threeRef G I xs (h - D.SP.Δ)
      l a ∈ rationalIntegerIntersection (tinySpan (fun (i : Fin (D.Ms (0 : Fin (4 : ℕ))
      G).zc.dim) => (D.Ms (0 : Fin (4 : ℕ)) G).zc.θ i / (↑D.S.Q0 : ℝ)) D.SP.Hn
      (D.SP.Tt⁻¹ / dyadicGridLength A.G (A.blkStart D.S.K I.1 - (2 : ℤ) * (↑D.S.K :
      ℤ)))) → nref x ∈ N ∧ expP1 ((6 : ℕ) ^ (h - D.SP.Δ)) (D.S.Q0 * (6 : ℕ) ^ (h -
      D.SP.Δ)) (sideOptN nn) x - nref x ∈ rationalIntegerIntersection (tinySpan (fun (i
      : Fin (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim) => (D.Ms (0 : Fin (4 : ℕ)) G).zc.θ i /
      (↑D.S.Q0 : ℝ)) D.SP.Hn (D.SP.Tt⁻¹ / dyadicGridLength A.G (A.blkStart D.S.K I.1 -
      (2 : ℤ) * (↑D.S.K : ℤ)))) ∧ |dyadicGridLength A.G I.1 * ((∑ j : Fin (4 : ℕ), if j
      = l then (0 : ℝ) else a j) + ∑ i : Fin (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim, (↑(expP1
      ((6 : ℕ) ^ (h - D.SP.Δ)) (D.S.Q0 * (6 : ℕ) ^ (h - D.SP.Δ)) (sideOptN nn) x i) : ℝ)
      * ((D.Ms (0 : Fin (4 : ℕ)) G).zc.θ i / ((↑D.S.Q0 : ℝ) * (↑((6 : ℕ) ^ (h - D.SP.Δ))
      : ℝ)))) - dyadicGridLength A.G I.1 * ((∑ j : Fin (4 : ℕ), if j = l then (0 : ℝ)
      else a j) + ∑ i : Fin (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim, (↑(nref x i) : ℝ) *
      ((D.Ms (0 : Fin (4 : ℕ)) G).zc.θ i / ((↑D.S.Q0 : ℝ) * (↑((6 : ℕ) ^ (h - D.SP.Δ)) :
      ℝ))))| ≤ D.SP.Tt⁻¹ / ModeSchedule.Lh (h - D.SP.Δ) ∧ |dyadicGridLength A.G I.1 *
      ((∑ j : Fin (4 : ℕ), (↑(↑j : ℕ) : ℝ) * if j = l then (0 : ℝ) else a j) + ∑ i : Fin
      (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim, (↑(expP2 ((6 : ℕ) ^ (h - D.SP.Δ)) (D.S.Q0 * (6
      : ℕ) ^ (h - D.SP.Δ)) (sideOptN nn) x i) : ℝ) * ((D.Ms (0 : Fin (4 : ℕ)) G).zc.θ i
      / ((↑D.S.Q0 : ℝ) * (↑((6 : ℕ) ^ (h - D.SP.Δ)) : ℝ))) - (↑(↑l : ℕ) : ℝ) * ((∑ j :
      Fin (4 : ℕ), if j = l then (0 : ℝ) else a j) + ∑ i : Fin (D.Ms (0 : Fin (4 : ℕ))
      G).zc.dim, (↑(expP1 ((6 : ℕ) ^ (h - D.SP.Δ)) (D.S.Q0 * (6 : ℕ) ^ (h - D.SP.Δ))
      (sideOptN nn) x i) : ℝ) * ((D.Ms (0 : Fin (4 : ℕ)) G).zc.θ i / ((↑D.S.Q0 : ℝ) *
      (↑((6 : ℕ) ^ (h - D.SP.Δ)) : ℝ))))) - D.threeBeta G I xs (h - D.SP.Δ) l a| ≤
      D.SP.Tt⁻¹ / ModeSchedule.Lh (h - D.SP.Δ))
    (_ : ∀ x ∈ frequencyBox ((D.Ms (0 : Fin (4 : ℕ)) G).zc.dim + (D.Ms (0 : Fin (4 : ℕ))
      G).zc.dim) ((2 : ℕ) ^ (Kt + (1 : ℕ))) ×ˢ Fintype.piFinset fun (j : Fin (4 : ℕ)) =>
      frequencyBox (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim ((2 : ℕ) ^ (Kt + (1 : ℕ))) ×ˢ
      sideOptF l Fsel j, expP2 ((6 : ℕ) ^ (h - D.SP.Δ)) (D.S.Q0 * (6 : ℕ) ^ (h -
      D.SP.Δ)) (sideOptN nn) x - (↑(↑l : ℕ) : ℤ) • expP1 ((6 : ℕ) ^ (h - D.SP.Δ))
      (D.S.Q0 * (6 : ℕ) ^ (h - D.SP.Δ)) (sideOptN nn) x - D.threeRef G I xs (h - D.SP.Δ)
      l a ∉ rationalIntegerIntersection (tinySpan (fun (i : Fin (D.Ms (0 : Fin (4 : ℕ))
      G).zc.dim) => (D.Ms (0 : Fin (4 : ℕ)) G).zc.θ i / (↑D.S.Q0 : ℝ)) D.SP.Hn
      (D.SP.Tt⁻¹ / dyadicGridLength A.G (A.blkStart D.S.K I.1 - (2 : ℤ) * (↑D.S.K :
      ℤ)))) → D.SP.Tt / ModeSchedule.Lh (h - D.SP.Δ) - D.U0 ≤ |dyadicGridLength A.G I.1
      * ((∑ j : Fin (4 : ℕ), (↑(↑j : ℕ) : ℝ) * if j = l then (0 : ℝ) else a j) + ∑ i :
      Fin (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim, (↑(expP2 ((6 : ℕ) ^ (h - D.SP.Δ)) (D.S.Q0 *
      (6 : ℕ) ^ (h - D.SP.Δ)) (sideOptN nn) x i) : ℝ) * ((D.Ms (0 : Fin (4 : ℕ)) G).zc.θ
      i / ((↑D.S.Q0 : ℝ) * (↑((6 : ℕ) ^ (h - D.SP.Δ)) : ℝ))) - (↑(↑l : ℕ) : ℝ) * ((∑ j :
      Fin (4 : ℕ), if j = l then (0 : ℝ) else a j) + ∑ i : Fin (D.Ms (0 : Fin (4 : ℕ))
      G).zc.dim, (↑(expP1 ((6 : ℕ) ^ (h - D.SP.Δ)) (D.S.Q0 * (6 : ℕ) ^ (h - D.SP.Δ))
      (sideOptN nn) x i) : ℝ) * ((D.Ms (0 : Fin (4 : ℕ)) G).zc.θ i / ((↑D.S.Q0 : ℝ) *
      (↑((6 : ℕ) ^ (h - D.SP.Δ)) : ℝ)))))|)
    (_ : (4 : ℝ) ≤ D.SP.Tt / ModeSchedule.Lh (h - D.SP.Δ) - D.U0),
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
                        (4 : ℝ) * ((1 : ℝ) + cutTail (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim δ Kt) ^
                          (3 : ℕ) *
                          cutTail (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim δ Kt +
                      ((1 : ℝ) + cutTail (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim δ Kt) ^ (4 : ℕ) *
                        multTail (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim δ'' D.S.Q0 Cm Kt)) *
                  ∏ j ∈ Finset.univ.erase l,
                    ∑ x ∈ Fsel j, ‖D.c j G (A.blkStart D.S.K I.1) (D.preAt I) (↑x : (D.Ms j
                      G).Md)‖) *
              ((dyadicGridLength A.G I.1)⁻¹ *
                ∫ (y : ℝ) in Set.Icc (dyadicGridLeft A.G I.1 I.2) (dyadicGridLeft A.G I.1 I.2 +
                  dyadicGridLength A.G I.1),
                  ‖augPhys X y‖) +
            (dyadicGridLength A.G I.1)⁻¹ * entryC κ' J Aw (D.threeBeta G I xs (h - D.SP.Δ) l a) *
                  (2 : ℝ) ^ (Aw + (4 : ℕ)) *
                ((2 : ℝ) * ((2 : ℝ) ^ (Iw + (1 : ℕ)))⁻¹ ^ (Aw + (1 : ℕ))) *
              ((((1 : ℝ) + multTail (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim δ'' D.S.Q0 Cm Kt) *
                    ((1 : ℝ) + cutTail (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim δ Kt) *
                  ∏ j ∈ Finset.univ.erase l,
                    ((eLpNorm
                          (fun
                              (u :
                                ↥(torusAnnihilator
                                    (rationalIntegerIntersection
                                      (tinySpan (fun (i : Fin (D.Ms j G).zc.dim) => (D.Ms j
                                        G).zc.θ i / (↑D.S.Q0 : ℝ))
                                        D.SP.Hn
                                        (D.SP.Tt⁻¹ /
                                          dyadicGridLength A.G (A.blkStart D.S.K I.1 - (2 : ℤ) *
                                            (↑D.S.K : ℤ))))))) =>
                            (D.Ms j G).torusGT D.S (h - D.SP.Δ) xs (Fsel j)
                              (fun
                                  (x :
                                    ↥((D.Ms j G).alive
                                        (ancAt A.G (D.preAt I) (A.blkStart D.S.K I.1 - (4 : ℤ) *
                                          (↑D.S.K : ℤ))))) =>
                                D.c j G (A.blkStart D.S.K I.1) (D.preAt I) (↑x : (D.Ms j G).Md))
                              (n j) (↑u : StandardTorus (D.Ms j G).zc.dim))
                          (2 : ℝ≥0∞)
                          (torusAnnihilatorHaar
                            (rationalIntegerIntersection
                              (tinySpan (fun (i : Fin (D.Ms j G).zc.dim) => (D.Ms j G).zc.θ i /
                                (↑D.S.Q0 : ℝ)) D.SP.Hn
                                (D.SP.Tt⁻¹ /
                                  dyadicGridLength A.G (A.blkStart D.S.K I.1 - (2 : ℤ) * (↑D.S.K
                                    : ℤ))))))).toReal +
                      cutTail (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim δ Kt *
                        ∑ x ∈ Fsel j, ‖D.c j G (A.blkStart D.S.K I.1) (D.preAt I) (↑x : (D.Ms j
                          G).Md)‖)) *
                √(dyadicGridLength A.G I.1 *
                    ∫ (y : ℝ) in dyadicGridLeft A.G I.1 I.2..dyadicGridLeft A.G I.1 I.2 +
                      dyadicGridLength A.G I.1,
                      ‖augPhys X y‖ ^ (2 : ℕ))) +
          multNorm (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim δ'' D.S.Q0 Cm *
              (cutNorm (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim δ *
                ∏ j ∈ Finset.univ.erase l,
                  cutNorm (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim δ *
                    ∑ x ∈ Fsel j, ‖D.c j G (A.blkStart D.S.K I.1) (D.preAt I) (↑x : (D.Ms j
                      G).Md)‖) *
            (((dyadicGridLength A.G I.1)⁻¹ *
                ∫ (y : ℝ) in Set.Ico (dyadicGridLeft A.G I.1 I.2) (dyadicGridLeft A.G I.1 I.2 +
                  dyadicGridLength A.G I.1),
                  ‖augPhys X y‖) *
              (nearB κ' (D.SP.Tt⁻¹ / ModeSchedule.Lh (h - D.SP.Δ)) +
                (12 : ℝ) * (kerC κ' J * ((4 : ℝ) / (D.SP.Tt / ModeSchedule.Lh (h - D.SP.Δ) -
                  D.U0)) ^ (J - (2 : ℕ))))) +
        ∑ i ∈ Finset.range (Iw + (1 : ℕ)),
          (dyadicGridLength A.G I.1)⁻¹ * entryC κ' J Aw (D.threeBeta G I xs (h - D.SP.Δ) l a) *
            (2 : ℝ) ^ (Aw + (4 : ℕ)) *
                ((2 : ℝ) ^ i)⁻¹ ^ (Aw + (1 : ℕ)) *
              (((1 : ℝ) + multTail (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim δ'' D.S.Q0 Cm Kt) *
                  ((1 : ℝ) + cutTail (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim δ Kt) *
                ∏ j ∈ Finset.univ.erase l,
                  ((eLpNorm
                        (fun
                            (u :
                              ↥(torusAnnihilator
                                  (rationalIntegerIntersection
                                    (tinySpan (fun (i : Fin (D.Ms j G).zc.dim) => (D.Ms j
                                      G).zc.θ i / (↑D.S.Q0 : ℝ))
                                      D.SP.Hn
                                      (D.SP.Tt⁻¹ /
                                        dyadicGridLength A.G (A.blkStart D.S.K I.1 - (2 : ℤ) *
                                          (↑D.S.K : ℤ))))))) =>
                          (D.Ms j G).torusGT D.S (h - D.SP.Δ) xs (Fsel j)
                            (fun
                                (x :
                                  ↥((D.Ms j G).alive
                                      (ancAt A.G (D.preAt I) (A.blkStart D.S.K I.1 - (4 : ℤ) *
                                        (↑D.S.K : ℤ))))) =>
                              D.c j G (A.blkStart D.S.K I.1) (D.preAt I) (↑x : (D.Ms j G).Md))
                            (n j) (↑u : StandardTorus (D.Ms j G).zc.dim))
                        (2 : ℝ≥0∞)
                        (torusAnnihilatorHaar
                          (rationalIntegerIntersection
                            (tinySpan (fun (i : Fin (D.Ms j G).zc.dim) => (D.Ms j G).zc.θ i /
                              (↑D.S.Q0 : ℝ)) D.SP.Hn
                              (D.SP.Tt⁻¹ /
                                dyadicGridLength A.G (A.blkStart D.S.K I.1 - (2 : ℤ) * (↑D.S.K :
                                  ℤ))))))).toReal +
                    cutTail (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim δ Kt *
                      ∑ x ∈ Fsel j, ‖D.c j G (A.blkStart D.S.K I.1) (D.preAt I) (↑x : (D.Ms j
                        G).Md)‖)) *
            √(∫ (ρ' : Fin (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim → ℝ),
                sideWinE (D.Ms (0 : Fin (4 : ℕ)) G).zc l (augPhys X) (dyadicGridLeft A.G I.1 I.2)
                  (dyadicGridLength A.G I.1) (D.threeWin G I xs (h - D.SP.Δ) l a ((2 : ℝ) ^ i))
                  ρ' ∂offsetMeasure (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim))




private theorem three_core_test_conclusion_9 : ThreeCoreTestConclusion9Statement := by
  classical
  intro κ' c₀ A bf fp D hQ I hI G δ hδ hδc Cm hCm0 δ'' hδ'' Kt J h l Fsel n a xs X Aw Iw hr hw hDp
    hξ ρ' n' f hind hnorm ρc hρcj nn hnnj fv hfvl hfvj cα hcα hFj hXm hL2X cc0 hccT N hNb key
  have hΛc := @three_core_form κ' c₀ A bf fp D I hI G l Fsel X f fv hind hfvl hfvj
  obtain ⟨_, hPS, hPN⟩ := @three_core_coefficient_products κ' c₀ A bf fp D I G l Fsel xs cα hcα δ
  -- the truncated core torus sizes
  have hG : ∀ j ∈ Finset.univ.erase l, (eLpNorm (fun u : torusAnnihilator
      (rationalIntegerIntersection (tinySpan (fun i => (D.Ms 0 G).zc.θ i / D.S.Q0) D.SP.Hn
        (D.SP.Tt⁻¹ / dyadicGridLength A.G (A.blkStart D.S.K I.1 - 2 * D.S.K)))) =>
      coreG (D.S.Q0 * 6 ^ (h - D.SP.Δ)) (2 ^ (Kt + 1)) (sideOptF l Fsel) (sideOptC cα)
        (sideOptN nn) (fun j v => cc0 j v *
          (Real.fourierChar (∑ i, (v i : ℝ) * ((D.Ms 0 G).zc.θ i * xs)) : ℂ)) j u) 2
      (torusAnnihilatorHaar (rationalIntegerIntersection
        (tinySpan (fun i => (D.Ms 0 G).zc.θ i / D.S.Q0) D.SP.Hn
          (D.SP.Tt⁻¹ / dyadicGridLength A.G (A.blkStart D.S.K I.1 - 2 * D.S.K)))))).toReal ≤
      (eLpNorm (fun u : torusAnnihilator (rationalIntegerIntersection
          (tinySpan (fun i => (D.Ms j G).zc.θ i / D.S.Q0) D.SP.Hn
            (D.SP.Tt⁻¹ / dyadicGridLength A.G (A.blkStart D.S.K I.1 - 2 * D.S.K)))) =>
        (D.Ms j G).torusGT D.S (h - D.SP.Δ) xs (Fsel j)
          (fun x => D.c j G (A.blkStart D.S.K I.1) (D.preAt I) x.1) (n j) u.1) 2
        (torusAnnihilatorHaar (rationalIntegerIntersection
          (tinySpan (fun i => (D.Ms j G).zc.θ i / D.S.Q0) D.SP.Hn
            (D.SP.Tt⁻¹ / dyadicGridLength A.G
              (A.blkStart D.S.K I.1 - 2 * D.S.K)))))).toReal +
        cutTail (D.Ms 0 G).zc.dim δ Kt *
          ∑ x ∈ Fsel j, ‖D.c j G (A.blkStart D.S.K I.1) (D.preAt I) x.1‖ := fun j hj' => by
    have hj := Finset.ne_of_mem_erase hj'
    have e : (fun u : torusAnnihilator (rationalIntegerIntersection
        (tinySpan (fun i => (D.Ms 0 G).zc.θ i / D.S.Q0) D.SP.Hn
          (D.SP.Tt⁻¹ / dyadicGridLength A.G (A.blkStart D.S.K I.1 - 2 * D.S.K)))) =>
        coreG (D.S.Q0 * 6 ^ (h - D.SP.Δ)) (2 ^ (Kt + 1)) (sideOptF l Fsel) (sideOptC cα)
          (sideOptN nn) (fun j v => cc0 j v *
            (Real.fourierChar (∑ i, (v i : ℝ) * ((D.Ms 0 G).zc.θ i * xs)) : ℂ)) j u) =
        fun u => ∑ p ∈ frequencyBox (D.Ms 0 G).zc.dim (2 ^ (Kt + 1)) ×ˢ Fsel j,
          (cc0 j p.1 * (Real.fourierChar (∑ i, (p.1 i : ℝ) * ((D.Ms 0 G).zc.θ i * xs)) : ℂ) *
            (D.c j G (A.blkStart D.S.K I.1) (D.preAt I) p.2.1 *
              (Real.fourierChar ((D.Ms j G).phase p.2.1 xs) : ℂ))) *
          torusCharacter (((D.S.Q0 * 6 ^ (h - D.SP.Δ) : ℕ) : ℤ) • p.1 + n' j hj p.2) u.1 := by
      funext u
      unfold coreG
      rw [hFj j hj, Finset.sum_product, Finset.sum_product]
      refine Finset.sum_congr rfl fun v _ => ?_
      rw [Finset.sum_map]
      refine Finset.sum_congr rfl fun x _ => ?_
      simp only [Function.Embedding.some_apply, sideOptC, sideOptN, Option.elim, hcα,
        hnnj j hj]
    rw [e]
    have h1 := hnorm j hj (cc0 j) (fun w => by rw [hδc j, ← hρcj j hj]; exact hccT j w)
    rw [hδc j] at h1
    exact h1
  have hτc := cutTail_nonneg (D.Ms 0 G).zc.dim hδ Kt
  have hτm : 0 ≤ multTail (D.Ms 0 G).zc.dim δ'' D.S.Q0 Cm Kt := by
    unfold multTail
    have := profR_nonneg hδ'' ((D.Ms 0 G).zc.dim + (D.Ms 0 G).zc.dim + 1)
    positivity
  have h1τ : 0 ≤ (1 + multTail (D.Ms 0 G).zc.dim δ'' D.S.Q0 Cm Kt) *
      (1 + cutTail (D.Ms 0 G).zc.dim δ Kt) :=
    mul_nonneg (by linarith only [hτm]) (by linarith only [hτc])
  have hQW := mul_le_mul_of_nonneg_left
    (Finset.prod_le_prod₀ (fun _ _ => ENNReal.toReal_nonneg) hG) h1τ
  have hWf0 : 0 ≤ (1 + multTail (D.Ms 0 G).zc.dim δ'' D.S.Q0 Cm Kt) *
      (1 + cutTail (D.Ms 0 G).zc.dim δ Kt) * ∏ j ∈ Finset.univ.erase l,
        ((eLpNorm (fun u : torusAnnihilator (rationalIntegerIntersection
            (tinySpan (fun i => (D.Ms j G).zc.θ i / D.S.Q0) D.SP.Hn
              (D.SP.Tt⁻¹ / dyadicGridLength A.G (A.blkStart D.S.K I.1 - 2 * D.S.K)))) =>
          (D.Ms j G).torusGT D.S (h - D.SP.Δ) xs (Fsel j)
            (fun x => D.c j G (A.blkStart D.S.K I.1) (D.preAt I) x.1) (n j) u.1) 2
          (torusAnnihilatorHaar (rationalIntegerIntersection
            (tinySpan (fun i => (D.Ms j G).zc.θ i / D.S.Q0) D.SP.Hn
              (D.SP.Tt⁻¹ / dyadicGridLength A.G
                (A.blkStart D.S.K I.1 - 2 * D.S.K)))))).toReal +
          cutTail (D.Ms 0 G).zc.dim δ Kt *
            ∑ x ∈ Fsel j, ‖D.c j G (A.blkStart D.S.K I.1) (D.preAt I) x.1‖) :=
    mul_nonneg h1τ (Finset.prod_nonneg fun j _ => add_nonneg ENNReal.toReal_nonneg
      (mul_nonneg hτc (Finset.sum_nonneg fun _ _ => norm_nonneg _)))
  have heC := entryC_nonneg hr hw J Aw (D.threeBeta G I xs (h - D.SP.Δ) l a)
  have hbi : ∀ i : ℕ, 0 ≤ (dyadicGridLength A.G I.1)⁻¹ *
      entryC κ' J Aw (D.threeBeta G I xs (h - D.SP.Δ) l a) * 2 ^ (Aw + 4) *
      ((2 : ℝ) ^ i)⁻¹ ^ (Aw + 1) := fun i =>
    mul_nonneg (mul_nonneg (mul_nonneg (inv_nonneg.mpr hr.le) heC) (by positivity))
      (by positivity)
  have hc0 : 0 ≤ (dyadicGridLength A.G I.1)⁻¹ *
      entryC κ' J Aw (D.threeBeta G I xs (h - D.SP.Δ) l a) * 2 ^ (Aw + 4) *
      (2 * ((2 : ℝ) ^ (Iw + 1))⁻¹ ^ (Aw + 1)) :=
    mul_nonneg (mul_nonneg (mul_nonneg (inv_nonneg.mpr hr.le) heC) (by positivity))
      (by positivity)
  have hQsum : ∑ j, (if j = l then 0 else a j) =
      threeQ l a := by
    unfold threeQ
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ l)]
    simp only [↓reduceIte, zero_add]
    exact Finset.sum_congr rfl fun j hj => by simp only [Finset.ne_of_mem_erase hj, ↓reduceIte]
  rw [hfvl, hPS, hPN, mul_div_cancel₀ _ hr.ne'] at key
  rw [hΛc]
  refine key.trans (mul_le_mul_of_nonneg_left ?_ (by norm_num))
  refine add_le_add (add_le_add (add_le_add le_rfl ?_) le_rfl) ?_
  · exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hQW (Real.sqrt_nonneg _)) hc0
  · refine Finset.sum_le_sum fun i hi => mul_le_mul (mul_le_mul_of_nonneg_left hQW (hbi i)) ?_
      (Real.sqrt_nonneg _) (mul_nonneg (hbi i) hWf0)
    refine Real.sqrt_le_sqrt (integral_mono (window_energy_integrable _ l hXm hr hL2X _).1
      (window_energy_integrable _ l hXm hr hL2X _).1 fun ρ' => ?_)
    unfold sideWinE
    refine Finset.sum_le_sum_of_subset_of_nonneg (fun k hk => ?_) fun _ _ _ => by positivity
    obtain ⟨-, n₁, hn₁, hk₁⟩ := Finset.mem_filter.mp hk
    refine D.mem_threeWin hDp.le (hNb n₁ hn₁) ?_
    have e : (k : ℝ) - dyadicGridLength A.G I.1 * (threeQ l a +
        ∑ i, (n₁ i : ℝ) * (D.Ms 0 G).torusξ D.S (h - D.SP.Δ) i) =
        (k : ℝ) + -(dyadicGridLength A.G I.1 *
          (∑ j, (if j = l then 0 else a j) +
            ∑ i, (n₁ i : ℝ) * ((D.Ms 0 G).zc.θ i / (D.S.Q0 * (6 ^ (h - D.SP.Δ) : ℕ))))) := by
      rw [hQsum]; simp only [hξ]; ring
    have h2 : (0 : ℝ) ≤ 2 ^ i := by positivity
    rw [e]
    exact hk₁.trans (by linarith only [h2])



private theorem three_core_test_stage_1 : ThreeCoreTestStage1Statement := by
  classical
  intro κ' c₀ A bf fp D hQ I hI G δ hδ hdδ hδ8 hδc hcl hQC Cm hCm0 hCm δ'' hδ'' Kt J hJ h l Fsel n
    a xs hxs X Aw Iw hAw hr hw hDp hQ0 hLh hT0 hη hξ ρ' n' f hfa hfb hind hnorm ρc hρc hρcj nn
    hnnj fv hfvl hfvj cα hcα hFj hXm hL2X hfi hfiρ cc0 hcc0 hccN hccT N nref hNb hN hsep hnear
    hfar hH4
  have hε₁ : 0 ≤ D.SP.Tt⁻¹ / ModeSchedule.Lh (h - D.SP.Δ) :=
    div_nonneg (inv_nonneg.mpr hT0.le) hLh.le
  have key := three_core_averaged_of hr hw (D.Ms 0 G).zc hδ hδ'' hdδ hδ8 ρc hρc hQ0 hQC hCm0 hCm
    (L := 6 ^ (h - D.SP.Δ)) (pow_pos (by norm_num) _) Kt ⟨hxs.1, hxs.2.le⟩ l
    (fun j => if j = l then 0 else a j) (by simp)
    (sideOptF l Fsel) (sideOptC cα) (sideOptN nn) (k₀ := none) (by simp [sideOptF]) rfl rfl fv
    (by rw [hfvl]; exact hXm) (by rw [hfvl]; exact hL2X) hfi hfiρ hη
    (fun j hj y hy => ?_) (fun j hj y hy => ?_) cc0 hcc0 hccN (fun j _ w => hccT j w) _
    (D.threeRef G I xs (h - D.SP.Δ) l a) N hN
    (fun n => ∑ j, (if j = l then 0 else a j) +
      ∑ i, (n i : ℝ) * ((D.Ms 0 G).zc.θ i / (D.S.Q0 * (6 ^ (h - D.SP.Δ) : ℕ))))
    (D.threeBeta G I xs (h - D.SP.Δ) l a / dyadicGridLength A.G I.1) hsep nref hε₁ hH4
    (fun x hx hm => by
      obtain ⟨h1, h2, h3, h4⟩ := hnear x hx hm
      exact ⟨h1, h2, h3, by rwa [mul_div_cancel₀ _ hr.ne']⟩) hfar hJ Aw Iw hAw
  · expose_names
    exact @three_core_test_conclusion_9 κ' c₀ A bf fp D hQ I hI G δ hδ hδc Cm hCm0 δ'' hδ'' Kt J h
      l Fsel n a xs X Aw Iw hr hw hDp hξ ρ' n' f hind hnorm ρc hρcj nn hnnj fv hfvl hfvj cα hcα
      hFj hXm hL2X cc0 hccT N hNb key
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
/-- Blueprint `eq:side-windows` (lines 2536-2560) on a leaf cell `I` of the side states, for a
three-core tuple with side role `l` of the group `G` (all roles in the chart of role `0`): let
`F_j`, `j ≠ l`, be the selected modes of the core roles with their torus forms
`eq:core-torus-form` at the final height `h ≤ J_*` (representatives `a_j`, shifts of size at most
`D_* E_{h-Δ}`, error `D_*^{-150}`), let a role `j₀` be good at `h` (a successful component, whose
gap gives the tiny/huge dichotomy), and let the tuple have a reference for the three-core test
(`m = threeRef`, `β = threeBeta`; the threshold `|β| ≥ U₀⁻¹` is not used). Then for every side
column `X` (`S_phys = augPhys X`) the cell form with the three selected core subtotals and the side
`X` in slot `l` is at most twice
* the torus-form and gauge errors `2‖w‖_∞ (4 D_*^{-150} + E_g) Π_{j ≠ l} Σ_{F_j} |α|` times
  `r⁻¹ ∫_I |S_phys|`, plus
* the shells above `2^{I_w}`: `C_{J,A} μ ν^{-J} 2^{-(I_w+1)(A+1)} W Π_{j ≠ l} a''_j` times
  `(r ∫_I |S_phys|²)^{1/2}`, with `W = (1 + τ_m)(1 + τ_c)`, `a''_j = a'_j + τ_c Σ_{F_j} |α|` and
  `a'_j` the torus size of the true periodic factor of role `j` (`eq:torus-size`), plus
* the coset errors: tiny replacement errors (`ε₁ = T⁻¹/L_{h-Δ}`) and far-coset tails
  (`H = T/L_{h-Δ} - U₀ ≥ 4`) times the absolute coefficient sum
  `multNorm cutNorm Π_{j ≠ l} (cutNorm Σ_{F_j} |α|)` and `r⁻¹ ∫_I |S_phys|`, plus
* the window sum `Σ_{Λ = 2^i ≤ 2^{I_w}} C_{J,A} μ ν^{-J} Λ^{-(A+1)} W Π_{j ≠ l} a''_j b_Λ` of
  `eq:side-windows`, where `b_Λ² = E_{ρ_l} Σ_{k ∈ threeWin(Λ)} |SFourier'_ρ(k)|²` is the offset
    average of
  the side energies in the mask-independent windows `|k - r(Q + n·ξ)| ≤ 2Λ`, `|n|_∞ ≤ 16 B'`.
Here `C_{J,A} μ ν^{-J} = entryC κ J A β` with `μ = min(1, |β|)`, `ν = max(1, |β|)`. -/
theorem three_core_test {Cj CA CT CK : ℕ} {δs W : ℝ} (hV : D.S.Valid Cj CA CT CK δs W)
    (hCA : 1 ≤ CA) (hCT : 4 ≤ CT) (hd2 : 2 ≤ D.S.dmax) (hD : 2 ≤ D.S.Dstar)
    (hB : 2 ≤ D.S.Bstar) (hQ : 1 ≤ D.S.Q0) (hSP : D.SP = D.S.sideParams δs) {I : ℤ × ℤ}
    (hI : I ∈ A.cells) (G : bf.Grp) (hz : ∀ j, (D.Ms j G).zc = (D.Ms 0 G).zc)
    (hdim : (D.Ms 0 G).zc.dim ≤ D.S.dmax) {δ : ℝ} (hδ : 0 < δ)
    (hdδ : 8 * (D.Ms 0 G).zc.dim * δ ≤ 1) (hδ8 : δ ≤ 1 / 8) (hδc : ∀ j, (D.Ms j G).δc = δ)
    (hcl : ∀ j, (D.Ms j G).cl = slotCoeff j) (hρ : ∀ j k, (D.Ms j G).ρ k ∈ Set.Icc (0 : ℝ) 1)
    (hQC : ∀ a b, ∃ k : ℤ, (D.S.Q0 : ℝ) * ((D.Ms 0 G).zc.C a b : ℝ) = k) {Cm : ℝ}
    (hCm0 : 0 ≤ Cm) (hCm : ∀ a b, |((D.Ms 0 G).zc.C a b : ℝ)| ≤ Cm) {δ'' : ℝ} (hδ'' : 0 < δ'')
    {Kt : ℕ} (hQB : (D.S.Q0 : ℝ) * 2 ^ (Kt + 1) ≤ D.S.Bstar) {J : ℕ} (hJ : 2 ≤ J) {h : ℕ}
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
    (Aw Iw : ℕ) (hAw : 1 ≤ Aw) :
    ‖fp.Λc I (Function.update (fun j => D.compSub j G I
        ((Fsel j).map ⟨Subtype.val, Subtype.val_injective⟩)) l X)‖ ≤ 2 * (
      2 * localKernelSupBound κ' * ((4 * (D.S.Dstar ^ 150)⁻¹ +
          (gaugeErr (D.Ms 0 G).zc.dim δ δ'' +
            4 * (1 + cutTail (D.Ms 0 G).zc.dim δ Kt) ^ 3 * cutTail (D.Ms 0 G).zc.dim δ Kt +
            (1 + cutTail (D.Ms 0 G).zc.dim δ Kt) ^ 4 *
              multTail (D.Ms 0 G).zc.dim δ'' D.S.Q0 Cm Kt)) *
        ∏ j ∈ Finset.univ.erase l,
          ∑ x ∈ Fsel j, ‖D.c j G (A.blkStart D.S.K I.1) (D.preAt I) x.1‖) *
        ((dyadicGridLength A.G I.1)⁻¹ * ∫ y in Set.Icc (dyadicGridLeft A.G I.1 I.2)
          (dyadicGridLeft A.G I.1 I.2 + dyadicGridLength A.G I.1), ‖augPhys X y‖) +
      (dyadicGridLength A.G I.1)⁻¹ * entryC κ' J Aw (D.threeBeta G I xs (h - D.SP.Δ) l a) *
          2 ^ (Aw + 4) * (2 * ((2 : ℝ) ^ (Iw + 1))⁻¹ ^ (Aw + 1)) *
        (((1 + multTail (D.Ms 0 G).zc.dim δ'' D.S.Q0 Cm Kt) *
            (1 + cutTail (D.Ms 0 G).zc.dim δ Kt) * ∏ j ∈ Finset.univ.erase l,
            ((eLpNorm (fun u : torusAnnihilator (rationalIntegerIntersection
                (tinySpan (fun i => (D.Ms j G).zc.θ i / D.S.Q0) D.SP.Hn
                  (D.SP.Tt⁻¹ / dyadicGridLength A.G (A.blkStart D.S.K I.1 - 2 * D.S.K)))) =>
              (D.Ms j G).torusGT D.S (h - D.SP.Δ) xs (Fsel j)
                (fun x => D.c j G (A.blkStart D.S.K I.1) (D.preAt I) x.1) (n j) u.1) 2
              (torusAnnihilatorHaar (rationalIntegerIntersection
                (tinySpan (fun i => (D.Ms j G).zc.θ i / D.S.Q0) D.SP.Hn
                  (D.SP.Tt⁻¹ / dyadicGridLength A.G
                    (A.blkStart D.S.K I.1 - 2 * D.S.K)))))).toReal +
              cutTail (D.Ms 0 G).zc.dim δ Kt *
                ∑ x ∈ Fsel j, ‖D.c j G (A.blkStart D.S.K I.1) (D.preAt I) x.1‖)) *
          Real.sqrt (dyadicGridLength A.G I.1 * ∫ y in (dyadicGridLeft A.G I.1 I.2)..
            dyadicGridLeft A.G I.1 I.2 + dyadicGridLength A.G I.1, ‖augPhys X y‖ ^ 2)) +
      (multNorm (D.Ms 0 G).zc.dim δ'' D.S.Q0 Cm * (cutNorm (D.Ms 0 G).zc.dim δ *
          ∏ j ∈ Finset.univ.erase l, (cutNorm (D.Ms 0 G).zc.dim δ *
            ∑ x ∈ Fsel j, ‖D.c j G (A.blkStart D.S.K I.1) (D.preAt I) x.1‖))) *
        ((dyadicGridLength A.G I.1)⁻¹ * (∫ y in Set.Ico (dyadicGridLeft A.G I.1 I.2)
          (dyadicGridLeft A.G I.1 I.2 + dyadicGridLength A.G I.1), ‖augPhys X y‖) *
          (nearB κ' (D.SP.Tt⁻¹ / ModeSchedule.Lh (h - D.SP.Δ)) + 12 * (kerC κ' J *
            (4 / (D.SP.Tt / ModeSchedule.Lh (h - D.SP.Δ) - D.U0)) ^ (J - 2)))) +
      ∑ i ∈ Finset.range (Iw + 1), ((dyadicGridLength A.G I.1)⁻¹ *
          entryC κ' J Aw (D.threeBeta G I xs (h - D.SP.Δ) l a) * 2 ^ (Aw + 4) *
          ((2 : ℝ) ^ i)⁻¹ ^ (Aw + 1) * ((1 + multTail (D.Ms 0 G).zc.dim δ'' D.S.Q0 Cm Kt) *
            (1 + cutTail (D.Ms 0 G).zc.dim δ Kt) * ∏ j ∈ Finset.univ.erase l,
            ((eLpNorm (fun u : torusAnnihilator (rationalIntegerIntersection
                (tinySpan (fun i => (D.Ms j G).zc.θ i / D.S.Q0) D.SP.Hn
                  (D.SP.Tt⁻¹ / dyadicGridLength A.G (A.blkStart D.S.K I.1 - 2 * D.S.K)))) =>
              (D.Ms j G).torusGT D.S (h - D.SP.Δ) xs (Fsel j)
                (fun x => D.c j G (A.blkStart D.S.K I.1) (D.preAt I) x.1) (n j) u.1) 2
              (torusAnnihilatorHaar (rationalIntegerIntersection
                (tinySpan (fun i => (D.Ms j G).zc.θ i / D.S.Q0) D.SP.Hn
                  (D.SP.Tt⁻¹ / dyadicGridLength A.G
                    (A.blkStart D.S.K I.1 - 2 * D.S.K)))))).toReal +
              cutTail (D.Ms 0 G).zc.dim δ Kt *
                ∑ x ∈ Fsel j, ‖D.c j G (A.blkStart D.S.K I.1) (D.preAt I) x.1‖))) *
        Real.sqrt (∫ ρ', sideWinE (D.Ms 0 G).zc l (augPhys X) (dyadicGridLeft A.G I.1 I.2)
          (dyadicGridLength A.G I.1) (D.threeWin G I xs (h - D.SP.Δ) l a (2 ^ i)) ρ'
          ∂offsetMeasure (D.Ms 0 G).zc.dim)) := by
  have hr : 0 < dyadicGridLength A.G I.1 := dyadicGridLength_pos A.G I.1
  have hw := A.adm I hI
  have hDp : 0 < D.S.Dstar := by linarith
  have hQ0 : 0 < D.S.Q0 := hQ
  have hE0 : 0 ≤ D.S.Eh (h - D.SP.Δ) := pow_nonneg (by linarith [D.hA]) _
  have hh' : h - D.SP.Δ ≤ D.SP.Jst := le_trans (Nat.sub_le _ _) hh
  have hLh : 0 < ModeSchedule.Lh (h - D.SP.Δ) := pow_pos (by norm_num) _
  have hTt : D.SP.Tt = D.S.T := by rw [hSP]; rfl
  have hT0 : 0 < D.SP.Tt := by rw [hTt]; linarith [hV.one_le_T (by omega) hd2 hD hB hQ]
  have hη : (0 : ℝ) ≤ (D.S.Dstar ^ 150)⁻¹ := by positivity
  have hξ : ∀ i, (D.Ms 0 G).torusξ D.S (h - D.SP.Δ) i =
      (D.Ms 0 G).zc.θ i / (D.S.Q0 * (6 ^ (h - D.SP.Δ) : ℕ)) := fun i => by
    unfold ModeSystem.torusξ ModeSchedule.Lh; push_cast; ring
  obtain ⟨ρ', n', f, ρc, nn, fv, cα, cc0, hfa, hfb, hind, hnorm, hρc, hρcj, hnnj, hfvl, hfvj, hcα,
    hFj, hXm, hL2X, hfi, hfiρ, hcc0, hccN, hccT, hnn⟩ :=
    @three_core_inputs κ' c₀ A bf fp D I G hz δ hδ hδc hρ Kt h l Fsel n hn a xs hform X hr hw hDp
      hQ0 hE0 hη
  obtain ⟨N, nref, hNb, hN, hsep, hnear, hfar⟩ := D.three_cosets hV hCA hCT hd2 hD hB hQ hSP I G
    j₀ (hz j₀) hdim hh hgood hQB (sideOptF l Fsel) (sideOptN nn) hnn xs l a hne
  have hH4 : 4 ≤ D.SP.Tt / ModeSchedule.Lh (h - D.SP.Δ) - D.U0 := by
    have h1 := D.Tt_ge_U0_four hV hCT hd2 hD hB hQ hSP hh'
    rw [le_sub_iff_add_le, le_div_iff₀ hLh]
    linarith only [h1]
  expose_names
  exact @three_core_test_stage_1 κ' c₀ A bf fp D hQ I hI G δ hδ hdδ hδ8 hδc hcl hQC Cm hCm0 hCm
    δ'' hδ'' Kt J hJ h l Fsel n a xs hxs X Aw Iw hAw hr hw hDp hQ0 hLh hT0 hη hξ ρ' n' f hfa hfb
    hind hnorm ρc hρc hρcj nn hnnj fv hfvl hfvj cα hcα hFj hXm hL2X hfi hfiρ cc0 hcc0 hccN hccT N
    nref hNb hN hsep hnear hfar hH4

end SideInput

end ActiveSetup.BasicFamilies.FamParams

/-! ## The absolute numerical errors (blueprint `eq:core-numerical`, lines 2562-2567) -/

/-- `Π_{j ∈ s} (a_j + τ S_j) ≤ Π_{j ∈ s} a_j + ((1 + τ)^{|s|} - 1) Π_{j ∈ s} S_j` for
`0 ≤ a_j ≤ S_j` and `τ ≥ 0` (the truncation parts of the core sizes are replacement errors). -/
theorem prod_add_mul_le {ι : Type*} (s : Finset ι) {a S : ι → ℝ} {τ : ℝ} (hτ : 0 ≤ τ)
    (ha : ∀ j ∈ s, 0 ≤ a j) (haS : ∀ j ∈ s, a j ≤ S j) :
    ∏ j ∈ s, (a j + τ * S j) ≤ ∏ j ∈ s, a j + ((1 + τ) ^ s.card - 1) * ∏ j ∈ s, S j := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert k s hk ih =>
    have ha' : ∀ j ∈ s, 0 ≤ a j := fun j hj => ha j (Finset.mem_insert_of_mem hj)
    have haS' : ∀ j ∈ s, a j ≤ S j := fun j hj => haS j (Finset.mem_insert_of_mem hj)
    have ih' := ih ha' haS'
    have hak := ha k (Finset.mem_insert_self k s)
    have hkS := haS k (Finset.mem_insert_self k s)
    have hSk : 0 ≤ S k := hak.trans hkS
    have hA : 0 ≤ ∏ j ∈ s, a j := Finset.prod_nonneg ha'
    have hAB : ∏ j ∈ s, a j ≤ ∏ j ∈ s, S j := Finset.prod_le_prod₀ ha' haS'
    have hB : 0 ≤ ∏ j ∈ s, S j := hA.trans hAB
    have hq : 0 ≤ (1 + τ) ^ s.card - 1 := by
      have := one_le_pow₀ (by linarith : (1 : ℝ) ≤ 1 + τ) (n := s.card); linarith
    rw [Finset.prod_insert hk, Finset.prod_insert hk, Finset.prod_insert hk,
      Finset.card_insert_of_notMem hk]
    set A := ∏ j ∈ s, a j
    set B := ∏ j ∈ s, S j
    set q := (1 + τ) ^ s.card - 1 with hqdef
    have hq1 : (1 + τ) ^ s.card = q + 1 := by rw [hqdef]; ring
    have h1 : a k * (q * B) ≤ S k * (q * B) :=
      mul_le_mul_of_nonneg_right hkS (mul_nonneg hq hB)
    have h2 : τ * S k * A ≤ τ * S k * B := mul_le_mul_of_nonneg_left hAB (mul_nonneg hτ hSk)
    calc (a k + τ * S k) * ∏ j ∈ s, (a j + τ * S j) ≤ (a k + τ * S k) * (A + q * B) :=
          mul_le_mul_of_nonneg_left ih' (add_nonneg hak (mul_nonneg hτ hSk))
      _ ≤ a k * A + ((1 + τ) ^ (s.card + 1) - 1) * (S k * B) := by
          rw [pow_succ, hq1]
          nlinarith only [h1, h2]

/-- A four-core kernel sample is at most the constant `C₀` of `fourK_mu_nu` (`μ ≤ 1`). -/
theorem fourK_le_fourKC {κ : LocalKernelClass} {a₀ r : ℝ} (hr : 0 < r) {w : ℝ × ℝ → ℂ}
    (hw : IsAdmissibleLocalKernel κ a₀ r w) (x₀ A B : ℝ) :
    ‖fourK a₀ r w x₀ A B‖ ≤ fourKC κ 0 := by
  have h := fourK_mu_nu hr hw 0 x₀ A B
  change ‖fourK a₀ r w x₀ A B‖ * fourNu r A B ^ 0 ≤ fourKC κ 0 * fourMu r A B at h
  have hC : 0 ≤ fourKC κ 0 := by
    have := kernelDerivBound_nonneg κ 0
    unfold fourKC
    positivity
  rw [pow_zero, mul_one] at h
  exact h.trans (mul_le_of_le_one_right hC (fourMu_le_one r A B))

/-- The anchored expansion frequencies `P₂ - l P₁` of the core product (anchor `l`, including
`l = 0`, where it is `P₂`): with indices at most `B_x` and shifts at most `N_b`, their entries are
at most `4 L B_x + 6 (QL B_x + N_b)` (`Σ_j |j - l| ≤ 6`). -/
theorem expP_anchor_le {d : ℕ} (L QL Bx : ℕ) {ι : Fin 4 → Type*} (F : ∀ j, Finset (ι j))
    (n : ∀ j, ι j → Fin d → ℤ) {Nb : ℝ} (hn : ∀ j, ∀ k ∈ F j, ∀ i, |(n j k i : ℝ)| ≤ Nb)
    (x : (Fin (d + d) → ℤ) × ∀ j, (Fin d → ℤ) × ι j)
    (hx : x ∈ frequencyBox (d + d) Bx ×ˢ Fintype.piFinset (fun j => frequencyBox d Bx ×ˢ F j))
    (l : Fin 4) (i : Fin d) :
    |((expP2 L QL n x - ((l : ℕ) : ℤ) • expP1 L QL n x) i : ℝ)| ≤
      4 * (L * Bx) + 6 * (QL * Bx + Nb) := by
  obtain ⟨hx1, hx2⟩ := Finset.mem_product.mp hx
  have hb1 : ∀ k : Fin (d + d), |(x.1 k : ℝ)| ≤ Bx := fun k => by
    have := Fintype.mem_piFinset.mp hx1 k
    rw [Finset.mem_Icc] at this
    rw [abs_le]; constructor <;> exact_mod_cast (by omega : _)
  have hb2 : ∀ j, |((((QL : ℤ) • (x.2 j).1 + n j (x.2 j).2) i : ℤ) : ℝ)| ≤
      (QL * Bx + Nb : ℝ) := by
    intro j
    obtain ⟨hv, hk⟩ := Finset.mem_product.mp (Fintype.mem_piFinset.mp hx2 j)
    have hvi := Fintype.mem_piFinset.mp hv i
    rw [Finset.mem_Icc] at hvi
    have hvi' : |((x.2 j).1 i : ℝ)| ≤ Bx := by
      rw [abs_le]; constructor <;> exact_mod_cast (by omega : _)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    refine (abs_add_le _ _).trans (add_le_add ?_ (hn j _ hk i))
    rw [abs_mul, Nat.abs_cast]
    exact mul_le_mul_of_nonneg_left hvi' (Nat.cast_nonneg _)
  set b : Fin 4 → ℝ := fun j => ((((QL : ℤ) • (x.2 j).1 + n j (x.2 j).2) i : ℤ) : ℝ) with hbdef
  have e : ((expP2 L QL n x - ((l : ℕ) : ℤ) • expP1 L QL n x) i : ℝ) =
      (L : ℝ) * (x.1 (Fin.natAdd d i) : ℝ) -
        ((l : ℕ) : ℝ) * ((L : ℝ) * (x.1 (Fin.castAdd d i) : ℝ)) +
        ∑ j : Fin 4, (((j : ℕ) : ℝ) - ((l : ℕ) : ℝ)) * b j := by
    simp only [expP1, expP2, hbdef, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Finset.sum_apply]
    simp only [Fin.sum_univ_four]
    push_cast
    ring
  rw [e]
  have hL0 : (0 : ℝ) ≤ L := Nat.cast_nonneg _
  have hl3 : ((l : ℕ) : ℝ) ≤ 3 := by have := l.isLt; exact_mod_cast (by omega : (l : ℕ) ≤ 3)
  have hl0 : (0 : ℝ) ≤ (l : ℕ) := Nat.cast_nonneg _
  have hP : |(L : ℝ) * (x.1 (Fin.natAdd d i) : ℝ) -
      ((l : ℕ) : ℝ) * ((L : ℝ) * (x.1 (Fin.castAdd d i) : ℝ))| ≤ 4 * (L * Bx) := by
    have h1 : |(L : ℝ) * (x.1 (Fin.natAdd d i) : ℝ)| ≤ L * Bx := by
      rw [abs_mul, abs_of_nonneg hL0]; exact mul_le_mul_of_nonneg_left (hb1 _) hL0
    have h2 : |((l : ℕ) : ℝ) * ((L : ℝ) * (x.1 (Fin.castAdd d i) : ℝ))| ≤ 3 * (L * Bx) := by
      rw [abs_mul, abs_mul, abs_of_nonneg hl0, abs_of_nonneg hL0]
      exact mul_le_mul hl3 (mul_le_mul_of_nonneg_left (hb1 _) hL0) (by positivity)
        (by norm_num)
    have h3 := abs_sub ((L : ℝ) * (x.1 (Fin.natAdd d i) : ℝ))
      (((l : ℕ) : ℝ) * ((L : ℝ) * (x.1 (Fin.castAdd d i) : ℝ)))
    linarith
  have hB0 : (0 : ℝ) ≤ QL * Bx + Nb := (abs_nonneg _).trans (hb2 0)
  have hS : |∑ j : Fin 4, (((j : ℕ) : ℝ) - ((l : ℕ) : ℝ)) * b j| ≤ 6 * (QL * Bx + Nb) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hj : ∀ j : Fin 4, |(((j : ℕ) : ℝ) - ((l : ℕ) : ℝ)) * b j| ≤
        |((j : ℕ) : ℝ) - ((l : ℕ) : ℝ)| * (QL * Bx + Nb) := fun j => by
      rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hb2 j) (abs_nonneg _)
    refine (Finset.sum_le_sum fun j _ => hj j).trans ?_
    rw [← Finset.sum_mul]
    refine mul_le_mul_of_nonneg_right ?_ hB0
    fin_cases l <;> simp [Fin.sum_univ_four] <;> norm_num [abs_of_nonneg, abs_of_nonpos]
  exact (abs_add_le _ _).trans (add_le_add hP hS)

open Classical in
/-- Blueprint lines 2512-2514 and 2562-2567 (a four-core tuple without reference is discarded) with
the Fourier truncations made explicit: if every expansion frequency has
`ν = max(1, r|q'|, r|t'|) ≥ U₀`, every kernel sample is at most `C₁ U₀⁻¹` (`fourK_discard`), and the
local form is at most the numerical errors plus `C₁ U₀⁻¹` times the absolute expansion coefficient
sum. -/
theorem four_core_noref_of {κ : LocalKernelClass} {a₀ r : ℝ} (hr : 0 < r) {w : ℝ × ℝ → ℂ}
    (hw : IsAdmissibleLocalKernel κ a₀ r w) (z : ChartTag) {δ δ'' : ℝ}
    (hδ : 0 < δ) (hδ'' : 0 < δ'') (ρ : Fin 4 → Fin z.dim → ℝ)
    (hρ : ∀ j a, ρ j a ∈ Set.Icc (0 : ℝ) 1) {Q0 : ℕ} (hQ0 : 0 < Q0)
    (hQ : ∀ a b, ∃ k : ℤ, (Q0 : ℝ) * (z.C a b : ℝ) = k) {Cm : ℝ}
    (hCm : ∀ a b, |(z.C a b : ℝ)| ≤ Cm) {L : ℕ} (hL : 0 < L) (Kt : ℕ) {xs : ℝ}
    (γ : Fin 4 → ℝ) {ι : Fin 4 → Type*}
    (F : ∀ j, Finset (ι j)) (c : ∀ j, ι j → ℂ) (n : ∀ j, ι j → Fin z.dim → ℤ)
    (f : Fin 4 → ℝ → ℂ)
    (hfi : Integrable (fun zz : ℝ × ℝ => w zz * ∏ j, f j (realProgressionCoordinate j zz)))
    {η : ℝ} (hη : 0 ≤ η)
    (hfa : ∀ j, ∀ y ∈ Set.Icc a₀ (a₀ + r), ‖f j y - ((centerCut z δ (ρ j) y : ℂ) *
      (Real.fourierChar (((slotCoeff j : ℤ) : ℝ) * centerPhase z (ρ j) y) : ℂ)) *
        ((Real.fourierChar (γ j * (y - xs)) : ℂ) * ∑ k ∈ F j, c j k *
          torusCharacter (n j k) (torusMk fun i => z.θ i / (Q0 * L) * (y - xs)))‖ ≤
            η * ∑ k ∈ F j, ‖c j k‖)
    (hfb : ∀ j, ∀ y ∈ Set.Icc a₀ (a₀ + r), ‖f j y‖ ≤ ∑ k ∈ F j, ‖c j k‖)
    (cc0 : Fin 4 → (Fin z.dim → ℤ) → ℂ) (hcc0 : ∀ j v, ‖cc0 j v‖ ≤ 1)
    (hccT : ∀ j w, ‖cutoffP δ (ρ j) w - ∑ v ∈ frequencyBox z.dim (2 ^ (Kt + 1)),
      cc0 j v * (Real.fourierChar (∑ i, (v i : ℝ) * w i) : ℂ)‖ ≤ cutTail z.dim δ Kt)
    (cm0 : (Fin (z.dim + z.dim) → ℤ) → ℂ) (hcm0 : ∀ v, ‖cm0 v‖ ≤ 1)
    (hcmT : ∀ w, ‖gaugeMult δ'' Q0 0 z.C ρ w - ∑ v ∈ frequencyBox (z.dim + z.dim) (2 ^ (Kt + 1)),
      cm0 v * (Real.fourierChar (∑ i, (v i : ℝ) * w i) : ℂ)‖ ≤ multTail z.dim δ'' Q0 Cm Kt)
    {U₀ : ℝ} (hU₀ : 0 < U₀)
    (hnoref : ∀ x ∈ frequencyBox (z.dim + z.dim) (2 ^ (Kt + 1)) ×ˢ Fintype.piFinset
        (fun j => frequencyBox z.dim (2 ^ (Kt + 1)) ×ˢ F j),
      U₀ ≤ fourNu r (∑ j, γ j + ∑ i, (expP1 L (Q0 * L) n x i : ℝ) * (z.θ i / (Q0 * L)))
        (∑ j : Fin 4, ((j : ℕ) : ℝ) * γ j + ∑ i, (expP2 L (Q0 * L) n x i : ℝ) *
          (z.θ i / (Q0 * L)))) :
    ‖localProgressionForm r w f‖ ≤
      2 * localKernelSupBound κ * ((4 * η + (gaugeErr z.dim δ δ'' +
          4 * (1 + cutTail z.dim δ Kt) ^ 3 * cutTail z.dim δ Kt +
          (1 + cutTail z.dim δ Kt) ^ 4 * multTail z.dim δ'' Q0 Cm Kt)) *
        ∏ j, ∑ k ∈ F j, ‖c j k‖) +
      fourKC κ 1 * U₀⁻¹ *
        ∑ x ∈ frequencyBox (z.dim + z.dim) (2 ^ (Kt + 1)) ×ˢ Fintype.piFinset
            (fun j => frequencyBox z.dim (2 ^ (Kt + 1)) ×ˢ F j),
          ‖cm0 x.1 * (Real.fourierChar (∑ a, (x.1 (Fin.castAdd z.dim a) : ℝ) *
            (z.θ a * xs / Q0)) : ℂ) * ∏ j, (cc0 j (x.2 j).1 *
              (Real.fourierChar (∑ i, ((x.2 j).1 i : ℝ) * (z.θ i * xs)) : ℂ) *
              c j (x.2 j).2)‖ := by
  obtain ⟨cc, cm, hccE, hcmE, -, -, -, -, hg⟩ :=
    gauge_torus_approx_of z hδ hδ'' ρ hρ hQ0 hQ hCm hL Kt xs cc0 hcc0 hccT cm0 hcm0 hcmT
  have ecc : cc = fun j v => cc0 j v * (Real.fourierChar (∑ i, (v i : ℝ) * (z.θ i * xs)) : ℂ) :=
    funext fun j => funext fun v => hccE j v
  have ecm : cm = fun v => cm0 v *
      (Real.fourierChar (∑ a, (v (Fin.castAdd z.dim a) : ℝ) * (z.θ a * xs / Q0)) : ℂ) :=
    funext hcmE
  subst ecc ecm
  have hprod := fun x t (hxt : ∀ j : Fin 4, x + ((j : ℕ) : ℝ) * t ∈ Set.Icc a₀ (a₀ + r)) =>
    four_inputs_approx z δ ρ (fun i => z.θ i / (Q0 * L)) xs γ F c n f a₀ (a₀ + r) hη hfa hfb
      _ _ hg x t hxt
  have hS0 : 0 ≤ ∏ j, ∑ k ∈ F j, ‖c j k‖ :=
    Finset.prod_nonneg fun j _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hEg0 : 0 ≤ gaugeErr z.dim δ δ'' + 4 * (1 + cutTail z.dim δ Kt) ^ 3 *
      cutTail z.dim δ Kt + (1 + cutTail z.dim δ Kt) ^ 4 * multTail z.dim δ'' Q0 Cm Kt := by
    have := gaugeErr_nonneg z.dim hδ hδ''
    have := cutTail_nonneg z.dim hδ Kt
    have : 0 ≤ multTail z.dim δ'' Q0 Cm Kt := (norm_nonneg _).trans (hcmT 0)
    positivity
  have hτ : ∀ x ∈ frequencyBox (z.dim + z.dim) (2 ^ (Kt + 1)) ×ˢ Fintype.piFinset
      (fun j => frequencyBox z.dim (2 ^ (Kt + 1)) ×ˢ F j),
      ‖fourK a₀ r w xs (∑ j, γ j + ∑ i, (expP1 L (Q0 * L) n x i : ℝ) * (z.θ i / (Q0 * L)))
        (∑ j : Fin 4, ((j : ℕ) : ℝ) * γ j + ∑ i, (expP2 L (Q0 * L) n x i : ℝ) *
          (z.θ i / (Q0 * L)))‖ ≤ fourKC κ 1 * U₀⁻¹ := fun x hx =>
    fourK_discard hr hw le_rfl xs _ _ hU₀ (Or.inr (hnoref x hx))
  have hcmE1 : ∀ v, ‖cm0 v *
      (Real.fourierChar (∑ a, (v (Fin.castAdd z.dim a) : ℝ) * (z.θ a * xs / Q0)) : ℂ)‖ ≤ 1 :=
    fun v => by rw [norm_mul, Circle.norm_coe, mul_one]; exact hcm0 v
  have hb := four_core_cell_bound hr hw f hfi ⊥ (fun i => z.θ i / (Q0 * L)) xs γ
    (frequencyBox (z.dim + z.dim) (2 ^ (Kt + 1))) _
    (fun q => ((L : ℤ) • fun a => q (Fin.castAdd z.dim a),
      (L : ℤ) • fun a => q (Fin.natAdd z.dim a)))
    (fun j => frequencyBox z.dim (2 ^ (Kt + 1)) ×ˢ F j) _
    (fun j p => (((Q0 * L : ℕ) : ℤ) • p.1 + n j p.2)) (mul_nonneg (by linarith) hS0)
    (fun zz hzz => hprod zz.1 zz.2 fun j => by
      have := hw.support zz hzz j
      simp only [realProgressionCoordinate] at this
      have hm := mul_nonneg κ.margin_pos.le hr.le
      exact ⟨by linarith [this.1], by linarith [this.2]⟩)
    0 0 (ε := fourKC κ 1 * U₀⁻¹) (τ := fourKC κ 1 * U₀⁻¹)
    (fun x hx _ => by rw [sub_zero]; exact hτ x hx) (fun x hx _ => hτ x hx)
    (Nat.cast_nonneg (frequencyBox (z.dim + z.dim) (2 ^ (Kt + 1))).card)
    (fun u v => truncMult_le_card _ L _ hcmE1 u v)
  rw [norm_zero, zero_mul, zero_add, max_self] at hb
  exact hb

namespace ModeSystem
variable {Gd : RealDyadicGrid} {Mc : ℕ} (Ms : ModeSystem Gd Mc) (S : ModeSchedule)

open Classical in
/-- The torus size of the true periodic factor is at most its absolute coefficient sum: the true
periodic cutoff is at most one, the characters are unimodular, and `𝓗` is a probability space. -/
theorem torusGT_eLpNorm_le_sum (hδ : 0 < Ms.δc) {U : ℤ × ℤ} (h : ℕ) (xs : ℝ)
    (F : Finset (Ms.alive U)) (α : Ms.alive U → ℂ) (n : Ms.alive U → Fin Ms.zc.dim → ℤ)
    (V : Submodule ℚ (Fin Ms.zc.dim → ℚ)) :
    (eLpNorm (fun x : torusAnnihilator (rationalIntegerIntersection V) =>
        Ms.torusGT S h xs F α n x.1) 2
        (torusAnnihilatorHaar (rationalIntegerIntersection V))).toReal ≤ ∑ x ∈ F, ‖α x‖ := by
  have hb : ∀ x, ‖Ms.torusGT S h xs F α n x‖ ≤ ∑ m ∈ F, ‖α m‖ := by
    intro x
    unfold torusGT torusG
    rw [norm_mul]
    refine (mul_le_of_le_one_left (norm_nonneg _) (cutoffP_norm_le _ _ _)).trans ?_
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => ?_)
    rw [norm_mul, norm_mul, Circle.norm_coe, Circle.norm_coe, mul_one, mul_one]
  have h1 := eLpNorm_two_toReal_le_add (μ := torusAnnihilatorHaar (rationalIntegerIntersection V))
    ((Ms.measurable_torusGT S hδ h xs F α n).comp measurable_subtype_coe).aestronglyMeasurable
    (aestronglyMeasurable_const (b := (0 : ℂ))) (B := 0) (fun _ => by simp)
    (Finset.sum_nonneg fun _ _ => norm_nonneg _) (fun x => by simpa using hb x.1)
  have e0 : (eLpNorm (fun _ : torusAnnihilator (rationalIntegerIntersection V) => (0 : ℂ)) 2
      (torusAnnihilatorHaar (rationalIntegerIntersection V))).toReal = 0 := by simp
  rw [e0, zero_add] at h1
  exact h1

end ModeSystem

open Classical in
/-- Blueprint `eq:frequency-box` for the combined expansion frequencies: with shifts at most
`D_* E_{h'}`, truncated cutoff indices `Q₀ L_{h'} v` and multiplier indices `L_{h'} v`
(`|v|_∞ ≤ 2^{K_t+1}`, `Q₀ 2^{K_t+1} ≤ B_*`), the horizontal frequency `P₁` and every anchored
frequency `P₂ - l P₁` of the core product lie in the full box `B'_{h'} = D_*^5 E_{h'}`. -/
theorem expP_fullBox (S : ModeSchedule) (hA6 : 6 ≤ S.A0) (hBA : S.Bstar ≤ S.A0)
    (hD : 2 ≤ S.Dstar) (hQ : 1 ≤ S.Q0) {Kt : ℕ} (hQB : (S.Q0 : ℝ) * 2 ^ (Kt + 1) ≤ S.Bstar)
    {d h' : ℕ} {ι : Fin 4 → Type*} (F : ∀ j, Finset (ι j)) (n : ∀ j, ι j → Fin d → ℤ)
    (hn : ∀ j, ∀ k ∈ F j, ∀ i, |(n j k i : ℝ)| ≤ S.Dstar * S.Eh h')
    (x : (Fin (d + d) → ℤ) × ∀ j, (Fin d → ℤ) × ι j)
    (hx : x ∈ frequencyBox (d + d) (2 ^ (Kt + 1)) ×ˢ
      Fintype.piFinset (fun j => frequencyBox d (2 ^ (Kt + 1)) ×ˢ F j)) (l : Fin 4) (i : Fin d) :
    |(expP1 (6 ^ h') (S.Q0 * 6 ^ h') n x i : ℝ)| ≤ S.Dstar ^ 5 * S.Eh h' ∧
      |((expP2 (6 ^ h') (S.Q0 * 6 ^ h') n x - ((l : ℕ) : ℤ) •
        expP1 (6 ^ h') (S.Q0 * 6 ^ h') n x) i : ℝ)| ≤ S.Dstar ^ 5 * S.Eh h' := by
  have hE0 : 0 ≤ S.Eh h' := by unfold ModeSchedule.Eh; exact pow_nonneg (by linarith) _
  have hQ1 : (1 : ℝ) ≤ S.Q0 := by exact_mod_cast hQ
  have hLh0 : 0 ≤ ModeSchedule.Lh h' := by unfold ModeSchedule.Lh; positivity
  have hQL : (S.Q0 : ℝ) * 6 ^ h' * 2 ^ (Kt + 1) ≤ S.Eh h' := by
    have hE := S.Bstar_Lh_le_Eh hA6 hBA h'
    calc (S.Q0 : ℝ) * 6 ^ h' * 2 ^ (Kt + 1) = ((S.Q0 : ℝ) * 2 ^ (Kt + 1)) * ModeSchedule.Lh h' := by
          unfold ModeSchedule.Lh; ring
      _ ≤ S.Bstar * ModeSchedule.Lh h' := mul_le_mul_of_nonneg_right hQB hLh0
      _ ≤ S.Eh h' := hE
  have hLB : (6 : ℝ) ^ h' * 2 ^ (Kt + 1) ≤ S.Eh h' := by
    refine le_trans ?_ hQL
    have h0 : (0 : ℝ) ≤ 6 ^ h' * 2 ^ (Kt + 1) := by positivity
    nlinarith only [hQ1, h0]
  have hD5 : 10 + 6 * S.Dstar ≤ S.Dstar ^ 5 := by
    have h4 : (16 : ℝ) ≤ S.Dstar ^ 4 :=
      calc (16 : ℝ) = 2 ^ 4 := by norm_num
        _ ≤ S.Dstar ^ 4 := pow_le_pow_left₀ (by norm_num) hD 4
    have : S.Dstar ^ 5 = S.Dstar ^ 4 * S.Dstar := pow_succ _ _
    nlinarith only [hD, h4]
  have hDE := mul_le_mul_of_nonneg_right hD5 hE0
  obtain ⟨h1, -⟩ := expP_entries_le (6 ^ h') (S.Q0 * 6 ^ h') (2 ^ (Kt + 1)) F n hn x hx i
  have h2 := expP_anchor_le (6 ^ h') (S.Q0 * 6 ^ h') (2 ^ (Kt + 1)) F n hn x hx l i
  push_cast at h1 h2
  have hD0 : 0 ≤ S.Dstar * S.Eh h' := mul_nonneg (by linarith) hE0
  constructor
  · nlinarith only [hD, hE0, hQL, hLB, hD5, h1]
  · nlinarith only [hE0, hQL, hLB, hD5, h2]

namespace ActiveSetup.BasicFamilies.FamParams
variable {κ' : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ' c₀} {bf : A.BasicFamilies}
  {fp : bf.FamParams}

namespace SideInput
variable (D : fp.SideInput)

/-- The torus size `a'_j = ‖g_j‖_{L²(𝓗)}` (blueprint `eq:torus-size`) of the true periodic factor of
a core role `j` with selected modes `F` and shifts `n` at a leaf cell `I` and torus height `h'`
(`𝓗` the annihilator torus of the tiny-frequency space of the chart of role `j`). -/
noncomputable def coreSize (G : bf.Grp) (I : ℤ × ℤ) (xs : ℝ) (h' : ℕ) (j : Fin 4)
    (F : Finset ((D.Ms j G).alive (ancAt A.G (D.preAt I) (A.blkStart D.S.K I.1 - 4 * D.S.K))))
    (n : (D.Ms j G).alive (ancAt A.G (D.preAt I) (A.blkStart D.S.K I.1 - 4 * D.S.K)) →
      Fin (D.Ms j G).zc.dim → ℤ) : ℝ :=
  (eLpNorm (fun u : torusAnnihilator (rationalIntegerIntersection
      (tinySpan (fun i => (D.Ms j G).zc.θ i / D.S.Q0) D.SP.Hn
        (D.SP.Tt⁻¹ / dyadicGridLength A.G (A.blkStart D.S.K I.1 - 2 * D.S.K)))) =>
    (D.Ms j G).torusGT D.S h' xs F
      (fun x => D.c j G (A.blkStart D.S.K I.1) (D.preAt I) x.1) n u.1) 2
    (torusAnnihilatorHaar (rationalIntegerIntersection
      (tinySpan (fun i => (D.Ms j G).zc.θ i / D.S.Q0) D.SP.Hn
        (D.SP.Tt⁻¹ / dyadicGridLength A.G (A.blkStart D.S.K I.1 - 2 * D.S.K)))))).toReal

/-- The absolute coefficient sum `Σ_{m ∈ F} |α_m|` of selected modes of a role `j`. -/
noncomputable def coefSum (G : bf.Grp) (I : ℤ × ℤ) (j : Fin 4)
    (F : Finset ((D.Ms j G).alive (ancAt A.G (D.preAt I) (A.blkStart D.S.K I.1 - 4 * D.S.K)))) :
    ℝ :=
  ∑ x ∈ F, ‖D.c j G (A.blkStart D.S.K I.1) (D.preAt I) x.1‖

theorem coefSum_nonneg (G : bf.Grp) (I : ℤ × ℤ) (j : Fin 4)
    (F : Finset ((D.Ms j G).alive (ancAt A.G (D.preAt I) (A.blkStart D.S.K I.1 - 4 * D.S.K)))) :
    0 ≤ D.coefSum G I j F :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

/-- The torus size of a core role is at most its absolute coefficient sum
(`torusGT_eLpNorm_le_sum`). -/
theorem coreSize_le (G : bf.Grp) (I : ℤ × ℤ) (xs : ℝ) (h' : ℕ) (j : Fin 4)
    (hδ : 0 < (D.Ms j G).δc)
    (F : Finset ((D.Ms j G).alive (ancAt A.G (D.preAt I) (A.blkStart D.S.K I.1 - 4 * D.S.K))))
    (n : (D.Ms j G).alive (ancAt A.G (D.preAt I) (A.blkStart D.S.K I.1 - 4 * D.S.K)) →
      Fin (D.Ms j G).zc.dim → ℤ) :
    D.coreSize G I xs h' j F n ≤ D.coefSum G I j F :=
  (D.Ms j G).torusGT_eLpNorm_le_sum D.S hδ h' xs F _ n _

theorem coreSize_nonneg (G : bf.Grp) (I : ℤ × ℤ) (xs : ℝ) (h' : ℕ) (j : Fin 4)
    (F : Finset ((D.Ms j G).alive (ancAt A.G (D.preAt I) (A.blkStart D.S.K I.1 - 4 * D.S.K))))
    (n : (D.Ms j G).alive (ancAt A.G (D.preAt I) (A.blkStart D.S.K I.1 - 4 * D.S.K)) →
      Fin (D.Ms j G).zc.dim → ℤ) :
    0 ≤ D.coreSize G I xs h' j F n :=
  ENNReal.toReal_nonneg

/-- At the chosen schedule `L_{h'} Ξ ≤ T` for `h' ≤ J_*` (`T > H Ξ`, `H > L_{J_*}`). -/
theorem Lh_mul_Ξ_le_Tt {Cj CA CT CK : ℕ} {δs W : ℝ} (hV : D.S.Valid Cj CA CT CK δs W)
    (hCT : 4 ≤ CT) (hd2 : 2 ≤ D.S.dmax) (hD : 2 ≤ D.S.Dstar) (hB : 2 ≤ D.S.Bstar)
    (hQ : 1 ≤ D.S.Q0) (hSP : D.SP = D.S.sideParams δs) {h' : ℕ} (hh : h' ≤ D.SP.Jst) :
    ModeSchedule.Lh h' * D.S.Ξ ≤ D.SP.Tt := by
  have hTt : D.SP.Tt = D.S.T := by rw [hSP]; rfl
  have hJst : D.SP.Jst = D.S.Jstar := by rw [hSP]; rfl
  rw [hTt]
  have hT := hV.H_mul_Ξ_lt_T (by omega) hd2 hD hB hQ
  have hH := hV.H_ge hd2 hD hB hQ
  have hA := hV.one_le_A0 hd2 hD hB
  have hE : 1 ≤ D.S.Eh D.S.Jstar := one_le_pow₀ hA
  have hLJ : (1 : ℝ) ≤ ModeSchedule.Lh D.S.Jstar := one_le_pow₀ (by norm_num)
  have hL : ModeSchedule.Lh h' ≤ ModeSchedule.Lh D.S.Jstar :=
    pow_le_pow_right₀ (by norm_num) (by rw [← hJst]; exact hh)
  have hD1 : (1 : ℝ) ≤ D.S.Dstar := by linarith
  have hLH : ModeSchedule.Lh D.S.Jstar ≤ D.S.H := by
    have hEL : ModeSchedule.Lh D.S.Jstar ≤ D.S.Eh D.S.Jstar * ModeSchedule.Lh D.S.Jstar :=
      le_mul_of_one_le_left (by linarith) hE
    have h1 : ModeSchedule.Lh D.S.Jstar ≤ (D.S.Eh D.S.Jstar * ModeSchedule.Lh D.S.Jstar) ^ 2 :=
      hEL.trans (le_self_pow₀ (le_trans hLJ hEL) (by norm_num))
    have h2 : 0 ≤ (D.S.Eh D.S.Jstar * ModeSchedule.Lh D.S.Jstar) ^ 2 := sq_nonneg _
    have hD4 : (1 : ℝ) ≤ 27 * D.S.Dstar ^ 4 := by
      have : (1 : ℝ) ≤ D.S.Dstar ^ 4 := one_le_pow₀ hD1
      linarith
    have h3 := mul_le_mul_of_nonneg_right hD4 h2
    linarith
  have hΞ0 : 0 ≤ D.S.Ξ := by unfold ModeSchedule.Ξ; positivity
  calc ModeSchedule.Lh h' * D.S.Ξ ≤ D.S.H * D.S.Ξ :=
        mul_le_mul_of_nonneg_right (hL.trans hLH) hΞ0
    _ ≤ D.S.T := hT.le

open Classical in
/-- Blueprint lines 2512-2514 and 2562-2567 on a leaf cell of the side states (four cores, no
reference: the tuple is discarded). When no reference lies in the full box (`fourRefSet` empty),
every expansion frequency of the four transported core inputs has `ν ≥ U₀` (its horizontal and
vertical frequencies lie in the full box, `expP_fullBox`), so the cell form of the four selected
subtotals is at most the torus-form and gauge errors plus
`C₁ U₀⁻¹ multNorm Π_j (cutNorm Σ_{F_j} |α|)` (`four_core_noref_of`). -/
theorem four_core_noref_side {Cj CA CT CK : ℕ} {δs W : ℝ} (hV : D.S.Valid Cj CA CT CK δs W)
    (hCA : 1 ≤ CA) (hd2 : 2 ≤ D.S.dmax) (hD : 2 ≤ D.S.Dstar)
    (hB : 2 ≤ D.S.Bstar) (hQ : 1 ≤ D.S.Q0) {I : ℤ × ℤ}
    (hI : I ∈ A.cells) (G : bf.Grp) (hz : ∀ j, (D.Ms j G).zc = (D.Ms 0 G).zc)
    {δ : ℝ} (hδ : 0 < δ) (hδc : ∀ j, (D.Ms j G).δc = δ)
    (hcl : ∀ j, (D.Ms j G).cl = slotCoeff j) (hρ : ∀ j k, (D.Ms j G).ρ k ∈ Set.Icc (0 : ℝ) 1)
    (hQC : ∀ a b, ∃ k : ℤ, (D.S.Q0 : ℝ) * ((D.Ms 0 G).zc.C a b : ℝ) = k) {Cm : ℝ}
    (hCm0 : 0 ≤ Cm) (hCm : ∀ a b, |((D.Ms 0 G).zc.C a b : ℝ)| ≤ Cm) {δ'' : ℝ} (hδ'' : 0 < δ'')
    {Kt : ℕ} (hQB : (D.S.Q0 : ℝ) * 2 ^ (Kt + 1) ≤ D.S.Bstar) (h' : ℕ)
    (Fsel : ∀ j, Finset ((D.Ms j G).alive (ancAt A.G (D.preAt I)
      (A.blkStart D.S.K I.1 - 4 * D.S.K))))
    (n : ∀ j, (D.Ms j G).alive (ancAt A.G (D.preAt I) (A.blkStart D.S.K I.1 - 4 * D.S.K)) →
      Fin (D.Ms j G).zc.dim → ℤ)
    (hn : ∀ j, ∀ x ∈ Fsel j, ∀ i, |(n j x i : ℝ)| ≤ D.S.Dstar * D.S.Eh h')
    (a : ∀ j, (D.Ms j G).alive (ancAt A.G (D.preAt I) (A.blkStart D.S.K I.1 - 4 * D.S.K)))
    (xs : ℝ)
    (hform : ∀ j, ∀ y ∈ dyadicGridCell A.G I.1 I.2,
      ‖∑ x ∈ Fsel j, D.c j G (A.blkStart D.S.K I.1) (D.preAt I) x.1 * (D.Ms j G).wave x.1 y -
        (Real.fourierChar (((D.Ms j G).cl : ℝ) * centerPhase (D.Ms j G).zc (D.Ms j G).ρ y) : ℂ) *
          (Real.fourierChar ((D.Ms j G).slope (a j).1 xs * (y - xs)) : ℂ) *
          (D.Ms j G).torusG D.S h' xs (Fsel j)
            (fun x => D.c j G (A.blkStart D.S.K I.1) (D.preAt I) x.1) (n j)
            (fun i => (D.Ms j G).torusξ D.S h' i * (y - xs))‖ ≤
        (D.S.Dstar ^ 150)⁻¹ * D.coefSum G I j (Fsel j))
    (hnoref : D.fourRefSet G I xs h' a = ∅) :
    ‖fp.Λc I (fun j => D.compSub j G I ((Fsel j).map ⟨Subtype.val, Subtype.val_injective⟩))‖ ≤
      2 * localKernelSupBound κ' * ((4 * (D.S.Dstar ^ 150)⁻¹ +
          (gaugeErr (D.Ms 0 G).zc.dim δ δ'' +
            4 * (1 + cutTail (D.Ms 0 G).zc.dim δ Kt) ^ 3 * cutTail (D.Ms 0 G).zc.dim δ Kt +
            (1 + cutTail (D.Ms 0 G).zc.dim δ Kt) ^ 4 *
              multTail (D.Ms 0 G).zc.dim δ'' D.S.Q0 Cm Kt)) *
        ∏ j, D.coefSum G I j (Fsel j)) +
      fourKC κ' 1 * D.U0⁻¹ * (multNorm (D.Ms 0 G).zc.dim δ'' D.S.Q0 Cm *
        ∏ j, (cutNorm (D.Ms 0 G).zc.dim δ * D.coefSum G I j (Fsel j))) := by
  have hr : 0 < dyadicGridLength A.G I.1 := dyadicGridLength_pos A.G I.1
  have hw := A.adm I hI
  have hDp : 0 < D.S.Dstar := by linarith
  have hD1 : (1 : ℝ) ≤ D.S.Dstar := by linarith
  have hQ0 : 0 < D.S.Q0 := hQ
  have hη : (0 : ℝ) ≤ (D.S.Dstar ^ 150)⁻¹ := by positivity
  have hU0 : 0 < D.U0 := by unfold U0; positivity
  -- the roles in the chart of role `0`
  have hrole := fun j => (D.Ms j G).role_four_input D.S (D.Ms 0 G).zc (hz j)
    ((hδc j).symm ▸ hδ) hQ0 h' xs (Fsel j)
    (fun x => D.c j G (A.blkStart D.S.K I.1) (D.preAt I) x.1) (n j) Kt D.SP.Hn
    (D.SP.Tt⁻¹ / dyadicGridLength A.G (A.blkStart D.S.K I.1 - 2 * D.S.K))
    (a₀ := dyadicGridLeft A.G I.1 I.2) (r := dyadicGridLength A.G I.1) hη
    ((D.Ms j G).slope (a j).1 xs) (hform j)
  choose ρ' n' f hρ'e hn'e hfm hfa hfb hind hnorm using hrole
  have hρ'' : ∀ j i, ρ' j i ∈ Set.Icc (0 : ℝ) 1 := fun j i => by
    obtain ⟨k, hk⟩ := hρ'e j i; rw [hk]; exact hρ j k
  have hn'' : ∀ j, ∀ x ∈ Fsel j, ∀ i, |(n' j x i : ℝ)| ≤ D.S.Dstar * D.S.Eh h' :=
    fun j x hx i => by
      obtain ⟨k, hk⟩ := hn'e j x i
      rw [hk]; exact hn j x hx k
  have hfa' : ∀ j, ∀ y ∈ Set.Icc (dyadicGridLeft A.G I.1 I.2)
      (dyadicGridLeft A.G I.1 I.2 + dyadicGridLength A.G I.1),
      ‖f j y - ((centerCut (D.Ms 0 G).zc δ (ρ' j) y : ℂ) *
        (Real.fourierChar (((slotCoeff j : ℤ) : ℝ) * centerPhase (D.Ms 0 G).zc (ρ' j) y) : ℂ)) *
          ((Real.fourierChar ((D.Ms j G).slope (a j).1 xs * (y - xs)) : ℂ) *
            ∑ k ∈ Fsel j, (D.c j G (A.blkStart D.S.K I.1) (D.preAt I) k.1 *
              (Real.fourierChar ((D.Ms j G).phase k.1 xs) : ℂ)) *
              torusCharacter (n' j k) (torusMk fun i => (D.Ms 0 G).zc.θ i /
                (D.S.Q0 * (6 ^ h' : ℕ)) * (y - xs)))‖ ≤
        (D.S.Dstar ^ 150)⁻¹ * ∑ k ∈ Fsel j, ‖D.c j G (A.blkStart D.S.K I.1) (D.preAt I) k.1 *
          (Real.fourierChar ((D.Ms j G).phase k.1 xs) : ℂ)‖ := fun j y hy => by
    have h1 := hfa j y hy
    rw [hδc j, hcl j] at h1
    exact h1
  have hfi := form_integrable_of_bounded hr hw f hfm _ hfb
  -- the truncations
  have hcut := fun j => cutoffP_truncate_all hδ (ρ' j) Kt
  choose cc0 hcc0 hccN hccT using hcut
  obtain ⟨cm0, hcm0, hcmN, hcmT⟩ := gaugeMult_truncate_all hδ'' D.S.Q0 0 (D.Ms 0 G).zc.C ρ'
    hρ'' hQC hCm0 hCm Kt
  have hξ : ∀ i, (D.Ms 0 G).torusξ D.S h' i =
      (D.Ms 0 G).zc.θ i / (D.S.Q0 * (6 ^ h' : ℕ)) := fun i => by
    unfold ModeSystem.torusξ ModeSchedule.Lh; push_cast; ring
  -- no reference: every expansion frequency is far
  have hA6 : 6 ≤ D.S.A0 := D.hA
  have hBA := hV.Bstar_le_A0 hCA hd2 hD hB
  have hnoref' : ∀ x ∈ frequencyBox ((D.Ms 0 G).zc.dim + (D.Ms 0 G).zc.dim) (2 ^ (Kt + 1)) ×ˢ
      Fintype.piFinset (fun j => frequencyBox (D.Ms 0 G).zc.dim (2 ^ (Kt + 1)) ×ˢ Fsel j),
      D.U0 ≤ fourNu (dyadicGridLength A.G I.1)
        (∑ j, (D.Ms j G).slope (a j).1 xs + ∑ i, (expP1 (6 ^ h') (D.S.Q0 * 6 ^ h') n' x i : ℝ) *
          ((D.Ms 0 G).zc.θ i / (D.S.Q0 * (6 ^ h' : ℕ))))
        (∑ j : Fin 4, ((j : ℕ) : ℝ) * (D.Ms j G).slope (a j).1 xs +
          ∑ i, (expP2 (6 ^ h') (D.S.Q0 * 6 ^ h') n' x i : ℝ) *
            ((D.Ms 0 G).zc.θ i / (D.S.Q0 * (6 ^ h' : ℕ)))) := by
    intro x hx
    by_contra hlt
    push Not at hlt
    have hb := fun i => expP_fullBox D.S hA6 hBA hD hQ hQB Fsel n' hn'' x hx 0 i
    have hmem : (expP1 (6 ^ h') (D.S.Q0 * 6 ^ h') n' x, expP2 (6 ^ h') (D.S.Q0 * 6 ^ h') n' x) ∈
        D.fourRefSet G I xs h' a := by
      unfold fourRefSet
      refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨(D.mem_fullBox hDp.le).mpr
        fun i => (hb i).1, (D.mem_fullBox hDp.le).mpr fun i => ?_⟩, ?_, ?_⟩
      · have := (hb i).2
        simpa using this
      · have h1 : dyadicGridLength A.G I.1 * |∑ j, (D.Ms j G).slope (a j).1 xs +
            ∑ i, (expP1 (6 ^ h') (D.S.Q0 * 6 ^ h') n' x i : ℝ) *
              ((D.Ms 0 G).zc.θ i / (D.S.Q0 * (6 ^ h' : ℕ)))| < D.U0 :=
          lt_of_le_of_lt ((le_max_left _ _).trans (le_max_right _ _)) hlt
        unfold fourQ
        simp_rw [hξ]
        exact h1.le
      · have h1 : dyadicGridLength A.G I.1 * |∑ j : Fin 4, ((j : ℕ) : ℝ) *
            (D.Ms j G).slope (a j).1 xs + ∑ i, (expP2 (6 ^ h') (D.S.Q0 * 6 ^ h') n' x i : ℝ) *
              ((D.Ms 0 G).zc.θ i / (D.S.Q0 * (6 ^ h' : ℕ)))| < D.U0 :=
          lt_of_le_of_lt ((le_max_right _ _).trans (le_max_right _ _)) hlt
        unfold fourT
        simp_rw [hξ]
        exact h1.le
    rw [hnoref] at hmem
    exact Finset.notMem_empty _ hmem
  have key := four_core_noref_of hr hw (D.Ms 0 G).zc hδ hδ'' ρ' hρ'' hQ0 hQC hCm
    (L := 6 ^ h') (pow_pos (by norm_num) _) Kt (xs := xs)
    (fun j => (D.Ms j G).slope (a j).1 xs) Fsel
    (fun j k => D.c j G (A.blkStart D.S.K I.1) (D.preAt I) k.1 *
      (Real.fourierChar ((D.Ms j G).phase k.1 xs) : ℂ)) n' f hfi hη hfa' hfb cc0 hcc0 hccT
    cm0 hcm0 hcmT hU0 hnoref'
  rw [D.Λc_selected_eq hI G Fsel f hind]
  have hnα : ∀ j (k : (D.Ms j G).alive (ancAt A.G (D.preAt I) (A.blkStart D.S.K I.1 - 4 * D.S.K))),
      ‖D.c j G (A.blkStart D.S.K I.1) (D.preAt I) k.1 *
        (Real.fourierChar ((D.Ms j G).phase k.1 xs) : ℂ)‖ =
      ‖D.c j G (A.blkStart D.S.K I.1) (D.preAt I) k.1‖ := fun j k => by
    rw [norm_mul, Circle.norm_coe, mul_one]
  have hsum := expansion_coeff_sum (2 ^ (Kt + 1)) Fsel
    (fun v => cm0 v * (Real.fourierChar (∑ a, (v (Fin.castAdd (D.Ms 0 G).zc.dim a) : ℝ) *
      ((D.Ms 0 G).zc.θ a * xs / D.S.Q0)) : ℂ))
    (fun j v => cc0 j v * (Real.fourierChar (∑ i, (v i : ℝ) * ((D.Ms 0 G).zc.θ i * xs)) : ℂ))
    (fun j k => D.c j G (A.blkStart D.S.K I.1) (D.preAt I) k.1 *
      (Real.fourierChar ((D.Ms j G).phase k.1 xs) : ℂ))
  simp only [hnα] at key hsum
  have hC1 : 0 ≤ fourKC κ' 1 := by
    have := kernelDerivBound_nonneg κ' 0
    have := kernelDerivBound_nonneg κ' 1
    unfold fourKC
    positivity
  refine key.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left ((le_of_eq hsum).trans ?_)
    (mul_nonneg hC1 (inv_nonneg.mpr hU0.le))))
  simp_rw [norm_mul, Circle.norm_coe, mul_one]
  exact mul_le_mul (hcmN _) (Finset.prod_le_prod₀ (fun j _ => mul_nonneg
      (Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.sum_nonneg fun _ _ => norm_nonneg _))
      fun j _ => mul_le_mul_of_nonneg_right (hccN j _)
        (Finset.sum_nonneg fun _ _ => norm_nonneg _))
      (Finset.prod_nonneg fun j _ => mul_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)
        (Finset.sum_nonneg fun _ _ => norm_nonneg _))
      ((le_of_eq Finset.sum_empty.symm).trans (hcmN ∅))

end SideInput

end ActiveSetup.BasicFamilies.FamParams

/-- The torus-form and gauge errors at the enlarged gauge cutoff `δ/2` (zero gauge error,
`gaugeErr_half`) with truncation tails at most `D_*^{-300}` (blueprint `eq:core-numerical`):
`2K (4 D_*^{-150} + E_g) P ≤ 104 K D_*^{-100} P`. -/
theorem gauge_err_le {K D τc τm P δ : ℝ} (d : ℕ) (hD1 : 1 ≤ D) (hK : 0 ≤ K) (hP : 0 ≤ P)
    (hτc0 : 0 ≤ τc) (hτm0 : 0 ≤ τm) (hτc : τc ≤ (D ^ 300)⁻¹) (hτm : τm ≤ (D ^ 300)⁻¹) :
    2 * K * ((4 * (D ^ 150)⁻¹ + (gaugeErr d δ (δ / 2) + 4 * (1 + τc) ^ 3 * τc +
      (1 + τc) ^ 4 * τm)) * P) ≤ 104 * K * (D ^ 100)⁻¹ * P := by
  rw [gaugeErr_half, zero_add]
  have hpow : ∀ k : ℕ, 100 ≤ k → (D ^ k)⁻¹ ≤ (D ^ 100)⁻¹ := fun k hk =>
    inv_anti₀ (by positivity) (pow_le_pow_right₀ hD1 hk)
  have hu1 : (D ^ 100)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hD1)
  have h150 := hpow 150 (by norm_num)
  have hτc' : τc ≤ (D ^ 100)⁻¹ := hτc.trans (hpow 300 (by norm_num))
  have hτm' : τm ≤ (D ^ 100)⁻¹ := hτm.trans (hpow 300 (by norm_num))
  have hτc1 : τc ≤ 1 := hτc'.trans hu1
  have hA3 : (1 + τc) ^ 3 ≤ 8 :=
    calc (1 + τc) ^ 3 ≤ 2 ^ 3 := pow_le_pow_left₀ (by linarith) (by linarith) 3
      _ = 8 := by norm_num
  have hA4 : (1 + τc) ^ 4 ≤ 16 :=
    calc (1 + τc) ^ 4 ≤ 2 ^ 4 := pow_le_pow_left₀ (by linarith) (by linarith) 4
      _ = 16 := by norm_num
  have e1 : 4 * (1 + τc) ^ 3 * τc ≤ 4 * 8 * (D ^ 100)⁻¹ :=
    mul_le_mul (mul_le_mul_of_nonneg_left hA3 (by norm_num)) hτc' hτc0 (by norm_num)
  have e2 : (1 + τc) ^ 4 * τm ≤ 16 * (D ^ 100)⁻¹ := mul_le_mul hA4 hτm' hτm0 (by norm_num)
  have hsum : 4 * (D ^ 150)⁻¹ + (4 * (1 + τc) ^ 3 * τc + (1 + τc) ^ 4 * τm) ≤
      52 * (D ^ 100)⁻¹ := by linarith only [h150, e1, e2]
  have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hsum hP)
    (by positivity : (0 : ℝ) ≤ 2 * K)
  linarith only [this]

/-- The truncation parts of the core sizes (blueprint `eq:core-numerical`): for `0 ≤ a_j ≤ S_j` and
tails `τ_c, τ_m ≤ u ≤ 1`, `(1 + τ_m) Π_j (a_j + τ_c S_j) ≤ Π_j a_j + 31 u Π_j S_j`. -/
theorem trunc_core_err {a S : Fin 4 → ℝ} {τc τm u : ℝ} (ha0 : ∀ j, 0 ≤ a j)
    (haS : ∀ j, a j ≤ S j) (hτc0 : 0 ≤ τc) (hτm0 : 0 ≤ τm) (hτc : τc ≤ u) (hτm : τm ≤ u)
    (hu1 : u ≤ 1) :
    (1 + τm) * ∏ j, (a j + τc * S j) ≤ ∏ j, a j + 31 * u * ∏ j, S j := by
  have hprod := prod_add_mul_le Finset.univ hτc0 (fun j _ => ha0 j) (fun j _ => haS j)
  simp only [Finset.card_univ, Fintype.card_fin] at hprod
  have hu0 : 0 ≤ u := hτc0.trans hτc
  have hP0 : 0 ≤ ∏ j, S j := Finset.prod_nonneg fun j _ => (ha0 j).trans (haS j)
  have hPa0 : 0 ≤ ∏ j, a j := Finset.prod_nonneg fun j _ => ha0 j
  have hPaP : ∏ j, a j ≤ ∏ j, S j := Finset.prod_le_prod₀ (fun j _ => ha0 j) fun j _ => haS j
  have hτc1 : τc ≤ 1 := hτc.trans hu1
  have h15 : (1 + τc) ^ 4 - 1 ≤ 15 * τc := by
    have e : (1 + τc) ^ 4 - 1 = τc * (4 + 6 * τc + 4 * τc ^ 2 + τc ^ 3) := by ring
    have h2 : τc ^ 2 ≤ 1 := pow_le_one₀ hτc0 hτc1
    have h3 : τc ^ 3 ≤ 1 := pow_le_one₀ hτc0 hτc1
    have h4 : 4 + 6 * τc + 4 * τc ^ 2 + τc ^ 3 ≤ 15 := by linarith
    rw [e]
    calc τc * (4 + 6 * τc + 4 * τc ^ 2 + τc ^ 3) ≤ τc * 15 := mul_le_mul_of_nonneg_left h4 hτc0
      _ = 15 * τc := by ring
  have hq : ∏ j, (a j + τc * S j) ≤ ∏ j, a j + 15 * u * ∏ j, S j := by
    refine hprod.trans ?_
    have := mul_le_mul_of_nonneg_right (h15.trans (mul_le_mul_of_nonneg_left hτc
      (by norm_num))) hP0
    linarith
  have hτm1 : τm ≤ 1 := hτm.trans hu1
  have e1 := mul_le_mul_of_nonneg_left hq (by linarith : (0 : ℝ) ≤ 1 + τm)
  have e2 : τm * ∏ j, a j ≤ u * ∏ j, S j := mul_le_mul hτm hPaP hPa0 hu0
  have e3 : τm * (15 * u * ∏ j, S j) ≤ 15 * u * ∏ j, S j :=
    mul_le_of_le_one_left (by positivity) hτm1
  calc (1 + τm) * ∏ j, (a j + τc * S j) ≤ (1 + τm) * (∏ j, a j + 15 * u * ∏ j, S j) := e1
    _ = ∏ j, a j + 15 * u * ∏ j, S j + τm * ∏ j, a j + τm * (15 * u * ∏ j, S j) := by ring
    _ ≤ ∏ j, a j + 31 * u * ∏ j, S j := by linarith

/-- The absolute Fourier costs of the expansion: `multNorm Π_j (cutNorm S_j) ≤ D_*^5 Π_j S_j` when
both full Fourier norms are at most `D_*` (blueprint line 1944). -/
theorem norm_prod_le_pow {D MN CN : ℝ} {S : Fin 4 → ℝ} (hS : ∀ j, 0 ≤ S j) (hMN : MN ≤ D)
    (hCN0 : 0 ≤ CN) (hCN : CN ≤ D) :
    MN * ∏ j, (CN * S j) ≤ D ^ 5 * ∏ j, S j := by
  have hP0 : 0 ≤ ∏ j, S j := Finset.prod_nonneg fun j _ => hS j
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  calc MN * (CN ^ 4 * ∏ j, S j) ≤ D * (D ^ 4 * ∏ j, S j) :=
        mul_le_mul hMN (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hCN0 hCN 4) hP0)
          (mul_nonneg (pow_nonneg hCN0 4) hP0) ((hCN0.trans hCN))
    _ = D ^ 5 * ∏ j, S j := by ring

/-- `D_*^{-k} D_*^5 ≤ D_*^{-100}` for `k ≥ 105`. -/
theorem inv_pow_mul_pow5_le {D : ℝ} (hD1 : 1 ≤ D) {k : ℕ} (hk : 105 ≤ k) :
    (D ^ k)⁻¹ * D ^ 5 ≤ (D ^ 100)⁻¹ := by
  have hD0 : 0 < D := by linarith
  have e : (D ^ k)⁻¹ * D ^ 5 = (D ^ (k - 5))⁻¹ := by
    rw [show D ^ k = D ^ (k - 5) * D ^ 5 by rw [← pow_add]; congr 1; omega]
    field_simp
  rw [e]
  exact inv_anti₀ (by positivity) (pow_le_pow_right₀ hD1 (by omega))

/-- The coset replacement and tail errors (blueprint `eq:core-numerical`): with replacement
precision `ε ≤ D_*^{-999}`, far separation `H ≥ D_*^{999}`, `J ≥ 1` and full Fourier norms at
most `D_*`, `max(C ε, C_J H^{-J}) multNorm Π_j (cutNorm S_j) ≤ (C + C_J) D_*^{-100} Π_j S_j`. -/
theorem coset_err_le {D ε H nC kJ MN CN : ℝ} {J : ℕ} {S : Fin 4 → ℝ} (hJ : 1 ≤ J)
    (hD1 : 1 ≤ D) (hnC : 0 ≤ nC) (hkJ : 0 ≤ kJ) (hS : ∀ j, 0 ≤ S j) (hMN0 : 0 ≤ MN)
    (hMN : MN ≤ D) (hCN0 : 0 ≤ CN) (hCN : CN ≤ D) (hε : ε ≤ (D ^ 999)⁻¹) (hH : D ^ 999 ≤ H) :
    max (nC * ε) (kJ * (H ^ J)⁻¹) * (MN * ∏ j, (CN * S j)) ≤
      (nC + kJ) * (D ^ 100)⁻¹ * ∏ j, S j := by
  have h9 : (0 : ℝ) < D ^ 999 := by positivity
  have hP0 : 0 ≤ ∏ j, S j := Finset.prod_nonneg fun j _ => hS j
  have hM : max (nC * ε) (kJ * (H ^ J)⁻¹) ≤ (nC + kJ) * (D ^ 999)⁻¹ := by
    have hk9 : 0 ≤ kJ * (D ^ 999)⁻¹ := mul_nonneg hkJ (inv_nonneg.mpr h9.le)
    have hn9 : 0 ≤ nC * (D ^ 999)⁻¹ := mul_nonneg hnC (inv_nonneg.mpr h9.le)
    rw [add_mul]
    refine max_le ?_ ?_
    · have := mul_le_mul_of_nonneg_left hε hnC
      linarith
    · have hHJ : D ^ 999 ≤ H ^ J :=
        hH.trans (le_self_pow₀ ((one_le_pow₀ hD1).trans hH) (by omega))
      have := mul_le_mul_of_nonneg_left (inv_anti₀ h9 hHJ) hkJ
      linarith
  have hCNP := norm_prod_le_pow hS hMN hCN0 hCN
  have h994 := inv_pow_mul_pow5_le hD1 (k := 999) (by norm_num)
  calc max (nC * ε) (kJ * (H ^ J)⁻¹) * (MN * ∏ j, (CN * S j)) ≤
        (nC + kJ) * (D ^ 999)⁻¹ * (D ^ 5 * ∏ j, S j) :=
        mul_le_mul hM hCNP (mul_nonneg hMN0 (Finset.prod_nonneg fun j _ => mul_nonneg hCN0 (hS j)))
          (mul_nonneg (add_nonneg hnC hkJ) (inv_nonneg.mpr h9.le))
    _ = (nC + kJ) * ((D ^ 999)⁻¹ * D ^ 5) * ∏ j, S j := by ring
    _ ≤ (nC + kJ) * (D ^ 100)⁻¹ * ∏ j, S j := by gcongr

/-- The arithmetic of a tuple with a reference (blueprint `eq:core-numerical`): from
`Λ ≤ E₁ + (F T + E₃)` with `E₁ ≤ A₁ u P`, `T ≤ P_a + 31 u P`, `E₃ ≤ A₃ u P` and `0 ≤ F ≤ C₀`, the
form is at most the principal quantity `F P_a` plus `(A₁ + 31 C₀ + A₃) u P`. -/
theorem four_err_combine {Λ E1 Fk T E3 Pa P u C0 A1 A3 : ℝ}
    (hkey : Λ ≤ E1 + (Fk * T + E3)) (hE1 : E1 ≤ A1 * u * P) (hT : T ≤ Pa + 31 * u * P)
    (hE3 : E3 ≤ A3 * u * P) (hF0 : 0 ≤ Fk) (hFC : Fk ≤ C0) (hu0 : 0 ≤ u) (hP0 : 0 ≤ P) :
    Λ ≤ Fk * Pa + (A1 + 31 * C0 + A3) * u * P := by
  have h1 := mul_le_mul_of_nonneg_left hT hF0
  have h2 : Fk * (31 * u * P) ≤ C0 * (31 * u * P) :=
    mul_le_mul_of_nonneg_right hFC (by positivity)
  nlinarith

/-- The absolute constant of the numerical errors of a four-core tuple (blueprint
`eq:core-numerical`): torus-form and gauge errors, truncation parts of the core sizes, coset
replacement and tail errors, and discarded tuples. -/
noncomputable def fourErrC (κ : LocalKernelClass) (J : ℕ) : ℝ :=
  104 * localKernelSupBound κ + 31 * fourKC κ 0 + 2 * fourKC κ 1 +
    (Real.pi * kerC κ 0 + 2 * (2 * 4 * (2 * 4 * (2 * Real.pi * 4 * kernelDerivBound κ 0)))) +
    kerC κ J

namespace ActiveSetup.BasicFamilies.FamParams
variable {κ' : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ' c₀} {bf : A.BasicFamilies}
  {fp : bf.FamParams}

namespace SideInput
variable (D : fp.SideInput)

/-- The schedule facts used for the numerical errors: `T⁻¹/L_{h'} ≤ D_*^{-999}` and
`T/L_{h'} - U₀ ≥ D_*^{999}` for `h' ≤ J_*` (`L_{h'} Ξ ≤ T`, `Ξ = D_*^{1000}`, `U₀ = D_*^{250}`). -/
theorem Tt_far_bounds {Cj CA CT CK : ℕ} {δs W : ℝ} (hV : D.S.Valid Cj CA CT CK δs W)
    (hCT : 4 ≤ CT) (hd2 : 2 ≤ D.S.dmax) (hD : 2 ≤ D.S.Dstar) (hB : 2 ≤ D.S.Bstar)
    (hQ : 1 ≤ D.S.Q0) (hSP : D.SP = D.S.sideParams δs) {h' : ℕ} (hh : h' ≤ D.SP.Jst) :
    D.SP.Tt⁻¹ / ModeSchedule.Lh h' ≤ (D.S.Dstar ^ 999)⁻¹ ∧
      D.S.Dstar ^ 999 ≤ D.SP.Tt / ModeSchedule.Lh h' - D.U0 := by
  have hT := D.Lh_mul_Ξ_le_Tt hV hCT hd2 hD hB hQ hSP hh
  have hD1 : (1 : ℝ) ≤ D.S.Dstar := by linarith
  have hL1 : (1 : ℝ) ≤ ModeSchedule.Lh h' := one_le_pow₀ (by norm_num)
  have hL0 : 0 < ModeSchedule.Lh h' := by linarith
  have hΞ : D.S.Ξ = D.S.Dstar ^ 1000 := rfl
  have h999 : (0 : ℝ) < D.S.Dstar ^ 999 := by positivity
  have hstep : D.S.Dstar ^ 1000 = D.S.Dstar ^ 999 * D.S.Dstar := pow_succ _ _
  have h250 : D.S.Dstar ^ 250 ≤ D.S.Dstar ^ 999 := pow_le_pow_right₀ hD1 (by norm_num)
  have hTL : D.S.Ξ ≤ D.SP.Tt / ModeSchedule.Lh h' := by
    rw [le_div_iff₀ hL0]; linarith [mul_comm (ModeSchedule.Lh h') D.S.Ξ]
  have hΞ1 : D.S.Dstar ^ 999 ≤ D.S.Ξ := by
    rw [hΞ]; exact pow_le_pow_right₀ hD1 (by norm_num)
  have hΞ0 : 0 < D.S.Ξ := by rw [hΞ]; positivity
  have hT0 : 0 < D.SP.Tt := lt_of_lt_of_le (mul_pos hL0 hΞ0) hT
  refine ⟨?_, ?_⟩
  · have hTi : D.SP.Tt⁻¹ ≤ (D.S.Dstar ^ 999)⁻¹ := by
      refine inv_anti₀ h999 ?_
      calc D.S.Dstar ^ 999 ≤ D.S.Ξ := hΞ1
        _ ≤ ModeSchedule.Lh h' * D.S.Ξ := le_mul_of_one_le_left (by linarith) hL1
        _ ≤ D.SP.Tt := hT
    calc D.SP.Tt⁻¹ / ModeSchedule.Lh h' ≤ D.SP.Tt⁻¹ :=
          div_le_self (inv_nonneg.mpr hT0.le) hL1
      _ ≤ _ := hTi
  · have hU : D.U0 = D.S.Dstar ^ 250 := rfl
    rw [hU]
    have : D.S.Dstar ^ 999 * 2 ≤ D.S.Dstar ^ 999 * D.S.Dstar :=
      mul_le_mul_of_nonneg_left hD h999.le
    linarith

open Classical in
/-- Blueprint `eq:core-numerical` (lines 2562-2567) for a four-core tuple on a leaf cell of the
side states (common chart of role `0`, torus forms with error `D_*^{-150}`, anchor role good at the
final height `h`; enlarged gauge cutoff `δ/2`, Fourier truncation tails at most `D_*^{-300}` and
full Fourier norms at most `D_*`, as chosen in blueprint line 1944): the cell form of the four
selected subtotals is at most the principal quantity `|WFourier_s(r q', r t')| Π_j a'_j` if the
  tuple
passes the four-core test, and `0` if it is discarded, plus the absolute error
`C_J D_*^{-100} Π_j Σ_{F_j} |α|`. The error collects the torus-form and gauge errors, the truncation
parts of the core sizes (`a'_j ≤ Σ_{F_j} |α|`, `coreSize_le`), the coset replacement and tail errors
(`T⁻¹/L ≤ D_*^{-999}`, `T/L - U₀ ≥ D_*^{999}`), discarded tuples with a reference
(`|WFourier_s| ≤ C₁ U₀⁻¹`, `fourK_discard`) and tuples without reference
  (`four_core_noref_side`). -/
theorem four_core_tuple_bound {Cj CA CT CK : ℕ} {δs W : ℝ} (hV : D.S.Valid Cj CA CT CK δs W)
    (hCA : 1 ≤ CA) (hCT : 4 ≤ CT) (hd2 : 2 ≤ D.S.dmax) (hD : 2 ≤ D.S.Dstar)
    (hB : 2 ≤ D.S.Bstar) (hQ : 1 ≤ D.S.Q0) (hSP : D.SP = D.S.sideParams δs) {I : ℤ × ℤ}
    (hI : I ∈ A.cells) (G : bf.Grp) (hz : ∀ j, (D.Ms j G).zc = (D.Ms 0 G).zc)
    (hdim : (D.Ms 0 G).zc.dim ≤ D.S.dmax) {δ : ℝ} (hδ : 0 < δ) (hδc : ∀ j, (D.Ms j G).δc = δ)
    (hcl : ∀ j, (D.Ms j G).cl = slotCoeff j) (hρ : ∀ j k, (D.Ms j G).ρ k ∈ Set.Icc (0 : ℝ) 1)
    (hQC : ∀ a b, ∃ k : ℤ, (D.S.Q0 : ℝ) * ((D.Ms 0 G).zc.C a b : ℝ) = k) {Cm : ℝ}
    (hCm0 : 0 ≤ Cm) (hCm : ∀ a b, |((D.Ms 0 G).zc.C a b : ℝ)| ≤ Cm)
    {Kt : ℕ} (hQB : (D.S.Q0 : ℝ) * 2 ^ (Kt + 1) ≤ D.S.Bstar)
    (hτc : cutTail (D.Ms 0 G).zc.dim δ Kt ≤ (D.S.Dstar ^ 300)⁻¹)
    (hτm : multTail (D.Ms 0 G).zc.dim (δ / 2) D.S.Q0 Cm Kt ≤ (D.S.Dstar ^ 300)⁻¹)
    (hMN : multNorm (D.Ms 0 G).zc.dim (δ / 2) D.S.Q0 Cm ≤ D.S.Dstar)
    (hCN : cutNorm (D.Ms 0 G).zc.dim δ ≤ D.S.Dstar) {J : ℕ} (hJ : 1 ≤ J) {h : ℕ}
    (hh : h ≤ D.SP.Jst)
    {m₀ : (D.Ms 0 G).alive (ancAt A.G (D.preAt I) (A.blkStart D.S.K I.1 - 4 * D.S.K))}
    (hgood : ((D.Ms 0 G).blockComps D.S D.hA (A.blkStart D.S.K I.1) (D.preAt I)).Good D.SP.Δ
      ((D.Ms 0 G).goodP D.S D.SP (A.blkStart D.S.K I.1)) h m₀)
    (Fsel : ∀ j, Finset ((D.Ms j G).alive (ancAt A.G (D.preAt I)
      (A.blkStart D.S.K I.1 - 4 * D.S.K))))
    (n : ∀ j, (D.Ms j G).alive (ancAt A.G (D.preAt I) (A.blkStart D.S.K I.1 - 4 * D.S.K)) →
      Fin (D.Ms j G).zc.dim → ℤ)
    (hn : ∀ j, ∀ x ∈ Fsel j, ∀ i, |(n j x i : ℝ)| ≤ D.S.Dstar * D.S.Eh (h - D.SP.Δ))
    (a : ∀ j, (D.Ms j G).alive (ancAt A.G (D.preAt I) (A.blkStart D.S.K I.1 - 4 * D.S.K)))
    {xs : ℝ} (hxs : xs ∈ dyadicGridCell A.G I.1 I.2)
    (hform : ∀ j, ∀ y ∈ dyadicGridCell A.G I.1 I.2,
      ‖∑ x ∈ Fsel j, D.c j G (A.blkStart D.S.K I.1) (D.preAt I) x.1 * (D.Ms j G).wave x.1 y -
        (Real.fourierChar (((D.Ms j G).cl : ℝ) * centerPhase (D.Ms j G).zc (D.Ms j G).ρ y) : ℂ) *
          (Real.fourierChar ((D.Ms j G).slope (a j).1 xs * (y - xs)) : ℂ) *
          (D.Ms j G).torusG D.S (h - D.SP.Δ) xs (Fsel j)
            (fun x => D.c j G (A.blkStart D.S.K I.1) (D.preAt I) x.1) (n j)
            (fun i => (D.Ms j G).torusξ D.S (h - D.SP.Δ) i * (y - xs))‖ ≤
        (D.S.Dstar ^ 150)⁻¹ * D.coefSum G I j (Fsel j)) :
    ‖fp.Λc I (fun j => D.compSub j G I ((Fsel j).map ⟨Subtype.val, Subtype.val_injective⟩))‖ ≤
      (if D.fourPasses G I xs (h - D.SP.Δ) a then
        ‖fourK (dyadicGridLeft A.G I.1 I.2) (dyadicGridLength A.G I.1) (A.w I) xs
          (D.fourQ' G I xs (h - D.SP.Δ) a) (D.fourT' G I xs (h - D.SP.Δ) a)‖ *
          ∏ j, D.coreSize G I xs (h - D.SP.Δ) j (Fsel j) (n j)
      else 0) +
      fourErrC κ' J * (D.S.Dstar ^ 100)⁻¹ * ∏ j, D.coefSum G I j (Fsel j) := by
  have hr : 0 < dyadicGridLength A.G I.1 := dyadicGridLength_pos A.G I.1
  have hw := A.adm I hI
  have hDp : 0 < D.S.Dstar := by linarith
  have hD1 : (1 : ℝ) ≤ D.S.Dstar := by linarith
  have hh' : h - D.SP.Δ ≤ D.SP.Jst := le_trans (Nat.sub_le _ _) hh
  have hu0 : (0 : ℝ) ≤ (D.S.Dstar ^ 100)⁻¹ := by positivity
  have hu1 : (D.S.Dstar ^ 100)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ hD1)
  have hpow : ∀ k : ℕ, 100 ≤ k → (D.S.Dstar ^ k)⁻¹ ≤ (D.S.Dstar ^ 100)⁻¹ := fun k hk =>
    inv_anti₀ (by positivity) (pow_le_pow_right₀ hD1 hk)
  have hK := localKernelSupBound_nonneg κ'
  have hC0 : 0 ≤ fourKC κ' 0 := by
    have := kernelDerivBound_nonneg κ' 0
    unfold fourKC; positivity
  have hC1 : 0 ≤ fourKC κ' 1 := by
    have := kernelDerivBound_nonneg κ' 0
    have := kernelDerivBound_nonneg κ' 1
    unfold fourKC; positivity
  have hnC : 0 ≤ Real.pi * kerC κ' 0 + 2 * (2 * 4 * (2 * 4 * (2 * Real.pi * 4 *
      kernelDerivBound κ' 0))) := by
    have := kerC_nonneg hr hw 0
    have := kernelDerivBound_nonneg κ' 0
    positivity
  have hkJ := kerC_nonneg hr hw J
  have hδ2 : 0 < δ / 2 := half_pos hδ
  have hτc0 := cutTail_nonneg (D.Ms 0 G).zc.dim hδ Kt
  have hτm0 : 0 ≤ multTail (D.Ms 0 G).zc.dim (δ / 2) D.S.Q0 Cm Kt := by
    unfold multTail
    have := profR_nonneg hδ2 ((D.Ms 0 G).zc.dim + (D.Ms 0 G).zc.dim + 1)
    positivity
  have hCN0 : 0 ≤ cutNorm (D.Ms 0 G).zc.dim δ := by
    unfold cutNorm; have := one_le_bumpConst; positivity
  have hMN0 : 0 ≤ multNorm (D.Ms 0 G).zc.dim (δ / 2) D.S.Q0 Cm := by
    unfold multNorm; have := profR_nonneg hδ2 ((D.Ms 0 G).zc.dim + (D.Ms 0 G).zc.dim + 1)
    positivity
  have hS0 : ∀ j, 0 ≤ D.coefSum G I j (Fsel j) := fun j => D.coefSum_nonneg G I j (Fsel j)
  have hP0 : 0 ≤ ∏ j, D.coefSum G I j (Fsel j) := Finset.prod_nonneg fun j _ => hS0 j
  have hU0u : D.U0⁻¹ ≤ (D.S.Dstar ^ 100)⁻¹ := by unfold U0; exact hpow 250 (by norm_num)
  have hfourErr : fourErrC κ' J = 104 * localKernelSupBound κ' + 31 * fourKC κ' 0 +
      2 * fourKC κ' 1 + (Real.pi * kerC κ' 0 + 2 * (2 * 4 * (2 * 4 * (2 * Real.pi * 4 *
        kernelDerivBound κ' 0)))) + kerC κ' J := rfl
  have hE1 := gauge_err_le (K := localKernelSupBound κ') (δ := δ)
    (P := ∏ j, D.coefSum G I j (Fsel j)) (D.Ms 0 G).zc.dim hD1 hK hP0 hτc0 hτm0 hτc hτm
  have h1P : 0 ≤ fourKC κ' 1 * (D.S.Dstar ^ 100)⁻¹ * ∏ j, D.coefSum G I j (Fsel j) := by
    positivity
  by_cases hne : (D.fourRefSet G I xs (h - D.SP.Δ) a).Nonempty
  · have key := D.four_core_test hV hCA hCT hd2 hD hB hQ hSP hI G hz hdim hδ hδc hcl hρ hQC
      hCm0 hCm hδ2 hQB J hh hgood Fsel n hn a hxs hform hne
    have hT := trunc_core_err (a := fun j => D.coreSize G I xs (h - D.SP.Δ) j (Fsel j) (n j))
      (S := fun j => D.coefSum G I j (Fsel j)) (fun j => D.coreSize_nonneg G I xs _ j _ _)
      (fun j => D.coreSize_le G I xs _ j (by rw [hδc j]; exact hδ) (Fsel j) (n j)) hτc0 hτm0
      (hτc.trans (hpow 300 (by norm_num))) (hτm.trans (hpow 300 (by norm_num))) hu1
    have hTb := D.Tt_far_bounds hV hCT hd2 hD hB hQ hSP hh'
    have hE3 := coset_err_le (S := fun j => D.coefSum G I j (Fsel j)) hJ hD1 hnC hkJ hS0 hMN0
      hMN hCN0 hCN hTb.1 hTb.2
    have hcomb := four_err_combine key hE1 hT hE3 (norm_nonneg _) (fourK_le_fourKC hr hw _ _ _)
      hu0 hP0
    beta_reduce at hcomb
    by_cases hpass : D.fourPasses G I xs (h - D.SP.Δ) a
    · simp only [hpass, ↓reduceIte]
      rw [hfourErr]
      refine hcomb.trans ?_
      linarith only [h1P]
    · simp only [hpass, ↓reduceIte, zero_add]
      rw [hfourErr]
      have hinner : fourInner (dyadicGridLength A.G I.1) (D.fourQ' G I xs (h - D.SP.Δ) a)
          (D.fourT' G I xs (h - D.SP.Δ) a) < D.U0⁻¹ := by
        by_contra hc
        exact hpass ⟨hne, not_lt.mp hc⟩
      have hFd : ‖fourK (dyadicGridLeft A.G I.1 I.2) (dyadicGridLength A.G I.1) (A.w I) xs
          (D.fourQ' G I xs (h - D.SP.Δ) a) (D.fourT' G I xs (h - D.SP.Δ) a)‖ ≤
          fourKC κ' 1 * (D.S.Dstar ^ 100)⁻¹ :=
        (fourK_discard hr hw le_rfl xs _ _ (by unfold U0; positivity)
          (Or.inl ((fourMu_le_inner _ _ _).trans hinner.le))).trans
          (mul_le_mul_of_nonneg_left hU0u hC1)
      have hPa0 : 0 ≤ ∏ j, D.coreSize G I xs (h - D.SP.Δ) j (Fsel j) (n j) :=
        Finset.prod_nonneg fun j _ => D.coreSize_nonneg G I xs _ j _ _
      have hPaP : ∏ j, D.coreSize G I xs (h - D.SP.Δ) j (Fsel j) (n j) ≤
          ∏ j, D.coefSum G I j (Fsel j) :=
        Finset.prod_le_prod₀ (fun j _ => D.coreSize_nonneg G I xs _ j _ _)
          fun j _ => D.coreSize_le G I xs _ j (by rw [hδc j]; exact hδ) (Fsel j) (n j)
      have h2 := mul_le_mul hFd hPaP hPa0 (mul_nonneg hC1 hu0)
      refine hcomb.trans ?_
      linarith only [h1P, h2]
  · have hnoref : D.fourRefSet G I xs (h - D.SP.Δ) a = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hne
    have key := D.four_core_noref_side hV hCA hd2 hD hB hQ hI G hz hδ hδc hcl hρ hQC hCm0 hCm
      hδ2 hQB (h - D.SP.Δ) Fsel n hn a xs hform hnoref
    have hpass : ¬ D.fourPasses G I xs (h - D.SP.Δ) a := fun hp => hne hp.1
    simp only [hpass, ↓reduceIte, zero_add]
    rw [hfourErr]
    have hNP := norm_prod_le_pow hS0 hMN hCN0 hCN
    have h250 := inv_pow_mul_pow5_le hD1 (k := 250) (by norm_num)
    have h2 : fourKC κ' 1 * D.U0⁻¹ * (multNorm (D.Ms 0 G).zc.dim (δ / 2) D.S.Q0 Cm *
        ∏ j, (cutNorm (D.Ms 0 G).zc.dim δ * D.coefSum G I j (Fsel j))) ≤
        fourKC κ' 1 * (D.S.Dstar ^ 100)⁻¹ * ∏ j, D.coefSum G I j (Fsel j) := by
      have hU : D.U0⁻¹ = (D.S.Dstar ^ 250)⁻¹ := rfl
      calc _ ≤ fourKC κ' 1 * D.U0⁻¹ * (D.S.Dstar ^ 5 * ∏ j, D.coefSum G I j (Fsel j)) :=
            mul_le_mul_of_nonneg_left hNP (mul_nonneg hC1 (inv_nonneg.mpr (by
              unfold U0; positivity)))
        _ = fourKC κ' 1 * (D.U0⁻¹ * D.S.Dstar ^ 5) * ∏ j, D.coefSum G I j (Fsel j) := by ring
        _ ≤ _ := by rw [hU]; gcongr
    have h3 : 0 ≤ (31 * fourKC κ' 0 + (Real.pi * kerC κ' 0 + 2 * (2 * 4 * (2 * 4 *
        (2 * Real.pi * 4 * kernelDerivBound κ' 0)))) + kerC κ' J) * (D.S.Dstar ^ 100)⁻¹ *
        ∏ j, D.coefSum G I j (Fsel j) := by positivity
    refine key.trans ?_
    linarith only [hE1, h1P, h2, h3]

end SideInput

end ActiveSetup.BasicFamilies.FamParams

/-- The constant of the anchor entries `entryC` without the band factor `μ ν^{-J}`. -/
noncomputable def entryCU (κ : LocalKernelClass) (J A : ℕ) : ℝ :=
  kerC κ (J + (A + 2)) * (3 + 2) ^ (J + (A + 2)) * 2 ^ (A + 2)

theorem entryCU_nonneg {κ : LocalKernelClass} {a₀ r : ℝ} (hr : 0 < r) {w : ℝ × ℝ → ℂ}
    (hw : IsAdmissibleLocalKernel κ a₀ r w) (J A : ℕ) : 0 ≤ entryCU κ J A := by
  unfold entryCU
  have := kerC_nonneg hr hw (J + (A + 2))
  positivity

/-- The anchor entry constant `C_{J,A} μ ν^{-J}` is at most `C_{J,A} min(1, |β|)` (a discarded
three-core tuple with `|β| < U₀⁻¹`). -/
theorem entryC_le_min {κ : LocalKernelClass} {a₀ r : ℝ} (hr : 0 < r) {w : ℝ × ℝ → ℂ}
    (hw : IsAdmissibleLocalKernel κ a₀ r w) (J A : ℕ) (b : ℝ) :
    entryC κ J A b ≤ entryCU κ J A * min 1 |b| := by
  unfold entryC entryCU
  have := kerC_nonneg hr hw (J + (A + 2))
  have h1 : 0 ≤ min 1 |b| := le_min zero_le_one (abs_nonneg _)
  have h2 : 1 ≤ max 1 |b| ^ J := one_le_pow₀ (le_max_left _ _)
  have h3 : (max 1 |b| ^ J)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h2
  have h4 : 0 ≤ (max 1 |b| ^ J)⁻¹ := inv_nonneg.mpr (by linarith)
  rw [div_eq_mul_inv]
  calc kerC κ (J + (A + 2)) * (3 + 2) ^ (J + (A + 2)) * min 1 |b| * (max 1 |b| ^ J)⁻¹ *
        2 ^ (A + 2) ≤ kerC κ (J + (A + 2)) * (3 + 2) ^ (J + (A + 2)) * min 1 |b| * 1 *
        2 ^ (A + 2) := by gcongr
    _ = _ := by ring

/-- The anchor entry constant `C_{J,A} μ ν^{-J}` is at most `C_{J,A} U^{-J}` when `|β| ≥ U ≥ 1`
(all anchored frequencies far: a three-core tuple without reference). -/
theorem entryC_le_far {κ : LocalKernelClass} {a₀ r : ℝ} (hr : 0 < r) {w : ℝ × ℝ → ℂ}
    (hw : IsAdmissibleLocalKernel κ a₀ r w) (J A : ℕ) {b U : ℝ} (hU : 1 ≤ U) (hb : U ≤ |b|) :
    entryC κ J A b ≤ entryCU κ J A * (U ^ J)⁻¹ := by
  unfold entryC entryCU
  have := kerC_nonneg hr hw (J + (A + 2))
  have h1 : min 1 |b| ≤ 1 := min_le_left _ _
  have h1' : 0 ≤ min 1 |b| := le_min zero_le_one (abs_nonneg _)
  have hUJ : 0 < U ^ J := pow_pos (by linarith) _
  have h2 : U ^ J ≤ max 1 |b| ^ J := pow_le_pow_left₀ (by linarith) (hb.trans (le_max_right _ _)) J
  have h3 : (max 1 |b| ^ J)⁻¹ ≤ (U ^ J)⁻¹ := inv_anti₀ hUJ h2
  have h4 : 0 ≤ (max 1 |b| ^ J)⁻¹ := inv_nonneg.mpr (hUJ.le.trans h2)
  rw [div_eq_mul_inv]
  calc kerC κ (J + (A + 2)) * (3 + 2) ^ (J + (A + 2)) * min 1 |b| * (max 1 |b| ^ J)⁻¹ *
        2 ^ (A + 2) ≤ kerC κ (J + (A + 2)) * (3 + 2) ^ (J + (A + 2)) * 1 * (U ^ J)⁻¹ *
        2 ^ (A + 2) := by gcongr
    _ = _ := by ring

open Classical in
/-- Blueprint lines 2540 and 2562-2567 (a three-core tuple without reference is discarded) with the
Fourier truncations made explicit: if every anchored expansion frequency is far,
`r |T_l + (P₂ - l P₁)·ξ| ≥ U ≥ 4`, the averaged three-core bound (`three_core_averaged_of`, with no
near coset) gives the form at most twice the torus-form and gauge errors, plus
`4 r⁻¹ C_{J,A} U^{-J} 2^{A+4} W Π_{j ≠ l} ‖g_j‖₂ (r ∫_I |f_l|²)^{1/2}`, plus the far-coset tails
`multNorm Π_j (cutNorm Σ|c|) r⁻¹ ∫_I |f_l| 12 C_J (4/U)^{J-2}`. -/
theorem three_core_noref_of {κ : LocalKernelClass} {a₀ r : ℝ} (hr : 0 < r) {w : ℝ × ℝ → ℂ}
    (hw : IsAdmissibleLocalKernel κ a₀ r w) (z : ChartTag) {δ δ'' : ℝ}
    (hδ : 0 < δ) (hδ'' : 0 < δ'') (hdδ : 8 * z.dim * δ ≤ 1) (hδ8 : δ ≤ 1 / 8)
    (ρc : Fin 4 → Fin z.dim → ℝ) (hρc : ∀ j a, ρc j a ∈ Set.Icc (0 : ℝ) 1) {Q0 : ℕ}
    (hQ0 : 0 < Q0) (hQ : ∀ a b, ∃ k : ℤ, (Q0 : ℝ) * (z.C a b : ℝ) = k) {Cm : ℝ} (hCm0 : 0 ≤ Cm)
    (hCm : ∀ a b, |(z.C a b : ℝ)| ≤ Cm) {L : ℕ} (hL : 0 < L) (Kt : ℕ) {xs : ℝ}
    (hxs : xs ∈ Set.Icc a₀ (a₀ + r)) (l : Fin 4) (γ : Fin 4 → ℝ) (hγl : γ l = 0)
    {ι : Fin 4 → Type*} (F : ∀ j, Finset (ι j)) (c : ∀ j, ι j → ℂ) (n : ∀ j, ι j → Fin z.dim → ℤ)
    {k₀ : ι l} (hFl : F l = {k₀}) (hcl : c l k₀ = 1) (hnl : n l k₀ = 0) (f : Fin 4 → ℝ → ℂ)
    (hgm : Measurable (f l)) (hL2 : MemLp (f l) 2 (volume.restrict (Set.Ioc a₀ (a₀ + r))))
    (hfi : Integrable (fun zz : ℝ × ℝ => w zz * ∏ j, f j (realProgressionCoordinate j zz)))
    (hfiρ : ∀ ρ' : Fin z.dim → ℝ, Integrable (fun zz : ℝ × ℝ => w zz * ∏ j, Function.update f l
      (fun y => (centerCut z δ ρ' y : ℂ) * f l y) j (realProgressionCoordinate j zz)))
    {η : ℝ} (hη : 0 ≤ η)
    (hfa : ∀ j, j ≠ l → ∀ y ∈ Set.Icc a₀ (a₀ + r), ‖f j y - ((centerCut z δ (ρc j) y : ℂ) *
      (Real.fourierChar (((slotCoeff j : ℤ) : ℝ) * centerPhase z (ρc j) y) : ℂ)) *
        ((Real.fourierChar (γ j * (y - xs)) : ℂ) * ∑ k ∈ F j, c j k *
          torusCharacter (n j k) (torusMk fun i => z.θ i / (Q0 * L) * (y - xs)))‖ ≤
            η * ∑ k ∈ F j, ‖c j k‖)
    (hfb : ∀ j, j ≠ l → ∀ y ∈ Set.Icc a₀ (a₀ + r), ‖f j y‖ ≤ ∑ k ∈ F j, ‖c j k‖)
    (cc0 : Fin 4 → (Fin z.dim → ℤ) → ℂ) (hcc0 : ∀ j v, ‖cc0 j v‖ ≤ 1)
    (hccN : ∀ j (s : Finset (Fin z.dim → ℤ)), ∑ v ∈ s, ‖cc0 j v‖ ≤ cutNorm z.dim δ)
    (hccT : ∀ j, j ≠ l → ∀ w, ‖cutoffP δ (ρc j) w - ∑ v ∈ frequencyBox z.dim (2 ^ (Kt + 1)),
      cc0 j v * (Real.fourierChar (∑ i, (v i : ℝ) * w i) : ℂ)‖ ≤ cutTail z.dim δ Kt)
    {U : ℝ} (hU4 : 4 ≤ U)
    (hfarall : ∀ x ∈ frequencyBox (z.dim + z.dim) (2 ^ (Kt + 1)) ×ˢ Fintype.piFinset
        (fun j => frequencyBox z.dim (2 ^ (Kt + 1)) ×ˢ F j),
      U ≤ |r * ((∑ j : Fin 4, ((j : ℕ) : ℝ) * γ j + ∑ i, (expP2 L (Q0 * L) n x i : ℝ) *
            (z.θ i / (Q0 * L))) - ((l : ℕ) : ℝ) * (∑ j, γ j + ∑ i,
              (expP1 L (Q0 * L) n x i : ℝ) * (z.θ i / (Q0 * L))))|)
    {J : ℕ} (hJ : 2 ≤ J) (A : ℕ) (hA : 1 ≤ A) :
    ‖localProgressionForm r w f‖ ≤ 2 * (
      2 * localKernelSupBound κ * ((4 * η + (gaugeErr z.dim δ δ'' +
          4 * (1 + cutTail z.dim δ Kt) ^ 3 * cutTail z.dim δ Kt +
          (1 + cutTail z.dim δ Kt) ^ 4 * multTail z.dim δ'' Q0 Cm Kt)) *
        ∏ j, ∑ k ∈ F j, ‖c j k‖) * (r⁻¹ * ∫ y in Set.Icc a₀ (a₀ + r), ‖f l y‖) +
      4 * (r⁻¹ * (entryCU κ J A * (U ^ J)⁻¹) * 2 ^ (A + 4) *
          (((1 + multTail z.dim δ'' Q0 Cm Kt) * (1 + cutTail z.dim δ Kt) *
            ∏ i ∈ Finset.univ.erase l, (eLpNorm (fun u : torusAnnihilator
              (rationalIntegerIntersection (⊥ : Submodule ℚ (Fin z.dim → ℚ))) =>
                coreG (Q0 * L) (2 ^ (Kt + 1)) F c n
                (fun j v => cc0 j v * (Real.fourierChar (∑ i, (v i : ℝ) * (z.θ i * xs)) : ℂ))
                i u) 2
            (torusAnnihilatorHaar (rationalIntegerIntersection
              (⊥ : Submodule ℚ (Fin z.dim → ℚ))))).toReal) *
            Real.sqrt (r * ∫ y in a₀..a₀ + r, ‖f l y‖ ^ 2))) +
      (multNorm z.dim δ'' Q0 Cm * ∏ j, (cutNorm z.dim δ * ∑ k ∈ F j, ‖c j k‖)) *
        (r⁻¹ * (∫ y in Set.Ico a₀ (a₀ + r), ‖f l y‖) *
          (12 * (kerC κ J * (4 / U) ^ (J - 2))))) := by
  set! T := ∑ j : Fin 4, ((j : ℕ) : ℝ) * γ j - ((l : ℕ) : ℝ) * ∑ j, γ j with hTdef
  set! β₀ : ℝ := if U ≤ |r * T| then T else U / r with hβ₀
  have hβ₀U : U ≤ |r * β₀| := by
    rw [hβ₀]
    split_ifs with hT
    · exact hT
    · rw [mul_div_cancel₀ _ hr.ne', abs_of_pos (by linarith)]
  have hbot : ∀ v : Fin z.dim → ℤ,
      v ∈ rationalIntegerIntersection (⊥ : Submodule ℚ (Fin z.dim → ℚ)) → v = 0 := by
    intro v hv
    have h0 : integerRationalMap z.dim v = 0 := (Submodule.mem_bot ℚ).mp hv
    funext i
    have := congrFun h0 i
    simp only [integerRationalMap, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply,
      Int.cast_eq_zero] at this
    exact this
  -- the coset data: no near coset in positive dimension; one constant coset in dimension zero
  obtain ⟨m₀, N, nref, αN, hN, hsep, hnear, hfar⟩ : ∃ (m₀ : Fin z.dim → ℤ)
      (N : Finset (Fin z.dim → ℤ))
      (nref : ((Fin (z.dim + z.dim) → ℤ) × ∀ j, (Fin z.dim → ℤ) × ι j) → Fin z.dim → ℤ)
      (αN : (Fin z.dim → ℤ) → ℝ),
      (∀ n ∈ N, ∀ n' ∈ N, n ≠ n' → n - n' ∉ rationalIntegerIntersection
        (⊥ : Submodule ℚ (Fin z.dim → ℚ))) ∧
      (∀ n ∈ N, ∀ n' ∈ N, n ≠ n' → 1 ≤ |-(r * αN n) - -(r * αN n')|) ∧
      (∀ x ∈ frequencyBox (z.dim + z.dim) (2 ^ (Kt + 1)) ×ˢ Fintype.piFinset
          (fun j => frequencyBox z.dim (2 ^ (Kt + 1)) ×ˢ F j),
        expP2 L (Q0 * L) n x - ((l : ℕ) : ℤ) • expP1 L (Q0 * L) n x - m₀ ∈
          rationalIntegerIntersection ⊥ →
        nref x ∈ N ∧ expP1 L (Q0 * L) n x - nref x ∈ rationalIntegerIntersection ⊥ ∧
          |r * (∑ j, γ j + ∑ i, (expP1 L (Q0 * L) n x i : ℝ) * (z.θ i / (Q0 * L))) -
            r * αN (nref x)| ≤ 0 ∧
          |r * ((∑ j : Fin 4, ((j : ℕ) : ℝ) * γ j + ∑ i, (expP2 L (Q0 * L) n x i : ℝ) *
              (z.θ i / (Q0 * L))) - ((l : ℕ) : ℝ) * (∑ j, γ j + ∑ i,
                (expP1 L (Q0 * L) n x i : ℝ) * (z.θ i / (Q0 * L)))) - r * β₀| ≤ 0) ∧
      (∀ x ∈ frequencyBox (z.dim + z.dim) (2 ^ (Kt + 1)) ×ˢ Fintype.piFinset
          (fun j => frequencyBox z.dim (2 ^ (Kt + 1)) ×ˢ F j),
        expP2 L (Q0 * L) n x - ((l : ℕ) : ℤ) • expP1 L (Q0 * L) n x - m₀ ∉
          rationalIntegerIntersection ⊥ →
        U ≤ |r * ((∑ j : Fin 4, ((j : ℕ) : ℝ) * γ j + ∑ i, (expP2 L (Q0 * L) n x i : ℝ) *
              (z.θ i / (Q0 * L))) - ((l : ℕ) : ℝ) * (∑ j, γ j + ∑ i,
                (expP1 L (Q0 * L) n x i : ℝ) * (z.θ i / (Q0 * L))))|) := by
    rcases Nat.eq_zero_or_pos z.dim with hd0 | hd
    · have : IsEmpty (Fin z.dim) := by rw [hd0]; infer_instance
      have hall : ∀ v : Fin z.dim → ℤ, v ∈ rationalIntegerIntersection
          (⊥ : Submodule ℚ (Fin z.dim → ℚ)) := fun v => by
        rw [Subsingleton.elim v 0]; exact Submodule.zero_mem _
      refine ⟨0, {0}, fun _ => 0, fun _ => ∑ j, γ j, fun n hn n' hn' hne => ?_,
        fun n hn n' hn' hne => ?_, fun x hx _ => ?_, fun x _ hm => absurd (hall _) hm⟩
      · exact absurd ((Finset.mem_singleton.mp hn).trans (Finset.mem_singleton.mp hn').symm) hne
      · exact absurd ((Finset.mem_singleton.mp hn).trans (Finset.mem_singleton.mp hn').symm) hne
      · have hT : U ≤ |r * T| := by
          have := hfarall x hx
          simpa [Finset.univ_eq_empty, hTdef] using this
        have hβ : β₀ = T := by rw [hβ₀]; simp only [hT, ↓reduceIte]
        refine ⟨Finset.mem_singleton_self _, hall _, ?_, ?_⟩
        · simp [Finset.univ_eq_empty]
        · rw [hβ]
          simp [Finset.univ_eq_empty, hTdef]
    · have : Nonempty (Fin z.dim) := ⟨⟨0, hd⟩⟩
      obtain ⟨m₀, hm₀⟩ := Infinite.exists_notMem_finset ((frequencyBox (z.dim + z.dim)
        (2 ^ (Kt + 1)) ×ˢ Fintype.piFinset
          (fun j => frequencyBox z.dim (2 ^ (Kt + 1)) ×ˢ F j)).image fun x =>
        expP2 L (Q0 * L) n x - ((l : ℕ) : ℤ) • expP1 L (Q0 * L) n x)
      refine ⟨m₀, ∅, fun _ => 0, fun _ => 0, by simp, by simp,
        fun x hx hmem => absurd (Finset.mem_image.mpr ⟨x, hx, (sub_eq_zero.mp (hbot _ hmem))⟩)
          hm₀, fun x hx _ => hfarall x hx⟩
  have key := three_core_averaged_of hr hw z hδ hδ'' hdδ hδ8 ρc hρc hQ0 hQ hCm0 hCm hL Kt hxs
    l γ hγl F c n hFl hcl hnl f hgm hL2 hfi hfiρ hη hfa hfb cc0 hcc0 hccN hccT ⊥ m₀ N hN αN β₀
    hsep nref le_rfl hU4 hnear hfar hJ A 0 hA
  -- the window and the shells above it are bounded by the energy of the side
  have hI2 : 0 ≤ ∫ y in a₀..a₀ + r, ‖f l y‖ ^ 2 :=
    intervalIntegral.integral_nonneg (by linarith only [hr]) fun _ _ => by positivity
  have hwin : ∀ K : Finset ℤ, Real.sqrt (∫ ρ', sideWinE z l (f l) a₀ r K ρ'
      ∂offsetMeasure z.dim) ≤ Real.sqrt (r * ∫ y in a₀..a₀ + r, ‖f l y‖ ^ 2) := fun K => by
    refine Real.sqrt_le_sqrt ?_
    have hb := (window_energy_integrable z l hgm hr hL2 K).2
    calc ∫ ρ', sideWinE z l (f l) a₀ r K ρ' ∂offsetMeasure z.dim ≤
          ∫ _ρ', (r * ∫ y in a₀..a₀ + r, ‖f l y‖ ^ 2) ∂offsetMeasure z.dim :=
          integral_mono (window_energy_integrable z l hgm hr hL2 K).1 (integrable_const _)
            fun ρ' => hb ρ'
      _ = r * ∫ y in a₀..a₀ + r, ‖f l y‖ ^ 2 := by simp
  have heC := entryC_le_far hr hw J A (b := r * β₀) (by linarith only [hU4]) hβ₀U
  have heC0 := entryC_nonneg hr hw J A (r * β₀)
  have hnear0 : nearB κ 0 = 0 := by simp [nearB]
  rw [hnear0, zero_add] at key
  simp only [Finset.range_one, Finset.sum_singleton, pow_zero, inv_one, one_pow, mul_one,
    zero_add, pow_one] at key
  refine key.trans (mul_le_mul_of_nonneg_left ?_ (by norm_num))
  set Qt := (1 + multTail z.dim δ'' Q0 Cm Kt) * (1 + cutTail z.dim δ Kt) *
    ∏ i ∈ Finset.univ.erase l, (eLpNorm (fun u : torusAnnihilator
      (rationalIntegerIntersection (⊥ : Submodule ℚ (Fin z.dim → ℚ))) =>
                coreG (Q0 * L) (2 ^ (Kt + 1)) F c n
        (fun j v => cc0 j v * (Real.fourierChar (∑ i, (v i : ℝ) * (z.θ i * xs)) : ℂ)) i u) 2
      (torusAnnihilatorHaar (rationalIntegerIntersection
              (⊥ : Submodule ℚ (Fin z.dim → ℚ))))).toReal with hQtdef
  have hτ := cutTail_nonneg z.dim hδ Kt
  have hτm : 0 ≤ multTail z.dim δ'' Q0 Cm Kt := by
    unfold multTail; have := profR_nonneg hδ'' (z.dim + z.dim + 1); positivity
  have hQt0 : 0 ≤ Qt := mul_nonneg (mul_nonneg (by linarith only [hτm]) (by linarith))
    (Finset.prod_nonneg fun _ _ => ENNReal.toReal_nonneg)
  set S2 := Real.sqrt (r * ∫ y in a₀..a₀ + r, ‖f l y‖ ^ 2) with hS2def
  have hS20 : 0 ≤ S2 := Real.sqrt_nonneg _
  have hc0 : 0 ≤ r⁻¹ * (entryCU κ J A * (U ^ J)⁻¹) * 2 ^ (A + 4) := by
    have := entryCU_nonneg hr hw J A
    have : 0 < U ^ J := pow_pos (by linarith) _
    positivity
  have hrC : r⁻¹ * entryC κ J A (r * β₀) ≤ r⁻¹ * (entryCU κ J A * (U ^ J)⁻¹) :=
    mul_le_mul_of_nonneg_left heC (inv_nonneg.mpr hr.le)
  have hhalf : 2 * (2 : ℝ)⁻¹ ^ (A + 1) ≤ 1 := by
    have : (2 : ℝ)⁻¹ ^ (A + 1) ≤ (2 : ℝ)⁻¹ ^ 1 :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    norm_num at this ⊢
    linarith only [this]
  have hT1 : r⁻¹ * entryC κ J A (r * β₀) * 2 ^ (A + 4) * (2 * (2 : ℝ)⁻¹ ^ (A + 1)) *
      (Qt * S2) ≤ r⁻¹ * (entryCU κ J A * (U ^ J)⁻¹) * 2 ^ (A + 4) * (Qt * S2) := by
    have h0 : 0 ≤ r⁻¹ * entryC κ J A (r * β₀) * 2 ^ (A + 4) := by
      have := inv_nonneg.mpr hr.le; positivity
    calc _ ≤ r⁻¹ * entryC κ J A (r * β₀) * 2 ^ (A + 4) * 1 * (Qt * S2) := by gcongr
      _ ≤ _ := by
        rw [mul_one]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hrC (by positivity))
          (mul_nonneg hQt0 hS20)
  have hW1 : r⁻¹ * entryC κ J A (r * β₀) * 2 ^ (A + 4) * Qt *
      Real.sqrt (∫ ρ', sideWinE z l (f l) a₀ r ((windowSet N (fun n => r * αN n) 0).filter
        (fun k : ℤ => ∃ n ∈ N, |(k : ℝ) + -(r * αN n)| ≤ 1)) ρ' ∂offsetMeasure z.dim) ≤
      r⁻¹ * (entryCU κ J A * (U ^ J)⁻¹) * 2 ^ (A + 4) * (Qt * S2) := by
    have h0 : 0 ≤ r⁻¹ * entryC κ J A (r * β₀) * 2 ^ (A + 4) := by
      have := inv_nonneg.mpr hr.le; positivity
    calc _ ≤ r⁻¹ * entryC κ J A (r * β₀) * 2 ^ (A + 4) * Qt * S2 :=
          mul_le_mul_of_nonneg_left (hwin _) (mul_nonneg h0 hQt0)
      _ ≤ _ := by
        rw [mul_assoc _ Qt]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hrC (by positivity))
          (mul_nonneg hQt0 hS20)
  have hfar0 : 0 ≤ (multNorm z.dim δ'' Q0 Cm * ∏ j, (cutNorm z.dim δ * ∑ k ∈ F j, ‖c j k‖)) *
      (r⁻¹ * (∫ y in Set.Ico a₀ (a₀ + r), ‖f l y‖) * (12 * (kerC κ J * (4 / U) ^ (J - 2)))) := by
    have hMN : 0 ≤ multNorm z.dim δ'' Q0 Cm := by
      unfold multNorm; have := profR_nonneg hδ'' (z.dim + z.dim + 1); positivity
    have hCN : 0 ≤ cutNorm z.dim δ := by
      unfold cutNorm; have := one_le_bumpConst; positivity
    have := kerC_nonneg hr hw J
    have : 0 ≤ ∫ y in Set.Ico a₀ (a₀ + r), ‖f l y‖ := integral_nonneg fun _ => norm_nonneg _
    have : 0 ≤ (4 / U) ^ (J - 2) := pow_nonneg (by positivity) _
    have : 0 ≤ ∏ j, (cutNorm z.dim δ * ∑ k ∈ F j, ‖c j k‖) :=
      Finset.prod_nonneg fun j _ => mul_nonneg hCN (Finset.sum_nonneg fun _ _ => norm_nonneg _)
    positivity
  have hE0 : 0 ≤ r⁻¹ * (entryCU κ J A * (U ^ J)⁻¹) * 2 ^ (A + 4) * (Qt * S2) :=
    mul_nonneg hc0 (mul_nonneg hQt0 hS20)
  linarith only [hT1, hW1, hE0]

/-- The constant of the near-coset replacement error: `nearB κ ε ≤ nearBC κ √ε` for `ε ≤ 1`. -/
noncomputable def nearBC (κ : LocalKernelClass) : ℝ :=
  24 * Real.sqrt (2 * 4 * (2 * 4 * (2 * Real.pi * 4 * 5 * kernelDerivBound κ 0))) *
    Real.sqrt (kerC κ 4) + Real.pi * (12 * kerC κ 2)

theorem nearB_le {κ : LocalKernelClass} {a₀ r : ℝ} (hr : 0 < r) {w : ℝ × ℝ → ℂ}
    (hw : IsAdmissibleLocalKernel κ a₀ r w) {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    nearB κ ε ≤ nearBC κ * Real.sqrt ε := by
  unfold nearB nearBC
  have hk0 := kernelDerivBound_nonneg κ 0
  have hk2 := kerC_nonneg hr hw 2
  have hk4 := kerC_nonneg hr hw 4
  have e : 2 * 4 * (2 * 4 * (2 * Real.pi * 4 * (4 * ε + ε) * kernelDerivBound κ 0)) =
      (2 * 4 * (2 * 4 * (2 * Real.pi * 4 * 5 * kernelDerivBound κ 0))) * ε := by ring
  rw [e, Real.sqrt_mul (by positivity)]
  have hs : ε ≤ Real.sqrt ε :=
    calc ε = Real.sqrt (ε ^ 2) := (Real.sqrt_sq hε0).symm
      _ ≤ Real.sqrt ε := Real.sqrt_le_sqrt (by nlinarith)
  have h12 : 0 ≤ Real.pi * (12 * kerC κ 2) := by positivity
  have := mul_le_mul_of_nonneg_left hs h12
  nlinarith only [Real.sqrt_nonneg ε, Real.sqrt_nonneg (kerC κ 4),
    Real.sqrt_nonneg (2 * 4 * (2 * 4 * (2 * Real.pi * 4 * 5 * kernelDerivBound κ 0))), hs, h12]

/-- The truncation parts of three core sizes with the multiplier and side-cutoff factor
`W = (1 + τ_m)(1 + τ_c)` (blueprint `eq:core-numerical`): for `0 ≤ a_j ≤ S_j`, three roles and tails
`τ_c, τ_m ≤ u ≤ 1`, `W Π_{j ∈ s} (a_j + τ_c S_j) ≤ Π_{j ∈ s} a_j + 31 u Π_{j ∈ s} S_j`. -/
theorem trunc_core_err3 {ι : Type*} (s : Finset ι) (hs : s.card = 3) {a S : ι → ℝ}
    {τc τm u : ℝ} (ha0 : ∀ j ∈ s, 0 ≤ a j) (haS : ∀ j ∈ s, a j ≤ S j) (hτc0 : 0 ≤ τc)
    (hτm0 : 0 ≤ τm) (hτc : τc ≤ u) (hτm : τm ≤ u) (hu1 : u ≤ 1) :
    (1 + τm) * (1 + τc) * ∏ j ∈ s, (a j + τc * S j) ≤ ∏ j ∈ s, a j + 31 * u * ∏ j ∈ s, S j := by
  have hprod := prod_add_mul_le s hτc0 ha0 haS
  rw [hs] at hprod
  have hu0 : 0 ≤ u := hτc0.trans hτc
  have hP0 : 0 ≤ ∏ j ∈ s, S j := Finset.prod_nonneg fun j hj => (ha0 j hj).trans (haS j hj)
  have hPa0 : 0 ≤ ∏ j ∈ s, a j := Finset.prod_nonneg ha0
  have hPaP : ∏ j ∈ s, a j ≤ ∏ j ∈ s, S j := Finset.prod_le_prod₀ ha0 haS
  have hτc1 : τc ≤ 1 := hτc.trans hu1
  have hτm1 : τm ≤ 1 := hτm.trans hu1
  have h7 : (1 + τc) ^ 3 - 1 ≤ 7 * τc := by
    have e : (1 + τc) ^ 3 - 1 = τc * (3 + 3 * τc + τc ^ 2) := by ring
    have h2 : τc ^ 2 ≤ 1 := pow_le_one₀ hτc0 hτc1
    have h4 : 3 + 3 * τc + τc ^ 2 ≤ 7 := by linarith
    rw [e]
    calc τc * (3 + 3 * τc + τc ^ 2) ≤ τc * 7 := mul_le_mul_of_nonneg_left h4 hτc0
      _ = 7 * τc := by ring
  have hq : ∏ j ∈ s, (a j + τc * S j) ≤ ∏ j ∈ s, a j + 7 * u * ∏ j ∈ s, S j := by
    refine hprod.trans ?_
    have := mul_le_mul_of_nonneg_right (h7.trans (mul_le_mul_of_nonneg_left hτc
      (by norm_num))) hP0
    linarith
  have hW0 : 0 ≤ (1 + τm) * (1 + τc) := by positivity
  have hW : (1 + τm) * (1 + τc) ≤ 1 + 3 * u := by nlinarith only [hτc0, hτc, hτm, hu1]
  have hW4 : (1 + τm) * (1 + τc) ≤ 4 := by nlinarith only [hτc0, hτc1, hτm1]
  have e1 := mul_le_mul_of_nonneg_left hq hW0
  have e2 : (1 + τm) * (1 + τc) * ∏ j ∈ s, a j ≤ (1 + 3 * u) * ∏ j ∈ s, a j :=
    mul_le_mul_of_nonneg_right hW hPa0
  have e3 : (1 + τm) * (1 + τc) * (7 * u * ∏ j ∈ s, S j) ≤ 4 * (7 * u * ∏ j ∈ s, S j) :=
    mul_le_mul_of_nonneg_right hW4 (by positivity)
  have e4 : 3 * u * ∏ j ∈ s, a j ≤ 3 * u * ∏ j ∈ s, S j :=
    mul_le_mul_of_nonneg_left hPaP (by positivity)
  calc (1 + τm) * (1 + τc) * ∏ j ∈ s, (a j + τc * S j) ≤
        (1 + τm) * (1 + τc) * (∏ j ∈ s, a j + 7 * u * ∏ j ∈ s, S j) := e1
    _ = (1 + τm) * (1 + τc) * ∏ j ∈ s, a j + (1 + τm) * (1 + τc) * (7 * u * ∏ j ∈ s, S j) := by
        ring
    _ ≤ (1 + 3 * u) * ∏ j ∈ s, a j + 4 * (7 * u * ∏ j ∈ s, S j) := add_le_add e2 e3
    _ ≤ ∏ j ∈ s, a j + 31 * u * ∏ j ∈ s, S j := by linarith

/-- `r⁻¹ (r X)^{1/2} = (r⁻¹ X)^{1/2}`: the normalized `L²` size of the side on a cell. -/
theorem inv_mul_sqrt_mul {r X : ℝ} (hr : 0 < r) :
    r⁻¹ * Real.sqrt (r * X) = Real.sqrt (r⁻¹ * X) := by
  have hs : 0 < Real.sqrt r := Real.sqrt_pos.mpr hr
  rw [Real.sqrt_mul hr.le, Real.sqrt_mul (inv_nonneg.mpr hr.le), Real.sqrt_inv]
  have e : r⁻¹ = (Real.sqrt r)⁻¹ * (Real.sqrt r)⁻¹ := by
    rw [← mul_inv, Real.mul_self_sqrt hr.le]
  rw [e]
  field_simp

/-- Cauchy-Schwarz on a cell: the normalized `L¹` norm of a square-integrable side on
`[a, a + r]` (or `[a, a + r)`) is at most its normalized `L²` size `(r⁻¹ ∫ |g|²)^{1/2}`. -/
theorem cell_l1_le_size {a r : ℝ} (hr : 0 < r) {g : ℝ → ℂ}
    (hg : MemLp g 2 (volume.restrict (Set.Ioc a (a + r)))) :
    r⁻¹ * ∫ y in Set.Icc a (a + r), ‖g y‖ ≤
        Real.sqrt (r⁻¹ * ∫ y in a..a + r, ‖g y‖ ^ 2) ∧
      r⁻¹ * ∫ y in Set.Ico a (a + r), ‖g y‖ ≤
        Real.sqrt (r⁻¹ * ∫ y in a..a + r, ‖g y‖ ^ 2) := by
  have hv : volume (Set.Ioc a (a + r)) < ⊤ := measure_Ioc_lt_top
  have hcs := setIntegral_norm_le_sqrt hv hg
  have hvol : volume.real (Set.Ioc a (a + r)) = r := by
    rw [Measure.real, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)]
    ring
  have e2 : ∫ y in Set.Ioc a (a + r), ‖g y‖ ^ 2 = ∫ y in a..a + r, ‖g y‖ ^ 2 :=
    (intervalIntegral.integral_of_le (by linarith)).symm
  rw [hvol, e2] at hcs
  have hX : 0 ≤ ∫ y in a..a + r, ‖g y‖ ^ 2 :=
    intervalIntegral.integral_nonneg (by linarith) fun _ _ => by positivity
  have hb : r⁻¹ * ∫ y in Set.Ioc a (a + r), ‖g y‖ ≤
      Real.sqrt (r⁻¹ * ∫ y in a..a + r, ‖g y‖ ^ 2) := by
    rw [← inv_mul_sqrt_mul hr, Real.sqrt_mul hr.le]
    exact mul_le_mul_of_nonneg_left hcs (inv_nonneg.mpr hr.le)
  refine ⟨?_, ?_⟩
  · rw [integral_Icc_eq_integral_Ioc]; exact hb
  · rw [integral_Ico_eq_integral_Ioc]; exact hb

/-- The `L²(𝓗)` norm of a character polynomial `Σ_{k ∈ F} c_k χ_{n_k}` is at most its absolute
coefficient sum (`𝓗` a probability space). -/
theorem eLpNorm_charSum_le {d : ℕ} (V : Submodule ℚ (Fin d → ℚ)) {ι : Type*} (F : Finset ι)
    (c : ι → ℂ) (n : ι → Fin d → ℤ) :
    (eLpNorm (fun u : torusAnnihilator (rationalIntegerIntersection V) =>
        ∑ k ∈ F, c k * torusCharacter (n k) u) 2
        (torusAnnihilatorHaar (rationalIntegerIntersection V))).toReal ≤ ∑ k ∈ F, ‖c k‖ := by
  have hg : Continuous fun u : torusAnnihilator (rationalIntegerIntersection V) =>
      ∑ k ∈ F, c k * torusCharacter (n k) u :=
    continuous_finsetSum _ fun k _ => continuous_const.mul
      ((continuous_torusCharacter _).comp continuous_subtype_val)
  have h1 := eLpNorm_two_toReal_le_add
    (μ := torusAnnihilatorHaar (rationalIntegerIntersection V)) hg.aestronglyMeasurable
    (aestronglyMeasurable_const (b := (0 : ℂ))) (B := 0)
    (fun _ => by simp) (Finset.sum_nonneg fun _ _ => norm_nonneg _) (fun u => by
      rw [norm_zero, zero_add]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
      rw [norm_mul, norm_torusCharacter, mul_one])
  have e0 : (eLpNorm (fun _ : torusAnnihilator (rationalIntegerIntersection V) => (0 : ℂ)) 2
      (torusAnnihilatorHaar (rationalIntegerIntersection V))).toReal = 0 := by simp
  rw [e0, zero_add] at h1
  exact h1

namespace ActiveSetup.BasicFamilies.FamParams
variable {κ' : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ' c₀} {bf : A.BasicFamilies}
  {fp : bf.FamParams}

namespace SideInput
variable (D : fp.SideInput)



end SideInput
end ActiveSetup.BasicFamilies.FamParams
end TrilinearHT.Auto
end
