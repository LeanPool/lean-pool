/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.LPS.SmoothingOrderedProduct

/-!
# Ordered derivatives of the regularized equation

For smooth fields, every ordered spatial derivative commutes with the
heat, tensor-divergence and pressure-gradient terms in the regularized
momentum equation.
-/

public section

open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

/-- The pointwise regularized momentum equation differentiates to
every ordered spatial word (`eq:lps-regularized-Hm-identity`). -/
theorem lps_regularized_equation_wordDeriv
    (u v q : Vec3 → Vec3) (p : Vec3 → ℝ)
    (hu : ∀ i : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun x => u x i))
    (hv : ∀ j : Fin 3, ContDiff ℝ (⊤ : ℕ∞) (fun x => v x j))
    (hp : ContDiff ℝ (⊤ : ℕ∞) p)
    (hPDE : ∀ (i : Fin 3) (x : Vec3),
      q x i =
        (∑ j : Fin 3,
          spatialDeriv (spatialDeriv (fun y => u y i) j) j x) -
        (∑ j : Fin 3,
          spatialDeriv (fun y => v y j * u y i) j x) -
          spatialDeriv p i x)
    (i : Fin 3) (α : List (Fin 3)) (x : Vec3) :
    wordDeriv α (fun y => q y i) x =
      (∑ j : Fin 3,
        spatialDeriv
          (spatialDeriv (wordDeriv α (fun y => u y i)) j) j x) -
      (∑ j : Fin 3,
        spatialDeriv
          (wordDeriv α (fun y => v y j * u y i)) j x) -
        spatialDeriv (wordDeriv α p) i x := by
  let H : Vec3 → ℝ := fun x =>
    ∑ j : Fin 3, spatialDeriv (spatialDeriv (fun y => u y i) j) j x
  let F : Vec3 → ℝ := fun x =>
    ∑ j : Fin 3, spatialDeriv (fun y => v y j * u y i) j x
  let P : Vec3 → ℝ := spatialDeriv p i
  have hHj (j : Fin 3) : ContDiff ℝ (⊤ : ℕ∞)
      (spatialDeriv (spatialDeriv (fun y => u y i) j) j) := by
    simpa [wordDeriv] using contDiff_wordDeriv (hu i) [j, j]
  have hFj (j : Fin 3) : ContDiff ℝ (⊤ : ℕ∞)
      (spatialDeriv (fun y => v y j * u y i) j) :=
    contDiff_wordDeriv ((hv j).mul (hu i)) [j]
  have hH : ContDiff ℝ (⊤ : ℕ∞) H := by
    exact ContDiff.sum (fun j _ => hHj j)
  have hF : ContDiff ℝ (⊤ : ℕ∞) F := by
    exact ContDiff.sum (fun j _ => hFj j)
  have hP : ContDiff ℝ (⊤ : ℕ∞) P :=
    contDiff_wordDeriv hp [i]
  have hqFun : (fun y : Vec3 => q y i) =
      (fun y => H y - F y - P y) := by
    funext y
    exact hPDE i y
  rw [hqFun, lps_wordDeriv_sub (hH.sub hF) hP α,
    lps_wordDeriv_sub hH hF α]
  have hHword : wordDeriv α H x =
      ∑ j : Fin 3,
        spatialDeriv
          (spatialDeriv (wordDeriv α (fun y => u y i)) j) j x := by
    have hsum := congrFun (localDivCurlSmooth_wordDeriv_sum α hHj) x
    change wordDeriv α H x = _ at hsum
    rw [hsum]
    apply Finset.sum_congr rfl
    intro j _
    have hinner : ContDiff ℝ (⊤ : ℕ∞)
        (spatialDeriv (fun y => u y i) j) :=
      contDiff_wordDeriv (hu i) [j]
    calc
      wordDeriv α
          (spatialDeriv (spatialDeriv (fun y => u y i) j) j) x =
          spatialDeriv
            (wordDeriv α (spatialDeriv (fun y => u y i) j)) j x :=
        congrFun (localDivCurlSmooth_wordDeriv_spatialDeriv hinner α j) x
      _ = spatialDeriv
            (spatialDeriv (wordDeriv α (fun y => u y i)) j) j x := by
        rw [localDivCurlSmooth_wordDeriv_spatialDeriv (hu i) α j]
  have hFword : wordDeriv α F x =
      ∑ j : Fin 3,
        spatialDeriv (wordDeriv α (fun y => v y j * u y i)) j x := by
    have hsum := congrFun (localDivCurlSmooth_wordDeriv_sum α hFj) x
    change wordDeriv α F x = _ at hsum
    rw [hsum]
    apply Finset.sum_congr rfl
    intro j _
    exact congrFun
      (localDivCurlSmooth_wordDeriv_spatialDeriv ((hv j).mul (hu i)) α j) x
  change wordDeriv α H x - wordDeriv α F x - wordDeriv α P x = _
  rw [hHword, hFword]
  rw [show wordDeriv α P x = spatialDeriv (wordDeriv α p) i x from
    congrFun (localDivCurlSmooth_wordDeriv_spatialDeriv hp α i) x]

end ESS
