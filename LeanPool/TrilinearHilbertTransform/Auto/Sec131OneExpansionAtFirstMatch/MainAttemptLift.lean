/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

/- Adapted for Lean Pool from roos-j/lean-trilinearht at
7b4209609e6a7fb9d9935973ee8541495f943660. Imports, names, proof organization and
Mathlib interfaces have been updated; original authorship is retained above. -/

public import LeanPool.TrilinearHilbertTransform.Auto.Sec131OneExpansionAtFirstMatch.ChooseSchedule

/-!
# Trilinear Hilbert transform: mainAttemptLift
-/

@[expose] public section

section
namespace TrilinearHT.Auto
open MeasureTheory Metric
open scoped FourierTransform ComplexConjugate ENNReal
namespace ActiveSetup.BasicFamilies.FamParams

open scoped Classical in
private def MainAttemptLiftConclusion8Statement : Prop :=
  ∀ (κ : LocalKernelClass)
    (c₀ : ℕ)
    (D : ℕ)
    (A : ActiveSetup κ c₀)
    (bf : A.BasicFamilies)
    (fp : bf.FamParams)
    (l : Fin (4 : ℕ))
    (s : List (CatCol bf.Vtx))
    (d : bf.Vtx)
    (cs : Finset (ℤ × ℤ))
    (G : bf.Grp)
    (j : ℕ)
    (z : bf.Vtx)
    (g : ℤ)
    (dB : ℕ)
    (_ : ∀ (w : bf.Vtx), (bf.vtag w).dim ≤ dB)
    (δ : ℝ)
    (ρ : Fin (bf.vtag z).dim → ℝ)
    (H : ℝ)
    (δc : ℝ)
    (N : ℝ)
    (hδcN : δc ^ (2 : ℕ) * N * A.colBudget ^ (2 : ℕ) ≤ (1 : ℝ)),
  let FM : bf.Lab ⊕ Fin fp.Mc → Finset (ℤ × ℤ) :=
    fp.firstCells cs l s G j d
  let X : ℝ :=
    (1 : ℝ) + Real.log (chartTranslationBudget (H ^ (6 : ℕ))) + Real.log ((3 : ℝ) *
      fp.ballEdgeH dB (fp.ballRadius g (fp.bbase j + fp.P)))
  let K : Finset ((_ : bf.Lab ⊕ Fin fp.Mc) × ℤ × ℤ) :=
    Finset.univ.sigma FM
  ∀ (Ny : ↥K → Type)
    (_ : (k : ↥K) → Fintype (Ny k))
    (coef : (k : ↥K) → Ny k → ℂ)
    (lam : ↥K → ℝ)
    (γ : (k : ↥K) → Ny k → ℝ)
    (dv : ↥K → ℕ)
    (θv : (k : ↥K) → Fin (dv k) → ℝ)
    (σ : (k : ↥K) → Ny k → Fin (dv k + (bf.vtag z).dim) → ℚ)
    (β : ↥K → ℝ)
    (_ : ∀ (k : ↥K) (k_1 : Ny k), γ k k_1 = β k + ∑ i : Fin (dv k + (bf.vtag z).dim), (↑(σ k
      k_1 i) : ℝ) * Fin.append (θv k) (bf.vtag z).θ i)
    (_ : ∀ (k : ↥K), dv k ≤ dB),
  let B : ℝ :=
    Real.exp ((↑D : ℝ) * X ^ D)
  ∀ (_ : ∀ (k : ↥K) (k_1 : Ny k) (i : Fin (dv k + (bf.vtag z).dim)), (↑(rationalHeight (σ k
      k_1 i)) : ℝ) ≤ B * ((1 : ℝ) + (4 : ℝ) * ((↑(dv k + (bf.vtag z).dim) : ℝ) + (1 :
      ℝ)) * max (1 : ℝ) ((4 : ℝ) * B / δc)))
    (_ : ∀ (k : ↥K), |lam k| * dyadicGridLength A.G (↑k : (_ : bf.Lab ⊕ Fin fp.Mc) × ℤ ×
      ℤ).snd.1 ^ (2 : ℕ) ≤ B)
    (_ : (0 : ℝ) ≤ B),
  let ζ : ℝ → ℝ :=
    centerCut (bf.vtag z) δ ρ
  let cell : ↥K → Set ℝ :=
    fun (k : ↥K) => dyadicGridCell A.G (↑k : (_ : bf.Lab ⊕ Fin fp.Mc) × ℤ × ℤ).snd.1 (↑k
      : (_ : bf.Lab ⊕ Fin fp.Mc) × ℤ × ℤ).snd.2
  let a₀ : ↥K → ℝ :=
    fun (k : ↥K) => dyadicGridLeft A.G (↑k : (_ : bf.Lab ⊕ Fin fp.Mc) × ℤ × ℤ).snd.1 (↑k
      : (_ : bf.Lab ⊕ Fin fp.Mc) × ℤ × ℤ).snd.2
  let φ : bf.Lab ⊕ Fin fp.Mc → ℝ → ℂ :=
    mainScalar fp.Mc (bf.origCols l) s
  let w : bf.Lab ⊕ Fin fp.Mc → ℝ :=
    mainWeight fp.Mc (bf.origCols l)
  ∀ (hw : ∀ (Φ : bf.Lab ⊕ Fin fp.Mc), (0 : ℝ) < w Φ),
  let ψ : (k : ↥K) × Ny k → ℝ → ℂ :=
    fun (m : (k : ↥K) × Ny k) (y : ℝ) => (↑(ζ y) : ℂ) * (↑((𝐞 : ℝ → Circle)
      ((↑(slotCoeff l) : ℝ) * centerPhase (bf.vtag z) ρ y)) : ℂ) * (↑((𝐞 : ℝ → Circle)
      (lam m.fst * (y - a₀ m.fst) ^ (2 : ℕ) + γ m.fst m.snd * (y - a₀ m.fst))) : ℂ)
  let am : (k : ↥K) × Ny k → ℝ → ℂ :=
    fun (m : (k : ↥K) × Ny k) => (cell m.fst).indicator fun (_ : ℝ) => coef m.fst m.snd
  let E : bf.Lab ⊕ Fin fp.Mc → Set ℝ :=
    fun (Φ : bf.Lab ⊕ Fin fp.Mc) => ⋃ I ∈ FM Φ, dyadicGridCell A.G I.1 I.2
  let sf : ℝ → ℂ :=
    fun (y : ℝ) => (↑(ζ y) : ℂ) ^ (2 : ℕ)
  let qf : bf.Lab ⊕ Fin fp.Mc → ℝ → ℂ :=
    fun (Φ : bf.Lab ⊕ Fin fp.Mc) => (E Φ).indicator fun (y : ℝ) => ∑ m : (k : ↥K) × Ny k
      with (↑m.fst : (_ : bf.Lab ⊕ Fin fp.Mc) × ℤ × ℤ).fst = Φ, am m y * ψ m y - sf y *
      φ Φ y
  ∀ (ham : ∀ (m : (k : ↥K) × Ny k), Measurable (am m))
    (hsfm : Measurable sf)
    (hsf1 : ∀ (y : ℝ), ‖sf y‖ ≤ (1 : ℝ))
    (hqm : ∀ (Φ : bf.Lab ⊕ Fin fp.Mc), Measurable (qf Φ))
    (_ : ∀ (m : (k : ↥K) × Ny k), (↑m.fst : (_ : bf.Lab ⊕ Fin fp.Mc) × ℤ × ℤ).snd ∈ FM
      (↑m.fst : (_ : bf.Lab ⊕ Fin fp.Mc) × ℤ × ℤ).fst)
    (hqle : ∀ (Φ : bf.Lab ⊕ Fin fp.Mc) (y : ℝ), ‖qf Φ y‖ ≤ δc)
    (hqsum : ∀ (y : ℝ), ∑ Φ : bf.Lab ⊕ Fin fp.Mc, ‖qf Φ y‖ ^ (2 : ℕ) / w Φ ≤ δc ^ (2 : ℕ) * N *
      A.colBudget ^ (2 : ℕ)),
  let εM : (k : ↥K) × Ny k → ℝ :=
    fun (m : (k : ↥K) × Ny k) => w (↑m.fst : (_ : bf.Lab ⊕ Fin fp.Mc) × ℤ × ℤ).fst * (∑
      i : Ny m.fst, ‖coef m.fst i‖ ^ (2 : ℕ) + (1 : ℝ))⁻¹
  ∀ (hεMpos : ∀ (m : (k : ↥K) × Ny k), (0 : ℝ) < εM m)
    (hweights : ∀ (Φ : bf.Lab ⊕ Fin fp.Mc) (y : ℝ), ∑ m : (k : ↥K) × Ny k with (↑m.fst : (_ : bf.Lab
      ⊕ Fin fp.Mc) × ℤ × ℤ).fst = Φ, εM m * ‖am m y‖ ^ (2 : ℕ) ≤ w Φ),
  let bnd : ℝ :=
    B * ((4 : ℝ) * max (1 : ℝ) ((4 : ℝ) * B / δc) + (1 : ℝ)) ^ ((4 : ℕ) * dB)
  ∀ (_ : ∀ (y : ℝ), (↑(Finset.card ({m : (k : ↥K) × Ny k | y ∈ cell m.fst})) : ℝ) ≤ N * bnd),
  ∃ (cellOf : (k : ↥K) × Ny k → ℤ × ℤ) (lamOf : (k : ↥K) × Ny k → ℝ) (γOf : (k : ↥K) ×
    Ny k → ℝ), (∀ (m : (k : ↥K) × Ny k), cellOf m ∈ FM ((LiftData.mk (fun (m : (k :
    ↥K) × Ny k) => (↑m.fst : (_ : bf.Lab ⊕ Fin fp.Mc) × ℤ × ℤ).fst) sf qf am w εM δc
    ham hsfm hsf1 hqm hqle hw (fun (y : ℝ) => LE.le.trans (hqsum y) hδcN) (fun (m : (k
    : ↥K) × Ny k) => LT.lt.le (hεMpos m)) hweights).own m) ∧ (∀ (y : ℝ), (LiftData.mk
    (fun (m : (k : ↥K) × Ny k) => (↑m.fst : (_ : bf.Lab ⊕ Fin fp.Mc) × ℤ × ℤ).fst) sf
    qf am w εM δc ham hsfm hsf1 hqm hqle hw (fun (y : ℝ) => LE.le.trans (hqsum y)
    hδcN) (fun (m : (k : ↥K) × Ny k) => LT.lt.le (hεMpos m)) hweights).a m y =
    (dyadicGridCell A.G (cellOf m).1 (cellOf m).2).indicator (fun (_ : ℝ) =>
    (LiftData.mk (fun (m : (k : ↥K) × Ny k) => (↑m.fst : (_ : bf.Lab ⊕ Fin fp.Mc) × ℤ
    × ℤ).fst) sf qf am w εM δc ham hsfm hsf1 hqm hqle hw (fun (y : ℝ) => LE.le.trans
    (hqsum y) hδcN) (fun (m : (k : ↥K) × Ny k) => LT.lt.le (hεMpos m)) hweights).a m
    (dyadicGridLeft A.G (cellOf m).1 (cellOf m).2)) y) ∧ |lamOf m| * dyadicGridLength
    A.G (cellOf m).1 ^ (2 : ℕ) ≤ B ∧ ∀ (y : ℝ), ψ m y = (↑(ζ y) : ℂ) * (↑((𝐞 : ℝ →
    Circle) ((↑(slotCoeff l) : ℝ) * centerPhase (bf.vtag z) ρ y)) : ℂ) * (↑((𝐞 : ℝ →
    Circle) (lamOf m * (y - dyadicGridLeft A.G (cellOf m).1 (cellOf m).2) ^ (2 : ℕ) +
    γOf m * (y - dyadicGridLeft A.G (cellOf m).1 (cellOf m).2))) : ℂ)) ∧ (∀ (y : ℝ),
    (↑(Finset.card ({m : (k : ↥K) × Ny k | y ∈ dyadicGridCell A.G (cellOf m).1 (cellOf
    m).2})) : ℝ) ≤ N * bnd) ∧ ∃ (Key : Type) (keyOf : (k : ↥K) × Ny k → Key) (dvOf :
    Key → ℕ) (θvOf : (k : Key) → Fin (dvOf k) → ℝ) (βOf : Key → ℝ) (σOf : (m : (k :
    ↥K) × Ny k) → Fin (dvOf (keyOf m) + (bf.vtag z).dim) → ℚ), (∀ (m m' : (k : ↥K) ×
    Ny k), (LiftData.mk (fun (m : (k : ↥K) × Ny k) => (↑m.fst : (_ : bf.Lab ⊕ Fin
    fp.Mc) × ℤ × ℤ).fst) sf qf am w εM δc ham hsfm hsf1 hqm hqle hw (fun (y : ℝ) =>
    LE.le.trans (hqsum y) hδcN) (fun (m : (k : ↥K) × Ny k) => LT.lt.le (hεMpos m))
    hweights).own m = (LiftData.mk (fun (m : (k : ↥K) × Ny k) => (↑m.fst : (_ : bf.Lab
    ⊕ Fin fp.Mc) × ℤ × ℤ).fst) sf qf am w εM δc ham hsfm hsf1 hqm hqle hw (fun (y : ℝ)
    => LE.le.trans (hqsum y) hδcN) (fun (m : (k : ↥K) × Ny k) => LT.lt.le (hεMpos m))
    hweights).own m' → cellOf m = cellOf m' → keyOf m = keyOf m') ∧ (∀ (m m' : (k :
    ↥K) × Ny k), keyOf m = keyOf m' → lamOf m = lamOf m') ∧ (∀ (k : Key), dvOf k ≤ dB)
    ∧ (∀ (m : (k : ↥K) × Ny k) (i : Fin (dvOf (keyOf m) + (bf.vtag z).dim)),
    (↑(rationalHeight (σOf m i)) : ℝ) ≤ B * ((1 : ℝ) + (4 : ℝ) * ((2 : ℝ) * (↑dB : ℝ)
    + (1 : ℝ)) * max (1 : ℝ) ((4 : ℝ) * B / δc))) ∧ (∀ (m : (k : ↥K) × Ny k), γOf m =
    βOf (keyOf m) + ∑ i : Fin (dvOf (keyOf m) + (bf.vtag z).dim), (↑(σOf m i) : ℝ) *
    Fin.append (θvOf (keyOf m)) (bf.vtag z).θ i) ∧ (∀ (m m' : (k : ↥K) × Ny k), keyOf
    m = keyOf m' → (LiftData.mk (fun (m : (k : ↥K) × Ny k) => (↑m.fst : (_ : bf.Lab ⊕
    Fin fp.Mc) × ℤ × ℤ).fst) sf qf am w εM δc ham hsfm hsf1 hqm hqle hw (fun (y : ℝ)
    => LE.le.trans (hqsum y) hδcN) (fun (m : (k : ↥K) × Ny k) => LT.lt.le (hεMpos m))
    hweights).own m = (LiftData.mk (fun (m : (k : ↥K) × Ny k) => (↑m.fst : (_ : bf.Lab
    ⊕ Fin fp.Mc) × ℤ × ℤ).fst) sf qf am w εM δc ham hsfm hsf1 hqm hqle hw (fun (y : ℝ)
    => LE.le.trans (hqsum y) hδcN) (fun (m : (k : ↥K) × Ny k) => LT.lt.le (hεMpos m))
    hweights).own m' ∧ cellOf m = cellOf m') ∧ ∀ (m m' : (k : ↥K) × Ny k), keyOf m =
    keyOf m' → ∃ (a : Fin (dvOf (keyOf m) + (bf.vtag z).dim) → ℚ) (b : Fin (dvOf
    (keyOf m) + (bf.vtag z).dim) → ℚ), (∀ (i : Fin (dvOf (keyOf m) + (bf.vtag
    z).dim)), (↑(rationalHeight (a i)) : ℝ) ≤ B * ((1 : ℝ) + (4 : ℝ) * ((2 : ℝ) * (↑dB
    : ℝ) + (1 : ℝ)) * max (1 : ℝ) ((4 : ℝ) * B / δc))) ∧ (∀ (i : Fin (dvOf (keyOf m) +
    (bf.vtag z).dim)), (↑(rationalHeight (b i)) : ℝ) ≤ B * ((1 : ℝ) + (4 : ℝ) * ((2 :
    ℝ) * (↑dB : ℝ) + (1 : ℝ)) * max (1 : ℝ) ((4 : ℝ) * B / δc))) ∧ γOf m - γOf m' = ∑
    i : Fin (dvOf (keyOf m) + (bf.vtag z).dim), (↑((a - b) i) : ℝ) * Fin.append (θvOf
    (keyOf m)) (bf.vtag z).θ i


open scoped Classical in
private def MainAttemptLiftHcellcountStatement : Prop :=
  ∀ (κ : LocalKernelClass)
    (c₀ : ℕ)
    (D : ℕ)
    (A : ActiveSetup κ c₀)
    (bf : A.BasicFamilies)
    (fp : bf.FamParams)
    (l : Fin (4 : ℕ))
    (s : List (CatCol bf.Vtx))
    (d : bf.Vtx)
    (cs : Finset (ℤ × ℤ))
    (G : bf.Grp)
    (j : ℕ)
    (g : ℤ)
    (dB : ℕ)
    (H : ℝ)
    (δc : ℝ)
    (N : ℝ),
  let FM : bf.Lab ⊕ Fin fp.Mc → Finset (ℤ × ℤ) :=
    fp.firstCells cs l s G j d
  let X : ℝ :=
    (1 : ℝ) + Real.log (chartTranslationBudget (H ^ (6 : ℕ))) + Real.log ((3 : ℝ) *
      fp.ballEdgeH dB (fp.ballRadius g (fp.bbase j + fp.P)))
  let K : Finset ((_ : bf.Lab ⊕ Fin fp.Mc) × ℤ × ℤ) :=
    Finset.univ.sigma FM
  ∀ (Ny : ↥K → Type)
    (_ : (k : ↥K) → Fintype (Ny k)),
  let B : ℝ :=
    Real.exp ((↑D : ℝ) * X ^ D)
  let cell : ↥K → Set ℝ :=
    fun (k : ↥K) => dyadicGridCell A.G (↑k : (_ : bf.Lab ⊕ Fin fp.Mc) × ℤ × ℤ).snd.1 (↑k
      : (_ : bf.Lab ⊕ Fin fp.Mc) × ℤ × ℤ).snd.2
  let E : bf.Lab ⊕ Fin fp.Mc → Set ℝ :=
    fun (Φ : bf.Lab ⊕ Fin fp.Mc) => ⋃ I ∈ FM Φ, dyadicGridCell A.G I.1 I.2
  ∀ (_ : ∀ (m : (k : ↥K) × Ny k), (↑m.fst : (_ : bf.Lab ⊕ Fin fp.Mc) × ℤ × ℤ).snd ∈ FM
      (↑m.fst : (_ : bf.Lab ⊕ Fin fp.Mc) × ℤ × ℤ).fst)
    (_ : ∀ (y : ℝ), (↑(Finset.card ({Φ : bf.Lab ⊕ Fin fp.Mc | y ∈ E Φ})) : ℝ) ≤ N),
  let bnd : ℝ :=
    B * ((4 : ℝ) * max (1 : ℝ) ((4 : ℝ) * B / δc) + (1 : ℝ)) ^ ((4 : ℕ) * dB)
  ∀ (_ : (0 : ℝ) ≤ bnd)
    (_ : ∀ (k : ↥K), (↑(Fintype.card (Ny k)) : ℝ) ≤ bnd),
  ∀ (y : ℝ), (↑(Finset.card ({m : (k : ↥K) × Ny k | y ∈ cell m.fst})) : ℝ) ≤ N * bnd


open scoped Classical in
private def MainAttemptLiftStage2Statement : Prop :=
  ∀ (κ : LocalKernelClass)
    (c₀ : ℕ)
    (D : ℕ)
    (A : ActiveSetup κ c₀)
    (bf : A.BasicFamilies)
    (fp : bf.FamParams)
    (l : Fin (4 : ℕ))
    (s : List (CatCol bf.Vtx))
    (d : bf.Vtx)
    (cs : Finset (ℤ × ℤ))
    (G : bf.Grp)
    (j : ℕ)
    (z : bf.Vtx)
    (g : ℤ)
    (dB : ℕ)
    (_ : ∀ (w : bf.Vtx), (bf.vtag w).dim ≤ dB)
    (δ : ℝ)
    (ρ : Fin (bf.vtag z).dim → ℝ)
    (H : ℝ)
    (δc : ℝ)
    (N : ℝ)
    (_ : δc ^ (2 : ℕ) * N * A.colBudget ^ (2 : ℕ) ≤ (1 : ℝ)),
  let FM : bf.Lab ⊕ Fin fp.Mc → Finset (ℤ × ℤ) :=
    fp.firstCells cs l s G j d
  let X : ℝ :=
    (1 : ℝ) + Real.log (chartTranslationBudget (H ^ (6 : ℕ))) + Real.log ((3 : ℝ) *
      fp.ballEdgeH dB (fp.ballRadius g (fp.bbase j + fp.P)))
  let K : Finset ((_ : bf.Lab ⊕ Fin fp.Mc) × ℤ × ℤ) :=
    Finset.univ.sigma FM
  ∀ (Ny : ↥K → Type)
    (_ : (k : ↥K) → Fintype (Ny k))
    (coef : (k : ↥K) → Ny k → ℂ)
    (lam : ↥K → ℝ)
    (γ : (k : ↥K) → Ny k → ℝ)
    (dv : ↥K → ℕ)
    (θv : (k : ↥K) → Fin (dv k) → ℝ)
    (σ : (k : ↥K) → Ny k → Fin (dv k + (bf.vtag z).dim) → ℚ)
    (β : ↥K → ℝ)
    (_ : ∀ (k : ↥K) (k_1 : Ny k), γ k k_1 = β k + ∑ i : Fin (dv k + (bf.vtag z).dim), (↑(σ k
      k_1 i) : ℝ) * Fin.append (θv k) (bf.vtag z).θ i)
    (_ : ∀ (k : ↥K), dv k ≤ dB),
  let B : ℝ :=
    Real.exp ((↑D : ℝ) * X ^ D)
  ∀ (_ : ∀ (k : ↥K) (k_1 : Ny k) (i : Fin (dv k + (bf.vtag z).dim)), (↑(rationalHeight (σ k
      k_1 i)) : ℝ) ≤ B * ((1 : ℝ) + (4 : ℝ) * ((↑(dv k + (bf.vtag z).dim) : ℝ) + (1 :
      ℝ)) * max (1 : ℝ) ((4 : ℝ) * B / δc)))
    (_ : ∀ (k : ↥K), |lam k| * dyadicGridLength A.G (↑k : (_ : bf.Lab ⊕ Fin fp.Mc) × ℤ ×
      ℤ).snd.1 ^ (2 : ℕ) ≤ B)
    (_ : (0 : ℝ) ≤ B),
  let ζ : ℝ → ℝ :=
    centerCut (bf.vtag z) δ ρ
  let cell : ↥K → Set ℝ :=
    fun (k : ↥K) => dyadicGridCell A.G (↑k : (_ : bf.Lab ⊕ Fin fp.Mc) × ℤ × ℤ).snd.1 (↑k
      : (_ : bf.Lab ⊕ Fin fp.Mc) × ℤ × ℤ).snd.2
  let a₀ : ↥K → ℝ :=
    fun (k : ↥K) => dyadicGridLeft A.G (↑k : (_ : bf.Lab ⊕ Fin fp.Mc) × ℤ × ℤ).snd.1 (↑k
      : (_ : bf.Lab ⊕ Fin fp.Mc) × ℤ × ℤ).snd.2
  let φ : bf.Lab ⊕ Fin fp.Mc → ℝ → ℂ :=
    mainScalar fp.Mc (bf.origCols l) s
  let w : bf.Lab ⊕ Fin fp.Mc → ℝ :=
    mainWeight fp.Mc (bf.origCols l)
  ∀ (_ : ∀ (Φ : bf.Lab ⊕ Fin fp.Mc), (0 : ℝ) < w Φ),
  let ψ : (k : ↥K) × Ny k → ℝ → ℂ :=
    fun (m : (k : ↥K) × Ny k) (y : ℝ) => (↑(ζ y) : ℂ) * (↑((𝐞 : ℝ → Circle)
      ((↑(slotCoeff l) : ℝ) * centerPhase (bf.vtag z) ρ y)) : ℂ) * (↑((𝐞 : ℝ → Circle)
      (lam m.fst * (y - a₀ m.fst) ^ (2 : ℕ) + γ m.fst m.snd * (y - a₀ m.fst))) : ℂ)
  let am : (k : ↥K) × Ny k → ℝ → ℂ :=
    fun (m : (k : ↥K) × Ny k) => (cell m.fst).indicator fun (_ : ℝ) => coef m.fst m.snd
  let E : bf.Lab ⊕ Fin fp.Mc → Set ℝ :=
    fun (Φ : bf.Lab ⊕ Fin fp.Mc) => ⋃ I ∈ FM Φ, dyadicGridCell A.G I.1 I.2
  let sf : ℝ → ℂ :=
    fun (y : ℝ) => (↑(ζ y) : ℂ) ^ (2 : ℕ)
  let qf : bf.Lab ⊕ Fin fp.Mc → ℝ → ℂ :=
    fun (Φ : bf.Lab ⊕ Fin fp.Mc) => (E Φ).indicator fun (y : ℝ) => ∑ m : (k : ↥K) × Ny k
      with (↑m.fst : (_ : bf.Lab ⊕ Fin fp.Mc) × ℤ × ℤ).fst = Φ, am m y * ψ m y - sf y *
      φ Φ y
  ∀ (_ : ∀ (m : (k : ↥K) × Ny k), Measurable (ψ m))
    (_ : ∀ (m : (k : ↥K) × Ny k), Measurable (am m))
    (_ : Measurable sf)
    (_ : ∀ (y : ℝ), ‖sf y‖ ≤ (1 : ℝ))
    (_ : ∀ (Φ : bf.Lab ⊕ Fin fp.Mc), Measurable (qf Φ))
    (_ : ∀ (m : (k : ↥K) × Ny k), (↑m.fst : (_ : bf.Lab ⊕ Fin fp.Mc) × ℤ × ℤ).snd ∈ FM
      (↑m.fst : (_ : bf.Lab ⊕ Fin fp.Mc) × ℤ × ℤ).fst)
    (_ : ∀ (m : (k : ↥K) × Ny k), ∀ y ∉ cell m.fst, am m y = (0 : ℂ))
    (_ : ∀ (Φ : bf.Lab ⊕ Fin fp.Mc), ∀ y ∉ E Φ, ∀ (m : (k : ↥K) × Ny k), (↑m.fst : (_ :
      bf.Lab ⊕ Fin fp.Mc) × ℤ × ℤ).fst = Φ → am m y = (0 : ℂ))
    (_ : ∀ (Φ : bf.Lab ⊕ Fin fp.Mc) (y : ℝ), ‖qf Φ y‖ ≤ δc)
    (_ : ∀ (y : ℝ), ∑ Φ : bf.Lab ⊕ Fin fp.Mc, ‖qf Φ y‖ ^ (2 : ℕ) / w Φ ≤ δc ^ (2 : ℕ) * N *
      A.colBudget ^ (2 : ℕ)),
  let εM : (k : ↥K) × Ny k → ℝ :=
    fun (m : (k : ↥K) × Ny k) => w (↑m.fst : (_ : bf.Lab ⊕ Fin fp.Mc) × ℤ × ℤ).fst * (∑
      i : Ny m.fst, ‖coef m.fst i‖ ^ (2 : ℕ) + (1 : ℝ))⁻¹
  ∀ (_ : ∀ (m : (k : ↥K) × Ny k), (0 : ℝ) < εM m)
    (_ : ∀ (m : (k : ↥K) × Ny k), (εM m)⁻¹ ≤ A.colBudget ^ (2 : ℕ) * (B ^ (2 : ℕ) + (1 : ℝ)))
    (_ : ∀ (m : (k : ↥K) × Ny k), εM m ≤ w (↑m.fst : (_ : bf.Lab ⊕ Fin fp.Mc) × ℤ × ℤ).fst)
    (_ : ∀ (Φ : bf.Lab ⊕ Fin fp.Mc) (y : ℝ), ∑ m : (k : ↥K) × Ny k with (↑m.fst : (_ : bf.Lab
      ⊕ Fin fp.Mc) × ℤ × ℤ).fst = Φ, εM m * ‖am m y‖ ^ (2 : ℕ) ≤ w Φ)
    (_ : ∀ (Φ : bf.Lab ⊕ Fin fp.Mc) (y : ℝ), ∑ m : (k : ↥K) × Ny k with (↑m.fst : (_ : bf.Lab
      ⊕ Fin fp.Mc) × ℤ × ℤ).fst = Φ, ‖am m y‖ ≤ B),
  let bnd : ℝ :=
    B * ((4 : ℝ) * max (1 : ℝ) ((4 : ℝ) * B / δc) + (1 : ℝ)) ^ ((4 : ℕ) * dB)
  ∀ (_ : ∀ (y : ℝ), (↑(Finset.card ({m : (k : ↥K) × Ny k | y ∈ cell m.fst})) : ℝ) ≤ N * bnd),
  ∃ (Md : Type) (_ : Fintype Md) (L : LiftData (bf.Lab ⊕ Fin fp.Mc) Md) (ψ : Md → ℝ →
    ℂ), (∀ (Φ : bf.Lab ⊕ Fin fp.Mc), L.εP Φ = w Φ) ∧ L.δ = δc ∧ (∀ (m : Md), (0 : ℝ) <
    L.εM m) ∧ (∀ (m : Md), L.εM m ≤ L.εP (L.own m)) ∧ (∀ (m : Md), (L.εM m)⁻¹ ≤
    A.colBudget ^ (2 : ℕ) * (B ^ (2 : ℕ) + (1 : ℝ))) ∧ (∀ (y : ℝ), ∑ Φ : bf.Lab ⊕ Fin
    fp.Mc, ‖L.q Φ y‖ ^ (2 : ℕ) / L.εP Φ ≤ δc ^ (2 : ℕ) * N * A.colBudget ^ (2 : ℕ)) ∧
    (∀ (y : ℝ), L.s y = (↑(ζ y) : ℂ) ^ (2 : ℕ)) ∧ (∀ (m : Md), Measurable (ψ m)) ∧ (∀
    (Φ : bf.Lab ⊕ Fin fp.Mc) (y : ℝ), (∀ I ∈ FM Φ, y ∉ dyadicGridCell A.G I.1 I.2) →
    L.q Φ y = (0 : ℂ) ∧ ∀ (m : Md), L.own m = Φ → L.a m y = (0 : ℂ)) ∧ (∀ (Φ : bf.Lab
    ⊕ Fin fp.Mc) (y : ℝ), (∃ I ∈ FM Φ, y ∈ dyadicGridCell A.G I.1 I.2) → L.q Φ y = ∑ m
    : Md with L.own m = Φ, L.a m y * ψ m y - L.s y * φ Φ y) ∧ (∀ (y : ℝ) (β : bf.Lab ⊕
    Fin fp.Mc → ℂ), (∀ (Φ : bf.Lab ⊕ Fin fp.Mc), β Φ ≠ (0 : ℂ) → ∃ I ∈ FM Φ, y ∈
    dyadicGridCell A.G I.1 I.2) → (L.at_ y : ColumnHilbert (bf.Lab ⊕ Fin fp.Mc) →
    ColumnHilbert Md) (augmentedMain (fun (Φ : bf.Lab ⊕ Fin fp.Mc) => φ Φ y) L.εP β) =
    ∑ m : Md, (β (L.own m) * L.a m y) • augmentedMode (fun (m : Md) => ψ m y) L.εM m)
    ∧ (∀ (Φ : bf.Lab ⊕ Fin fp.Mc) (y : ℝ), ∑ m : Md with L.own m = Φ, ‖L.a m y‖ ≤ B) ∧
    (∃ (cellOf : Md → ℤ × ℤ) (lamOf : Md → ℝ) (γOf : Md → ℝ), (∀ (m : Md), cellOf m ∈
    FM (L.own m) ∧ (∀ (y : ℝ), L.a m y = (dyadicGridCell A.G (cellOf m).1 (cellOf
    m).2).indicator (fun (_ : ℝ) => L.a m (dyadicGridLeft A.G (cellOf m).1 (cellOf
    m).2)) y) ∧ |lamOf m| * dyadicGridLength A.G (cellOf m).1 ^ (2 : ℕ) ≤ B ∧ ∀ (y :
    ℝ), ψ m y = (↑(ζ y) : ℂ) * (↑((𝐞 : ℝ → Circle) ((↑(slotCoeff l) : ℝ) * centerPhase
    (bf.vtag z) ρ y)) : ℂ) * (↑((𝐞 : ℝ → Circle) (lamOf m * (y - dyadicGridLeft A.G
    (cellOf m).1 (cellOf m).2) ^ (2 : ℕ) + γOf m * (y - dyadicGridLeft A.G (cellOf
    m).1 (cellOf m).2))) : ℂ)) ∧ (∀ (y : ℝ), (↑(Finset.card ({m : Md | y ∈
    dyadicGridCell A.G (cellOf m).1 (cellOf m).2})) : ℝ) ≤ N * bnd) ∧ ∃ (Key : Type)
    (keyOf : Md → Key) (dvOf : Key → ℕ) (θvOf : (k : Key) → Fin (dvOf k) → ℝ) (βOf :
    Key → ℝ) (σOf : (m : Md) → Fin (dvOf (keyOf m) + (bf.vtag z).dim) → ℚ), (∀ (m m' :
    Md), L.own m = L.own m' → cellOf m = cellOf m' → keyOf m = keyOf m') ∧ (∀ (m m' :
    Md), keyOf m = keyOf m' → lamOf m = lamOf m') ∧ (∀ (k : Key), dvOf k ≤ dB) ∧ (∀ (m
    : Md) (i : Fin (dvOf (keyOf m) + (bf.vtag z).dim)), (↑(rationalHeight (σOf m i)) :
    ℝ) ≤ B * ((1 : ℝ) + (4 : ℝ) * ((2 : ℝ) * (↑dB : ℝ) + (1 : ℝ)) * max (1 : ℝ) ((4 :
    ℝ) * B / δc))) ∧ (∀ (m : Md), γOf m = βOf (keyOf m) + ∑ i : Fin (dvOf (keyOf m) +
    (bf.vtag z).dim), (↑(σOf m i) : ℝ) * Fin.append (θvOf (keyOf m)) (bf.vtag z).θ i)
    ∧ (∀ (m m' : Md), keyOf m = keyOf m' → L.own m = L.own m' ∧ cellOf m = cellOf m')
    ∧ ∀ (m m' : Md), keyOf m = keyOf m' → ∃ (a : Fin (dvOf (keyOf m) + (bf.vtag
    z).dim) → ℚ) (b : Fin (dvOf (keyOf m) + (bf.vtag z).dim) → ℚ), (∀ (i : Fin (dvOf
    (keyOf m) + (bf.vtag z).dim)), (↑(rationalHeight (a i)) : ℝ) ≤ B * ((1 : ℝ) + (4 :
    ℝ) * ((2 : ℝ) * (↑dB : ℝ) + (1 : ℝ)) * max (1 : ℝ) ((4 : ℝ) * B / δc))) ∧ (∀ (i :
    Fin (dvOf (keyOf m) + (bf.vtag z).dim)), (↑(rationalHeight (b i)) : ℝ) ≤ B * ((1 :
    ℝ) + (4 : ℝ) * ((2 : ℝ) * (↑dB : ℝ) + (1 : ℝ)) * max (1 : ℝ) ((4 : ℝ) * B / δc)))
    ∧ γOf m - γOf m' = ∑ i : Fin (dvOf (keyOf m) + (bf.vtag z).dim), (↑((a - b) i) :
    ℝ) * Fin.append (θvOf (keyOf m)) (bf.vtag z).θ i) ∧ ∀ (y : ℝ), (↑(Finset.card ({m
    : Md | L.a m y ≠ (0 : ℂ)})) : ℝ) ≤ N * bnd


open scoped Classical in
private def MainAttemptLiftStage1Statement : Prop :=
  ∀ (κ : LocalKernelClass)
    (c₀ : ℕ)
    (D : ℕ)
    (A : ActiveSetup κ c₀)
    (bf : A.BasicFamilies)
    (fp : bf.FamParams)
    (l : Fin (4 : ℕ))
    (s : List (CatCol bf.Vtx))
    (d : bf.Vtx)
    (cs : Finset (ℤ × ℤ))
    (_ : cs ⊆ A.cells)
    (G : bf.Grp)
    (j : ℕ)
    (z : bf.Vtx)
    (g : ℤ)
    (dB : ℕ)
    (_ : ∀ (w : bf.Vtx), (bf.vtag w).dim ≤ dB)
    (δ : ℝ)
    (_ : (0 : ℝ) < δ)
    (_ : δ < (1 / 4 : ℝ))
    (ρ : Fin (bf.vtag z).dim → ℝ)
    (H : ℝ)
    (δc : ℝ)
    (_ : (0 : ℝ) < δc)
    (N : ℝ)
    (_ : (0 : ℝ) ≤ N)
    (_ : ∀ I ∈ A.cells, (↑(mainLabels A.G fp.Mc (bf.origCols l) s I (fp.brank j)).card : ℝ) ≤
      N)
    (_ : δc ^ (2 : ℕ) * N * A.colBudget ^ (2 : ℕ) ≤ (1 : ℝ)),
  let FM : bf.Lab ⊕ Fin fp.Mc → Finset (ℤ × ℤ) :=
    fp.firstCells cs l s G j d
  let X : ℝ :=
    (1 : ℝ) + Real.log (chartTranslationBudget (H ^ (6 : ℕ))) + Real.log ((3 : ℝ) *
      fp.ballEdgeH dB (fp.ballRadius g (fp.bbase j + fp.P)))
  let K : Finset ((_ : bf.Lab ⊕ Fin fp.Mc) × ℤ × ℤ) :=
    Finset.univ.sigma FM
  ∀ (Ny : ↥K → Type)
    (_ : (k : ↥K) → Fintype (Ny k))
    (coef : (k : ↥K) → Ny k → ℂ)
    (lam : ↥K → ℝ)
    (γ : (k : ↥K) → Ny k → ℝ)
    (dv : ↥K → ℕ)
    (θv : (k : ↥K) → Fin (dv k) → ℝ)
    (σ : (k : ↥K) → Ny k → Fin (dv k + (bf.vtag z).dim) → ℚ)
    (β : ↥K → ℝ)
    (_ : ∀ (k : ↥K) (k_1 : Ny k), γ k k_1 = β k + ∑ i : Fin (dv k + (bf.vtag z).dim), (↑(σ k
      k_1 i) : ℝ) * Fin.append (θv k) (bf.vtag z).θ i)
    (_ : ∀ (k : ↥K), dv k ≤ dB),
  let B : ℝ :=
    Real.exp ((↑D : ℝ) * X ^ D)
  ∀ (_ : ∀ (k : ↥K), (↑(Fintype.card (Ny k)) : ℝ) ≤ B * ((4 : ℝ) * max (1 : ℝ) ((4 : ℝ) * B /
      δc) + (1 : ℝ)) ^ (dv k + (bf.vtag z).dim + (dv k + (bf.vtag z).dim)))
    (_ : ∀ (k : ↥K) (k_1 : Ny k) (i : Fin (dv k + (bf.vtag z).dim)), (↑(rationalHeight (σ k
      k_1 i)) : ℝ) ≤ B * ((1 : ℝ) + (4 : ℝ) * ((↑(dv k + (bf.vtag z).dim) : ℝ) + (1 :
      ℝ)) * max (1 : ℝ) ((4 : ℝ) * B / δc)))
    (_ : ∀ (k : ↥K), ∑ k_1 : Ny k, ‖coef k k_1‖ ≤ B)
    (_ : ∀ (k : ↥K), |lam k| * dyadicGridLength A.G (↑k : (_ : bf.Lab ⊕ Fin fp.Mc) × ℤ ×
      ℤ).snd.1 ^ (2 : ℕ) ≤ B)
    (_ : (0 : ℝ) ≤ B),
  let ζ : ℝ → ℝ :=
    centerCut (bf.vtag z) δ ρ
  let cell : ↥K → Set ℝ :=
    fun (k : ↥K) => dyadicGridCell A.G (↑k : (_ : bf.Lab ⊕ Fin fp.Mc) × ℤ × ℤ).snd.1 (↑k
      : (_ : bf.Lab ⊕ Fin fp.Mc) × ℤ × ℤ).snd.2
  let a₀ : ↥K → ℝ :=
    fun (k : ↥K) => dyadicGridLeft A.G (↑k : (_ : bf.Lab ⊕ Fin fp.Mc) × ℤ × ℤ).snd.1 (↑k
      : (_ : bf.Lab ⊕ Fin fp.Mc) × ℤ × ℤ).snd.2
  let φ : bf.Lab ⊕ Fin fp.Mc → ℝ → ℂ :=
    mainScalar fp.Mc (bf.origCols l) s
  let w : bf.Lab ⊕ Fin fp.Mc → ℝ :=
    mainWeight fp.Mc (bf.origCols l)
  ∀ (_ : ∀ (Φ : bf.Lab ⊕ Fin fp.Mc), (0 : ℝ) < w Φ)
    (_ : ∀ (Φ : bf.Lab ⊕ Fin fp.Mc), (w Φ)⁻¹ ≤ A.colBudget ^ (2 : ℕ)),
  let ψ : (k : ↥K) × Ny k → ℝ → ℂ :=
    fun (m : (k : ↥K) × Ny k) (y : ℝ) => (↑(ζ y) : ℂ) * (↑((𝐞 : ℝ → Circle)
      ((↑(slotCoeff l) : ℝ) * centerPhase (bf.vtag z) ρ y)) : ℂ) * (↑((𝐞 : ℝ → Circle)
      (lam m.fst * (y - a₀ m.fst) ^ (2 : ℕ) + γ m.fst m.snd * (y - a₀ m.fst))) : ℂ)
  let am : (k : ↥K) × Ny k → ℝ → ℂ :=
    fun (m : (k : ↥K) × Ny k) => (cell m.fst).indicator fun (_ : ℝ) => coef m.fst m.snd
  let E : bf.Lab ⊕ Fin fp.Mc → Set ℝ :=
    fun (Φ : bf.Lab ⊕ Fin fp.Mc) => ⋃ I ∈ FM Φ, dyadicGridCell A.G I.1 I.2
  let sf : ℝ → ℂ :=
    fun (y : ℝ) => (↑(ζ y) : ℂ) ^ (2 : ℕ)
  let qf : bf.Lab ⊕ Fin fp.Mc → ℝ → ℂ :=
    fun (Φ : bf.Lab ⊕ Fin fp.Mc) => (E Φ).indicator fun (y : ℝ) => ∑ m : (k : ↥K) × Ny k
      with (↑m.fst : (_ : bf.Lab ⊕ Fin fp.Mc) × ℤ × ℤ).fst = Φ, am m y * ψ m y - sf y *
      φ Φ y
  ∀ (_ : ∀ (m : (k : ↥K) × Ny k), Measurable (ψ m))
    (_ : ∀ (m : (k : ↥K) × Ny k), Measurable (am m))
    (_ : Measurable sf)
    (_ : ∀ (y : ℝ), ‖sf y‖ ≤ (1 : ℝ))
    (_ : ∀ (Φ : bf.Lab ⊕ Fin fp.Mc), Measurable (qf Φ))
    (_ : ∀ (m : (k : ↥K) × Ny k), (↑m.fst : (_ : bf.Lab ⊕ Fin fp.Mc) × ℤ × ℤ).snd ∈ FM
      (↑m.fst : (_ : bf.Lab ⊕ Fin fp.Mc) × ℤ × ℤ).fst)
    (_ : ∀ (m : (k : ↥K) × Ny k), ∀ y ∉ cell m.fst, am m y = (0 : ℂ))
    (_ : ∀ {R : Type} [AddCommMonoid R] (Φ : bf.Lab ⊕ Fin fp.Mc) (y : ℝ) (I₀ : ℤ × ℤ) (hI₀ :
      I₀ ∈ FM Φ), y ∈ dyadicGridCell A.G I₀.1 I₀.2 → ∀ (F : (k : ↥K) × Ny k → R), (∀ (m
      : (k : ↥K) × Ny k), y ∉ cell m.fst → F m = (0 : R)) → ∑ m : (k : ↥K) × Ny k with
      (↑m.fst : (_ : bf.Lab ⊕ Fin fp.Mc) × ℤ × ℤ).fst = Φ, F m = ∑ i : Ny (Subtype.mk
      ((@Sigma.mk (bf.Lab ⊕ Fin fp.Mc) (fun _ => ℤ × ℤ) Φ I₀)) (Finset.mem_sigma.mpr
      (And.intro (Finset.mem_univ ((@Sigma.mk (bf.Lab ⊕ Fin fp.Mc) (fun _ => ℤ × ℤ) Φ
      I₀)).fst) hI₀))), F (Sigma.mk (Subtype.mk ((@Sigma.mk (bf.Lab ⊕ Fin fp.Mc) (fun _
      => ℤ × ℤ) Φ I₀)) (Finset.mem_sigma.mpr (And.intro (Finset.mem_univ ((@Sigma.mk
      (bf.Lab ⊕ Fin fp.Mc) (fun _ => ℤ × ℤ) Φ I₀)).fst) hI₀))) i))
    (_ : ∀ (Φ : bf.Lab ⊕ Fin fp.Mc), ∀ y ∉ E Φ, ∀ (m : (k : ↥K) × Ny k), (↑m.fst : (_ :
      bf.Lab ⊕ Fin fp.Mc) × ℤ × ℤ).fst = Φ → am m y = (0 : ℂ))
    (_ : ∀ (Φ : bf.Lab ⊕ Fin fp.Mc) (y : ℝ), ‖qf Φ y‖ ≤ δc),
  ∃ (Md : Type) (_ : Fintype Md) (L : LiftData (bf.Lab ⊕ Fin fp.Mc) Md) (ψ : Md → ℝ →
    ℂ), (∀ (Φ : bf.Lab ⊕ Fin fp.Mc), L.εP Φ = w Φ) ∧ L.δ = δc ∧ (∀ (m : Md), (0 : ℝ) <
    L.εM m) ∧ (∀ (m : Md), L.εM m ≤ L.εP (L.own m)) ∧ (∀ (m : Md), (L.εM m)⁻¹ ≤
    A.colBudget ^ (2 : ℕ) * (B ^ (2 : ℕ) + (1 : ℝ))) ∧ (∀ (y : ℝ), ∑ Φ : bf.Lab ⊕ Fin
    fp.Mc, ‖L.q Φ y‖ ^ (2 : ℕ) / L.εP Φ ≤ δc ^ (2 : ℕ) * N * A.colBudget ^ (2 : ℕ)) ∧
    (∀ (y : ℝ), L.s y = (↑(ζ y) : ℂ) ^ (2 : ℕ)) ∧ (∀ (m : Md), Measurable (ψ m)) ∧ (∀
    (Φ : bf.Lab ⊕ Fin fp.Mc) (y : ℝ), (∀ I ∈ FM Φ, y ∉ dyadicGridCell A.G I.1 I.2) →
    L.q Φ y = (0 : ℂ) ∧ ∀ (m : Md), L.own m = Φ → L.a m y = (0 : ℂ)) ∧ (∀ (Φ : bf.Lab
    ⊕ Fin fp.Mc) (y : ℝ), (∃ I ∈ FM Φ, y ∈ dyadicGridCell A.G I.1 I.2) → L.q Φ y = ∑ m
    : Md with L.own m = Φ, L.a m y * ψ m y - L.s y * φ Φ y) ∧ (∀ (y : ℝ) (β : bf.Lab ⊕
    Fin fp.Mc → ℂ), (∀ (Φ : bf.Lab ⊕ Fin fp.Mc), β Φ ≠ (0 : ℂ) → ∃ I ∈ FM Φ, y ∈
    dyadicGridCell A.G I.1 I.2) → (L.at_ y : ColumnHilbert (bf.Lab ⊕ Fin fp.Mc) →
    ColumnHilbert Md) (augmentedMain (fun (Φ : bf.Lab ⊕ Fin fp.Mc) => φ Φ y) L.εP β) =
    ∑ m : Md, (β (L.own m) * L.a m y) • augmentedMode (fun (m : Md) => ψ m y) L.εM m)
    ∧ (∀ (Φ : bf.Lab ⊕ Fin fp.Mc) (y : ℝ), ∑ m : Md with L.own m = Φ, ‖L.a m y‖ ≤ B) ∧
    (∃ (cellOf : Md → ℤ × ℤ) (lamOf : Md → ℝ) (γOf : Md → ℝ), (∀ (m : Md), cellOf m ∈
    FM (L.own m) ∧ (∀ (y : ℝ), L.a m y = (dyadicGridCell A.G (cellOf m).1 (cellOf
    m).2).indicator (fun (_ : ℝ) => L.a m (dyadicGridLeft A.G (cellOf m).1 (cellOf
    m).2)) y) ∧ |lamOf m| * dyadicGridLength A.G (cellOf m).1 ^ (2 : ℕ) ≤ B ∧ ∀ (y :
    ℝ), ψ m y = (↑(ζ y) : ℂ) * (↑((𝐞 : ℝ → Circle) ((↑(slotCoeff l) : ℝ) * centerPhase
    (bf.vtag z) ρ y)) : ℂ) * (↑((𝐞 : ℝ → Circle) (lamOf m * (y - dyadicGridLeft A.G
    (cellOf m).1 (cellOf m).2) ^ (2 : ℕ) + γOf m * (y - dyadicGridLeft A.G (cellOf
    m).1 (cellOf m).2))) : ℂ)) ∧ (∀ (y : ℝ), (↑(Finset.card ({m : Md | y ∈
    dyadicGridCell A.G (cellOf m).1 (cellOf m).2})) : ℝ) ≤ N * (B * ((4 : ℝ) * max (1
    : ℝ) ((4 : ℝ) * B / δc) + (1 : ℝ)) ^ ((4 : ℕ) * dB))) ∧ ∃ (Key : Type) (keyOf : Md
    → Key) (dvOf : Key → ℕ) (θvOf : (k : Key) → Fin (dvOf k) → ℝ) (βOf : Key → ℝ) (σOf
    : (m : Md) → Fin (dvOf (keyOf m) + (bf.vtag z).dim) → ℚ), (∀ (m m' : Md), L.own m
    = L.own m' → cellOf m = cellOf m' → keyOf m = keyOf m') ∧ (∀ (m m' : Md), keyOf m
    = keyOf m' → lamOf m = lamOf m') ∧ (∀ (k : Key), dvOf k ≤ dB) ∧ (∀ (m : Md) (i :
    Fin (dvOf (keyOf m) + (bf.vtag z).dim)), (↑(rationalHeight (σOf m i)) : ℝ) ≤ B *
    ((1 : ℝ) + (4 : ℝ) * ((2 : ℝ) * (↑dB : ℝ) + (1 : ℝ)) * max (1 : ℝ) ((4 : ℝ) * B /
    δc))) ∧ (∀ (m : Md), γOf m = βOf (keyOf m) + ∑ i : Fin (dvOf (keyOf m) + (bf.vtag
    z).dim), (↑(σOf m i) : ℝ) * Fin.append (θvOf (keyOf m)) (bf.vtag z).θ i) ∧ (∀ (m
    m' : Md), keyOf m = keyOf m' → L.own m = L.own m' ∧ cellOf m = cellOf m') ∧ ∀ (m
    m' : Md), keyOf m = keyOf m' → ∃ (a : Fin (dvOf (keyOf m) + (bf.vtag z).dim) → ℚ)
    (b : Fin (dvOf (keyOf m) + (bf.vtag z).dim) → ℚ), (∀ (i : Fin (dvOf (keyOf m) +
    (bf.vtag z).dim)), (↑(rationalHeight (a i)) : ℝ) ≤ B * ((1 : ℝ) + (4 : ℝ) * ((2 :
    ℝ) * (↑dB : ℝ) + (1 : ℝ)) * max (1 : ℝ) ((4 : ℝ) * B / δc))) ∧ (∀ (i : Fin (dvOf
    (keyOf m) + (bf.vtag z).dim)), (↑(rationalHeight (b i)) : ℝ) ≤ B * ((1 : ℝ) + (4 :
    ℝ) * ((2 : ℝ) * (↑dB : ℝ) + (1 : ℝ)) * max (1 : ℝ) ((4 : ℝ) * B / δc))) ∧ γOf m -
    γOf m' = ∑ i : Fin (dvOf (keyOf m) + (bf.vtag z).dim), (↑((a - b) i) : ℝ) *
    Fin.append (θvOf (keyOf m)) (bf.vtag z).θ i) ∧ ∀ (y : ℝ), (↑(Finset.card ({m : Md
    | L.a m y ≠ (0 : ℂ)})) : ℝ) ≤ N * (B * ((4 : ℝ) * max (1 : ℝ) ((4 : ℝ) * B / δc) +
    (1 : ℝ)) ^ ((4 : ℕ) * dB))




private theorem mainAttemptLift_conclusion_8 : MainAttemptLiftConclusion8Statement := by
  classical
  intro κ c₀ D A bf fp l s d cs G j z g dB hdim δ ρ H δc N hδcN FM X K Ny hNy coef lam γ dv θv σ β
    hγ hdv B hσh hlam hB0 ζ cell a₀ φ w hw ψ am E sf qf ham hsfm hsf1 hqm hmodeK hqle hqsum εM
    hεMpos hweights bnd hcellcount
  have hσB : ∀ (k : {k // k ∈ K}) (i : Ny k) j', (rationalHeight (σ k i j') : ℝ) ≤
      B * (1 + 4 * (2 * dB + 1) * max 1 (4 * B / δc)) := by
    intro k i j'
    refine (hσh k i j').trans (mul_le_mul_of_nonneg_left ?_ hB0)
    have h1 : ((dv k + (bf.vtag z).dim : ℕ) : ℝ) ≤ 2 * dB := by
      have := hdv k; have := hdim z
      exact_mod_cast (by omega : dv k + (bf.vtag z).dim ≤ 2 * dB)
    nlinarith only [le_max_left (1 : ℝ) (4 * B / δc), h1]
  refine ⟨fun m => m.1.1.2, fun m => lam m.1, fun m => γ m.1 m.2, fun m => ⟨hmodeK m,
    fun y => ?_, hlam m.1, fun y => rfl⟩, hcellcount, {k // k ∈ K}, fun m => m.1,
    dv, θv, β, fun m => σ m.1 m.2, fun m m' hown hcell => ?_, fun m m' hk => ?_, hdv,
    fun m i => hσB m.1 m.2 i, fun m => hγ m.1 m.2, fun m m' hk => ?_, fun m m' hk => ?_⟩
  · change am m y = (cell m.1).indicator (fun _ => am m (a₀ m.1)) y
    have hl : a₀ m.1 ∈ cell m.1 := dyadicGridCell_left_mem A.G _ _
    simp only [am, Set.indicator_of_mem hl]
  · exact Subtype.ext (Sigma.ext hown (heq_of_eq hcell))
  · exact congrArg lam hk
  · exact ⟨congrArg (fun k : {k // k ∈ K} => k.1.1) hk,
      congrArg (fun k : {k // k ∈ K} => k.1.2) hk⟩
  · obtain ⟨k, i⟩ := m
    obtain ⟨k', i'⟩ := m'
    simp only at hk
    subst hk
    refine ⟨σ k i, σ k i', hσB k i, hσB k i', ?_⟩
    change γ k i - γ k i' = _
    rw [hγ k i, hγ k i']
    simp only [Pi.sub_apply, Rat.cast_sub, sub_mul, Finset.sum_sub_distrib]
    ring



private theorem mainAttemptLift_hcellcount : MainAttemptLiftHcellcountStatement := by
  classical
  intro κ c₀ D A bf fp l s d cs G j g dB H δc N FM X K Ny hNy B cell E hmodeK hmatched bnd hbnd0
    hNk y
  rw [Finset.card_eq_sum_card_fiberwise (f := fun m => m.1.1.1) (t := Finset.univ)
    (fun _ _ => Finset.mem_univ _)]
  push_cast
  set! Mt := Finset.univ.filter fun Φ => y ∈ E Φ
  rw [← Finset.sum_subset (Finset.subset_univ Mt) (fun Φ _ hΦ => by
    have hy : y ∉ E Φ := fun hy => hΦ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩)
    rw [Nat.cast_eq_zero, Finset.card_eq_zero]
    refine Finset.eq_empty_of_forall_notMem fun m hm => ?_
    obtain ⟨hm1, hm2⟩ := Finset.mem_filter.mp hm
    exact hy (Set.mem_iUnion₂.mpr ⟨m.1.1.2, hm2 ▸ hmodeK m, (Finset.mem_filter.mp hm1).2⟩))]
  have hfib : ∀ Φ ∈ Mt, (((Finset.univ.filter fun m : (Σ k : {k // k ∈ K}, Ny k) =>
      y ∈ cell m.1).filter fun m => m.1.1.1 = Φ).card : ℝ) ≤ bnd := by
    intro Φ hΦ
    obtain ⟨I₀, hI₀, hyI⟩ := Set.mem_iUnion₂.mp (Finset.mem_filter.mp hΦ).2
    set! k₀ : {k // k ∈ K} := ⟨⟨Φ, I₀⟩, Finset.mem_sigma.mpr ⟨Finset.mem_univ _, hI₀⟩⟩
    have hsub : ((Finset.univ.filter fun m : (Σ k : {k // k ∈ K}, Ny k) =>
        y ∈ cell m.1).filter fun m => m.1.1.1 = Φ) ⊆
        (Finset.univ : Finset (Ny k₀)).map ⟨fun i => (⟨k₀, i⟩ : Σ k : {k // k ∈ K}, Ny k),
          fun i i' h => by simpa using h⟩ := by
      intro m hm
      obtain ⟨hm1, hm2⟩ := Finset.mem_filter.mp hm
      have hyc := (Finset.mem_filter.mp hm1).2
      have hkI : m.1.1.2 ∈ FM Φ := hm2 ▸ hmodeK m
      have heq : m.1.1.2 = I₀ := fp.firstCell_unique cs l s G j d hkI hI₀ hyc hyI
      have hk : m.1 = k₀ := Subtype.ext (Sigma.ext hm2 (heq_of_eq heq))
      rcases m with ⟨k, i⟩
      simp only at hk
      subst hk
      exact Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩
    refine (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans ?_
    rw [Finset.card_map, Finset.card_univ]; exact hNk k₀
  refine (Finset.sum_le_sum hfib).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (hmatched y) hbnd0



private theorem mainAttemptLift_stage_2 : MainAttemptLiftStage2Statement := by
  classical
  intro κ c₀ D A bf fp l s d cs G j z g dB hdim δ ρ H δc N hδcN FM X K Ny hNy coef lam γ dv θv σ β
    hγ hdv B hσh hlam hB0 ζ cell a₀ φ w hw ψ am E sf qf hψm ham hsfm hsf1 hqm hmodeK ham0 hoff
    hqle hqsum εM hεMpos hεMinv hεMle hweights hcoefsum bnd hcellcount
  have hqform : ∀ Φ y, (∃ I ∈ FM Φ, y ∈ dyadicGridCell A.G I.1 I.2) →
      qf Φ y = ∑ m ∈ Finset.univ.filter (fun m : (Σ k : {k // k ∈ K}, Ny k) => m.1.1.1 = Φ),
        am m y * ψ m y - sf y * φ Φ y := fun Φ y hy => by
    simp only [qf]
    obtain ⟨I, hI, hyI⟩ := hy
    rw [Set.indicator_of_mem (Set.mem_iUnion₂.mpr ⟨I, hI, hyI⟩)]
  refine ⟨Σ k : {k // k ∈ K}, Ny k, inferInstance,
    { own := fun m => m.1.1.1
      s := sf
      q := qf
      a := am
      εP := w
      εM := εM
      δ := δc
      a_meas := ham
      s_meas := hsfm
      s_le := hsf1
      q_meas := hqm
      q_le := hqle
      εP_pos := hw
      q_sum := fun y => (hqsum y).trans hδcN
      εM_nonneg := fun m => (hεMpos m).le
      weights := hweights }, ψ,
    fun _ => rfl, rfl, hεMpos, hεMle, hεMinv, hqsum, fun _ => rfl, hψm, ?_, hqform, ?_, hcoefsum,
    ?_,
    fun y => ?_⟩
  · intro Φ y hy
    have hy' : y ∉ E Φ := fun h => by
      obtain ⟨I, hI, hyI⟩ := Set.mem_iUnion₂.mp h
      exact hy I hI hyI
    refine ⟨?_, fun m hm => hoff Φ y hy' m hm⟩
    change qf Φ y = 0
    simp only [qf]; rw [Set.indicator_of_notMem hy']
  · intro y β hβ
    let _ : DecidableEq (Σ k : {k // k ∈ K}, Ny k) := fun a b => Classical.propDecidable (a = b)
    exact modeLift_synthesis_supp (fun m : (Σ k : {k // k ∈ K}, Ny k) => m.1.1.1) (sf y)
      (fun Φ => φ Φ y) (fun m => am m y) (fun m => ψ m y) w hw εM (fun Φ => qf Φ y) β
      fun Φ hΦ => hqform Φ y (hβ Φ hΦ)
  · expose_names
    exact @mainAttemptLift_conclusion_8 κ c₀ D A bf fp l s d cs G j z g dB hdim δ ρ H δc N hδcN Ny
      hNy coef lam γ dv θv σ β hγ hdv hσh hlam hB0 hw ham hsfm hsf1 hqm hmodeK hqle hqsum hεMpos
      hweights hcellcount
  · -- the number of modes alive at `y`
    change ((Finset.univ.filter fun m => am m y ≠ 0).card : ℝ) ≤ N * bnd
    refine le_trans (Nat.cast_le.mpr (Finset.card_le_card fun m hm => ?_)) (hcellcount y)
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    by_contra hc
    exact (Finset.mem_filter.mp hm).2 (ham0 m y hc)



private theorem mainAttemptLift_stage_1 : MainAttemptLiftStage1Statement := by
  classical
  intro κ c₀ D A bf fp l s d cs hcs G j z g dB hdim δ hδ hδ' ρ H δc hδc N hN0 hN hδcN FM X K Ny
    hNy coef lam γ dv θv σ β hγ hdv B hcount hσh hsum hlam hB0 ζ cell a₀ φ w hw hwinv ψ am E sf qf
    hψm ham hsfm hsf1 hqm hmodeK ham0 hsred hoff hqle
  have hmatched : ∀ y, ((Finset.univ.filter fun Φ => y ∈ E Φ).card : ℝ) ≤ N := fun y => by
    have h := fp.card_matched_le cs hcs l s G j d hN0 hN y
    refine le_trans (le_of_eq ?_) h
    congr 2
    ext Φ
    simp only [E, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_iUnion₂, exists_prop]
    rfl
  have hqsum : ∀ y, ∑ Φ, ‖qf Φ y‖ ^ 2 / w Φ ≤ δc ^ 2 * N * A.colBudget ^ 2 := fun y => by
    set! Mt := Finset.univ.filter fun Φ => y ∈ E Φ
    rw [← Finset.sum_subset (Finset.subset_univ Mt) (fun Φ _ hΦ => by
      have hy : y ∉ E Φ := fun hy => hΦ (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩)
      simp only [qf]; rw [Set.indicator_of_notMem hy, norm_zero]; ring)]
    have hterm : ∀ Φ, ‖qf Φ y‖ ^ 2 / w Φ ≤ δc ^ 2 * A.colBudget ^ 2 := fun Φ => by
      rw [div_eq_mul_inv]
      exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (hqle Φ y) 2) (hwinv Φ)
        (inv_nonneg.mpr (hw Φ).le) (sq_nonneg _)
    refine (Finset.sum_le_card_nsmul _ _ _ fun Φ _ => hterm Φ).trans ?_
    rw [nsmul_eq_mul]
    have := hmatched y
    have h0 : 0 ≤ δc ^ 2 * A.colBudget ^ 2 := by positivity
    nlinarith only [this, h0]
  -- local mode weights
  set! εM : (Σ k : {k // k ∈ K}, Ny k) → ℝ := fun m =>
    w m.1.1.1 * (∑ i, ‖coef m.1 i‖ ^ 2 + 1)⁻¹
  have hεMpos : ∀ m, 0 < εM m := fun m => by
    have := hw m.1.1.1; simp only [εM]; positivity
  have hcoef2 : ∀ k, ∑ i, ‖coef k i‖ ^ 2 ≤ B ^ 2 := fun k =>
    (Finset.sum_sq_le_sq_sum_of_nonneg fun i _ => norm_nonneg _).trans
      (pow_le_pow_left₀ (Finset.sum_nonneg fun i _ => norm_nonneg _) (hsum k) 2)
  have hεMinv : ∀ m, (εM m)⁻¹ ≤ A.colBudget ^ 2 * (B ^ 2 + 1) := fun m => by
    simp only [εM]
    rw [mul_inv, inv_inv]
    exact mul_le_mul (hwinv _) (by linarith [hcoef2 m.1]) (by positivity) (by positivity)
  have hεMle : ∀ m, εM m ≤ w m.1.1.1 := fun m => by
    simp only [εM]
    refine mul_le_of_le_one_right (hw _).le (inv_le_one_of_one_le₀ ?_)
    have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => sq_nonneg ‖coef m.1 i‖)
    linarith
  have hweights : ∀ Φ y, ∑ m ∈ Finset.univ.filter
      (fun m : (Σ k : {k // k ∈ K}, Ny k) => m.1.1.1 = Φ), εM m * ‖am m y‖ ^ 2 ≤ w Φ := by
    intro Φ y
    by_cases hy : y ∈ E Φ
    · obtain ⟨I₀, hI₀, hyI⟩ := Set.mem_iUnion₂.mp hy
      rw [hsred Φ y I₀ hI₀ hyI (fun m => εM m * ‖am m y‖ ^ 2)
        (fun m hm => by rw [ham0 m y hm, norm_zero]; ring)]
      set k₀ : {k // k ∈ K} := ⟨⟨Φ, I₀⟩, Finset.mem_sigma.mpr ⟨Finset.mem_univ _, hI₀⟩⟩
      have hyk : y ∈ cell k₀ := hyI
      have e : ∑ i, εM ⟨k₀, i⟩ * ‖am ⟨k₀, i⟩ y‖ ^ 2 =
          w Φ * ((∑ i, ‖coef k₀ i‖ ^ 2) * (∑ i, ‖coef k₀ i‖ ^ 2 + 1)⁻¹) := by
        rw [Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        change w Φ * (∑ i, ‖coef k₀ i‖ ^ 2 + 1)⁻¹ * ‖am ⟨k₀, i⟩ y‖ ^ 2 = _
        simp only [am, Set.indicator_of_mem hyk]
        ring
      rw [e]
      have h1 : (∑ i, ‖coef k₀ i‖ ^ 2) * (∑ i, ‖coef k₀ i‖ ^ 2 + 1)⁻¹ ≤ 1 := by
        have h0 : 0 ≤ ∑ i, ‖coef k₀ i‖ ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
        rw [mul_inv_le_iff₀ (by linarith)]; linarith
      calc w Φ * _ ≤ w Φ * 1 := mul_le_mul_of_nonneg_left h1 (hw Φ).le
        _ = w Φ := mul_one _
    · rw [Finset.sum_eq_zero fun m hm => by
        rw [hoff Φ y hy m (Finset.mem_filter.mp hm).2, norm_zero]; ring]
      exact (hw Φ).le
  -- the absolute coefficient sum of the modes of `Φ` at `y`
  have hcoefsum : ∀ Φ y, ∑ m ∈ Finset.univ.filter
      (fun m : (Σ k : {k // k ∈ K}, Ny k) => m.1.1.1 = Φ), ‖am m y‖ ≤ B := by
    intro Φ y
    by_cases hy : y ∈ E Φ
    · obtain ⟨I₀, hI₀, hyI⟩ := Set.mem_iUnion₂.mp hy
      rw [hsred Φ y I₀ hI₀ hyI (fun m => ‖am m y‖) (fun m hm => by rw [ham0 m y hm, norm_zero])]
      set k₀ : {k // k ∈ K} := ⟨⟨Φ, I₀⟩, Finset.mem_sigma.mpr ⟨Finset.mem_univ _, hI₀⟩⟩
      have hyk : y ∈ cell k₀ := hyI
      simp only [am, Set.indicator_of_mem hyk]
      exact hsum k₀
    · rw [Finset.sum_eq_zero fun m hm => by rw [hoff Φ y hy m (Finset.mem_filter.mp hm).2,
        norm_zero]]
      exact hB0
  -- the number of modes whose first-match cell contains `y`
  set bnd : ℝ := B * (4 * max 1 (4 * B / δc) + 1) ^ (4 * dB)
  have hbase : (1 : ℝ) ≤ 4 * max 1 (4 * B / δc) + 1 := by
    have := le_max_left (1 : ℝ) (4 * B / δc); linarith
  have hbnd0 : 0 ≤ bnd := mul_nonneg hB0 (pow_nonneg (by linarith) _)
  have hNk : ∀ k, (Fintype.card (Ny k) : ℝ) ≤ bnd := fun k =>
    (hcount k).trans (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hbase (by
      have := hdv k; have := hdim z; omega)) hB0)
  have hcellcount : ∀ y, ((Finset.univ.filter fun m : (Σ k : {k // k ∈ K}, Ny k) =>
      y ∈ cell m.1).card : ℝ) ≤ N * bnd := by
    expose_names
    exact @mainAttemptLift_hcellcount κ c₀ D A bf fp l s d cs G j g dB H δc N Ny hNy hmodeK
      hmatched hbnd0 hNk
  expose_names
  exact @mainAttemptLift_stage_2 κ c₀ D A bf fp l s d cs G j z g dB hdim δ ρ H δc N hδcN Ny hNy
    coef lam γ dv θv σ β hγ hdv hσh hlam hB0 hw hψm ham hsfm hsf1 hqm hmodeK ham0 hoff hqle hqsum
    hεMpos hεMinv hεMle hweights hcoefsum hcellcount


open Classical in
/-- Blueprint line 1932 (`eq:modes` and the lift `R_(l,G)`) on the main columns of a role: the
augmented modes `ψ_m = ζ^ρ e(c_l p_ρ) e(λ_m (y - a)² + γ_m (y - a))` of the first-match
expansions of all primaries `Φ` at their first-match cells, with private indices distinct across
primaries and branches, and the pointwise linear map with physical coordinate
`(ζ^ρ)² F_phys + Σ_Φ F_Φ / √ε_Φ q_Φ` (`q_Φ = Σ_m a_(Φ,m) (ψ_m)_phys - (ζ^ρ)² φ_Φ` on the first-match
branches of `Φ`, zero before the match) and mode coordinates `√ε_m a_(Φ,m) F_Φ / √ε_Φ`. The
primary weights are the private weights `ε_Φ` of the main columns; the mode weights are chosen
locally, `ε_m = ε_Φ / (Σ_m' |a_(Φ,m')|² + 1)`, so that the private map has squared norm at most one
and `1 / ε_m ≤ colBudget² (exp(D X^D)² + 1)` (`log (1/ε_m) ≤ P^C`). The physical correction
satisfies `Σ_Φ |q_Φ|² / ε_Φ ≤ δ_c² N colBudget²` pointwise, `N` bounding the main labels at the
cells (`δ_c D_m^C`); with `δ_c² N colBudget² ≤ 1` this is the absolute norm bound of the lift. -/
theorem mainAttemptLift (κ : LocalKernelClass) (c₀ : ℕ) :
    ∃ D : ℕ, 1 ≤ D ∧ ∀ (A : ActiveSetup κ c₀) (bf : A.BasicFamilies) (fp : bf.FamParams)
      (l : Fin 4) (s : List (CatCol bf.Vtx))
      (_hT : ∀ e ∈ s, ∃ R ∈ residueBox (bf.vtag e.tag).dim 9, ∃ γ : ℝ,
        e = templateCol (bf.vtag e.tag) l R γ e.birth e.rank e.tag)
      (_htag : ∀ e ∈ s, bf.occAvail e.tag.2.1 e.tag.1) (d : bf.Vtx)
      (cs : Finset (ℤ × ℤ)) (_hcs : cs ⊆ A.cells) {G : bf.Grp} {j : ℕ}
      {ρ₀ : Fin fp.K.d0} {z : bf.Vtx} {g : ℤ} (_hG : G.2.1 = some (ρ₀, z, g))
      (_hHed : 2 ≤ fp.Hed) {dB : ℕ} (_hdim : ∀ w : bf.Vtx, (bf.vtag w).dim ≤ dB)
      (_hC : ∀ (w : bf.Vtx) a c, (rationalHeight ((bf.vtag w).C a c) : ℝ) ≤ fp.Hed)
      {δ : ℝ} (_hδ : 0 < δ) (_hδ' : δ < 1 / 4) (ρ : Fin (bf.vtag z).dim → ℝ)
      (_hρ : ∀ i, ρ i ∈ Set.Icc (0 : ℝ) 1) {H : ℝ} (_hHs : A.Hsrc ≤ H)
      (_hdz : ((bf.vtag z).dim : ℝ) ≤ Real.log H)
      (_hCz : ∀ i k, (chartRationalHeight ((((-slotCoeff l : ℤ) : ℚ) • (bf.vtag z).C) i k) : ℝ) ≤
        H)
      (_hHδ : ((bf.vtag z).dim : ℝ) * (bumpConst * 8 ^ 32 * (2 / δ)) ≤ H) {δc : ℝ} (_hδc : 0 < δc)
      {N : ℝ} (_hN0 : 0 ≤ N) (_hN : ∀ I ∈ A.cells,
        ((mainLabels A.G fp.Mc (bf.origCols l) s I (fp.brank j)).card : ℝ) ≤ N)
      (_hδcN : δc ^ 2 * N * A.colBudget ^ 2 ≤ 1),
      let FM := fp.firstCells cs l s G j d
      let X := 1 + Real.log (chartTranslationBudget (H ^ 6)) +
        Real.log (3 * fp.ballEdgeH dB (fp.ballRadius g (fp.bbase j + fp.P)))
      ∃ (Md : Type) (_ : Fintype Md) (L : LiftData (bf.Lab ⊕ Fin fp.Mc) Md)
        (ψ : Md → ℝ → ℂ),
        (∀ Φ, L.εP Φ = mainWeight fp.Mc (bf.origCols l) Φ) ∧ L.δ = δc ∧ (∀ m, 0 < L.εM m) ∧
        (∀ m, L.εM m ≤ L.εP (L.own m)) ∧
        (∀ m, (L.εM m)⁻¹ ≤ A.colBudget ^ 2 * (Real.exp (D * X ^ D) ^ 2 + 1)) ∧
        (∀ y, ∑ Φ, ‖L.q Φ y‖ ^ 2 / L.εP Φ ≤ δc ^ 2 * N * A.colBudget ^ 2) ∧
        (∀ y, L.s y = ((centerCut (bf.vtag z) δ ρ y : ℝ) : ℂ) ^ 2) ∧
        (∀ m, Measurable (ψ m)) ∧
        (∀ Φ y, (∀ I ∈ FM Φ, y ∉ dyadicGridCell A.G I.1 I.2) →
          L.q Φ y = 0 ∧ ∀ m, L.own m = Φ → L.a m y = 0) ∧
        (∀ Φ y, (∃ I ∈ FM Φ, y ∈ dyadicGridCell A.G I.1 I.2) →
          L.q Φ y = ∑ m ∈ Finset.univ.filter (fun m => L.own m = Φ), L.a m y * ψ m y -
            L.s y * mainScalar fp.Mc (bf.origCols l) s Φ y) ∧
        (∀ y (β : bf.Lab ⊕ Fin fp.Mc → ℂ),
          (∀ Φ, β Φ ≠ 0 → ∃ I ∈ FM Φ, y ∈ dyadicGridCell A.G I.1 I.2) →
          L.at_ y (augmentedMain (fun Φ => mainScalar fp.Mc (bf.origCols l) s Φ y) L.εP β) =
            ∑ m, (β (L.own m) * L.a m y) • augmentedMode (fun m => ψ m y) L.εM m) ∧
        (∀ Φ y, ∑ m ∈ Finset.univ.filter (fun m => L.own m = Φ), ‖L.a m y‖ ≤
          Real.exp (D * X ^ D)) ∧
        (∃ (cellOf : Md → ℤ × ℤ) (lamOf γOf : Md → ℝ),
          (∀ m, cellOf m ∈ FM (L.own m) ∧
            (∀ y, L.a m y = (dyadicGridCell A.G (cellOf m).1 (cellOf m).2).indicator
              (fun _ => L.a m (dyadicGridLeft A.G (cellOf m).1 (cellOf m).2)) y) ∧
            |lamOf m| * dyadicGridLength A.G (cellOf m).1 ^ 2 ≤ Real.exp (D * X ^ D) ∧
            ∀ y, ψ m y = (centerCut (bf.vtag z) δ ρ y : ℂ) *
              (Real.fourierChar ((slotCoeff l : ℝ) * centerPhase (bf.vtag z) ρ y) : ℂ) *
              (Real.fourierChar (lamOf m * (y - dyadicGridLeft A.G (cellOf m).1 (cellOf m).2) ^ 2 +
                γOf m * (y - dyadicGridLeft A.G (cellOf m).1 (cellOf m).2)) : ℂ)) ∧
          (∀ y, ((Finset.univ.filter fun m =>
              y ∈ dyadicGridCell A.G (cellOf m).1 (cellOf m).2).card : ℝ) ≤ N *
            (Real.exp (D * X ^ D) * (4 * max 1 (4 * Real.exp (D * X ^ D) / δc) + 1) ^ (4 * dB))) ∧
          ∃ (Key : Type) (keyOf : Md → Key) (dvOf : Key → ℕ) (θvOf : ∀ k, Fin (dvOf k) → ℝ)
            (βOf : Key → ℝ) (σOf : ∀ m, Fin (dvOf (keyOf m) + (bf.vtag z).dim) → ℚ),
            (∀ m m', L.own m = L.own m' → cellOf m = cellOf m' → keyOf m = keyOf m') ∧
            (∀ m m', keyOf m = keyOf m' → lamOf m = lamOf m') ∧ (∀ k, dvOf k ≤ dB) ∧
            (∀ m i, (rationalHeight (σOf m i) : ℝ) ≤ Real.exp (D * X ^ D) *
              (1 + 4 * (2 * dB + 1) * max 1 (4 * Real.exp (D * X ^ D) / δc))) ∧
            (∀ m, γOf m = βOf (keyOf m) +
              ∑ i, (σOf m i : ℝ) * Fin.append (θvOf (keyOf m)) (bf.vtag z).θ i) ∧
            (∀ m m', keyOf m = keyOf m' → L.own m = L.own m' ∧ cellOf m = cellOf m') ∧
            ∀ m m', keyOf m = keyOf m' → ∃ a b : Fin (dvOf (keyOf m) + (bf.vtag z).dim) → ℚ,
              (∀ i, (rationalHeight (a i) : ℝ) ≤ Real.exp (D * X ^ D) *
                (1 + 4 * (2 * dB + 1) * max 1 (4 * Real.exp (D * X ^ D) / δc))) ∧
              (∀ i, (rationalHeight (b i) : ℝ) ≤ Real.exp (D * X ^ D) *
                (1 + 4 * (2 * dB + 1) * max 1 (4 * Real.exp (D * X ^ D) / δc))) ∧
              γOf m - γOf m' =
                ∑ i, ((a - b) i : ℝ) * Fin.append (θvOf (keyOf m)) (bf.vtag z).θ i) ∧
        ∀ y, ((Finset.univ.filter fun m => L.a m y ≠ 0).card : ℝ) ≤ N *
          (Real.exp (D * X ^ D) * (4 * max 1 (4 * Real.exp (D * X ^ D) / δc) + 1) ^ (4 * dB)) := by
  obtain ⟨D, hD, hfin⟩ := mainFirstMatch_finite κ c₀
  refine ⟨D, hD, ?_⟩
  intro A bf fp l s hT htag d cs hcs G j ρ₀ z g hG hHed dB hdim hC δ hδ hδ' ρ hρ H hHs hdz hCz
    hHδ δc hδc N hN0 hN hδcN FM X
  set! K : Finset (Σ _ : bf.Lab ⊕ Fin fp.Mc, ℤ × ℤ) := Finset.univ.sigma FM
  have hK : ∀ k : {k // k ∈ K}, k.1.2 ∈ FM k.1.1 := fun k => (Finset.mem_sigma.mp k.2).2
  have hK' : ∀ k : {k // k ∈ K}, k.1.2 ∈ A.cells ∧ k.1.1 ∈ fp.primaries l s G j d k.1.2 :=
    fun k => by
      have h := Finset.mem_filter.mp (mem_maxCells.mp (hK k)).1
      exact ⟨hcs h.1, h.2⟩
  have hdata := fun k : {k // k ∈ K} => hfin A bf fp l s hT htag d (hK' k).1 (hK' k).2 hG hHed
    hdim hC hδ hδ' ρ hρ hHs hdz hCz hHδ hδc
  choose Ny hNy coef lam γ dv θv σ β hγ hdv hcount hσh hsum hlam happrox using hdata
  set B : ℝ := Real.exp (D * X ^ D)
  have hB0 : 0 ≤ B := (Real.exp_pos _).le
  set ζ : ℝ → ℝ := centerCut (bf.vtag z) δ ρ
  set! cell : {k // k ∈ K} → Set ℝ := fun k => dyadicGridCell A.G k.1.2.1 k.1.2.2
  set! a₀ : {k // k ∈ K} → ℝ := fun k => dyadicGridLeft A.G k.1.2.1 k.1.2.2
  set φ : bf.Lab ⊕ Fin fp.Mc → ℝ → ℂ := mainScalar fp.Mc (bf.origCols l) s
  set w : bf.Lab ⊕ Fin fp.Mc → ℝ := mainWeight fp.Mc (bf.origCols l)
  have hw : ∀ Φ, 0 < w Φ := fun Φ => by
    rcases Φ with x | n
    · exact (bf.origCols l).weight_pos x
    · exact one_pos
  have hwinv : ∀ Φ, (w Φ)⁻¹ ≤ A.colBudget ^ 2 := fun Φ => bf.inv_mainWeight_le l Φ
  have hφm : ∀ Φ, Measurable (φ Φ) := fun Φ => by
    rcases Φ with x | n
    · exact (bf.P x.1 x.2.1).Ψ.D.scalar_measurable x.2.2
    · exact catAtom_measurable s n
  set! ψ : (Σ k : {k // k ∈ K}, Ny k) → ℝ → ℂ := fun m y => (ζ y : ℂ) *
    (Real.fourierChar ((slotCoeff l : ℝ) * centerPhase (bf.vtag z) ρ y) : ℂ) *
    (Real.fourierChar (lam m.1 * (y - a₀ m.1) ^ 2 + γ m.1 m.2 * (y - a₀ m.1)) : ℂ)
  set! am : (Σ k : {k // k ∈ K}, Ny k) → ℝ → ℂ := fun m => (cell m.1).indicator fun _ =>
    coef m.1 m.2
  set! E : bf.Lab ⊕ Fin fp.Mc → Set ℝ := fun Φ => ⋃ I ∈ FM Φ, dyadicGridCell A.G I.1 I.2
  set! sf : ℝ → ℂ := fun y => ((ζ y : ℝ) : ℂ) ^ 2
  set! qf : bf.Lab ⊕ Fin fp.Mc → ℝ → ℂ := fun Φ => (E Φ).indicator fun y =>
    ∑ m ∈ Finset.univ.filter (fun m : (Σ k : {k // k ∈ K}, Ny k) => m.1.1.1 = Φ),
      am m y * ψ m y - sf y * φ Φ y
  have hζm : Measurable ζ := centerCut_measurable _ _ _
  have hζ1 : ∀ y, ‖(ζ y : ℂ)‖ ≤ 1 := fun y => by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (centerCut_mem _ _ _ y).1]
    exact (centerCut_mem _ _ _ y).2
  have hψm : ∀ m, Measurable (ψ m) := fun m => by
    refine ((Complex.measurable_ofReal.comp hζm).mul ?_).mul ?_
    · exact measurable_fourierChar_comp
        (measurable_const.mul (centerPhase_measurable _ _))
    · exact measurable_fourierChar_comp (by fun_prop)
  have ham : ∀ m, Measurable (am m) := fun m =>
    measurable_const.indicator (dyadicGridCell_measurable _ _ _)
  have hEm : ∀ Φ, MeasurableSet (E Φ) := fun Φ =>
    Finset.measurableSet_biUnion _ fun I _ => dyadicGridCell_measurable _ _ _
  have hsfm : Measurable sf := (Complex.measurable_ofReal.comp hζm).pow_const 2
  have hsf1 : ∀ y, ‖sf y‖ ≤ 1 := fun y => by
    simp only [sf, norm_pow]; exact pow_le_one₀ (norm_nonneg _) (hζ1 y)
  have hqm : ∀ Φ, Measurable (qf Φ) := fun Φ => by
    refine Measurable.indicator ?_ (hEm Φ)
    exact (Finset.measurable_sum _ fun m _ => (ham m).mul (hψm m)).sub (hsfm.mul (hφm Φ))
  -- a mode of `Φ` lives on a first-match cell of `Φ`
  have hmodeK : ∀ m : (Σ k : {k // k ∈ K}, Ny k), m.1.1.2 ∈ FM m.1.1.1 := fun m => hK m.1
  have ham0 : ∀ m y, y ∉ cell m.1 → am m y = 0 := fun m y hy => by
    simp only [am]; rw [Set.indicator_of_notMem hy]
  -- the sum over the modes of `Φ` at `y` reduces to the first-match branch of `Φ` at `y`
  have hsred : ∀ {R : Type} [AddCommMonoid R] (Φ : bf.Lab ⊕ Fin fp.Mc) (y : ℝ) (I₀ : ℤ × ℤ)
      (hI₀ : I₀ ∈ FM Φ) (_hy : y ∈ dyadicGridCell A.G I₀.1 I₀.2)
      (F : (Σ k : {k // k ∈ K}, Ny k) → R), (∀ m, y ∉ cell m.1 → F m = 0) →
      ∑ m ∈ Finset.univ.filter (fun m : (Σ k : {k // k ∈ K}, Ny k) => m.1.1.1 = Φ), F m =
        ∑ i, F ⟨⟨⟨Φ, I₀⟩, Finset.mem_sigma.mpr ⟨Finset.mem_univ _, hI₀⟩⟩, i⟩ := by
    intro R _ Φ y I₀ hI₀ hy F hF
    set k₀ : {k // k ∈ K} := ⟨⟨Φ, I₀⟩, Finset.mem_sigma.mpr ⟨Finset.mem_univ _, hI₀⟩⟩
    rw [Finset.sum_filter, Fintype.sum_sigma, Finset.sum_eq_single k₀]
    · exact Finset.sum_congr rfl fun i _ => by simp [k₀]
    · intro k _ hk
      refine Finset.sum_eq_zero fun i _ => ?_
      split_ifs with h
      · have hkI : k.1.2 ∈ FM Φ := h ▸ hK k
        have hyk : y ∉ cell k := fun hyk => hk (Subtype.ext (Sigma.ext h (heq_of_eq
          (fp.firstCell_unique cs l s G j d hkI hI₀ hyk hy))))
        exact hF _ hyk
      · rfl
    · intro h; exact absurd (Finset.mem_univ k₀) h
  -- off the first-match branches of `Φ`, the modes of `Φ` vanish
  have hoff : ∀ Φ y, y ∉ E Φ → ∀ m, m.1.1.1 = Φ → am m y = 0 := fun Φ y hy m hm => by
    refine ham0 m y fun hyc => hy (Set.mem_iUnion₂.mpr ⟨m.1.1.2, hm ▸ hmodeK m, hyc⟩)
  have hqle : ∀ Φ y, ‖qf Φ y‖ ≤ δc := fun Φ y => by
    by_cases hy : y ∈ E Φ
    · simp only [qf]; rw [Set.indicator_of_mem hy]
      obtain ⟨I₀, hI₀, hyI⟩ := Set.mem_iUnion₂.mp hy
      rw [hsred Φ y I₀ hI₀ hyI (fun m => am m y * ψ m y)
        (fun m hm => by rw [ham0 m y hm, zero_mul])]
      set k₀ : {k // k ∈ K} := ⟨⟨Φ, I₀⟩, Finset.mem_sigma.mpr ⟨Finset.mem_univ _, hI₀⟩⟩
      have hyk : y ∈ cell k₀ := hyI
      have h := happrox k₀ y hyI
      set! u : ℂ := (Real.fourierChar ((slotCoeff l : ℝ) * centerPhase (bf.vtag z) ρ y) : ℂ)
      set u' : ℂ := (Real.fourierChar (-(slotCoeff l : ℝ) * centerPhase (bf.vtag z) ρ y) : ℂ)
      have huw : u * u' = 1 := by
        simp only [u, u']
        rw [← Circle.coe_mul, ← AddChar.map_add_eq_mul, show (slotCoeff l : ℝ) *
          centerPhase (bf.vtag z) ρ y + -(slotCoeff l : ℝ) * centerPhase (bf.vtag z) ρ y = 0 by
          ring, AddChar.map_zero_eq_one, Circle.coe_one]
      have hu : ‖u‖ = 1 := Circle.norm_coe _
      have e : ∑ i, am ⟨k₀, i⟩ y * ψ ⟨k₀, i⟩ y - sf y * φ Φ y =
          ((ζ y : ℂ) * u) * (∑ i, coef k₀ i * (Real.fourierChar (lam k₀ * (y - a₀ k₀) ^ 2 +
            γ k₀ i * (y - a₀ k₀)) : ℂ) - φ Φ y * ((ζ y : ℂ) * u')) := by
        simp only [am, Set.indicator_of_mem hyk, ψ, sf, mul_sub, Finset.mul_sum]
        congr 1
        · exact Finset.sum_congr rfl fun i _ => by ring
        · linear_combination (-(φ Φ y) * (ζ y : ℂ) ^ 2) * huw
      rw [e, norm_mul, norm_mul, hu, mul_one]
      exact (mul_le_mul (hζ1 y) h (norm_nonneg _) zero_le_one).trans (le_of_eq (one_mul _))
    · simp only [qf]; rw [Set.indicator_of_notMem hy, norm_zero]; exact hδc.le
  -- the primaries matched at `y`
  expose_names
  exact @mainAttemptLift_stage_1 κ c₀ D A bf fp l s d cs hcs G j z g dB hdim δ hδ hδ' ρ H δc hδc N
    hN0 hN hδcN Ny hNy coef lam γ dv θv σ β hγ hdv hcount hσh hsum hlam hB0 hw hwinv hψm ham hsfm
    hsf1 hqm hmodeK ham0 hsred hoff hqle

end ActiveSetup.BasicFamilies.FamParams

/-! ## The mode budget `D_*` (blueprint line 1934) -/

/-! ### The clearing integer `Q₀` (blueprint lines 1893 and 1934) -/

/-- The clearing integer of a rational matrix: the product of the denominators of its entries
(blueprint line 1893: "an integer `Q₀` in the main budget clearing `C_z`"). -/
def clearInt {d : ℕ} (C : Matrix (Fin d) (Fin d) ℚ) : ℕ := ∏ a, ∏ b, (C a b).den

theorem clearInt_pos {d : ℕ} (C : Matrix (Fin d) (Fin d) ℚ) : 0 < clearInt C :=
  Finset.prod_pos fun a _ => Finset.prod_pos fun b _ => (C a b).den_pos

/-- The clearing integer clears every entry. -/
theorem clearInt_clears {d : ℕ} (C : Matrix (Fin d) (Fin d) ℚ) (a b : Fin d) :
    ∃ z : ℤ, (clearInt C : ℝ) * (C a b : ℝ) = z := by
  have hdvd : (C a b).den ∣ clearInt C :=
    (Finset.dvd_prod_of_mem (fun b' => (C a b').den) (Finset.mem_univ b)).trans
      (Finset.dvd_prod_of_mem (fun a' => ∏ b', (C a' b').den) (Finset.mem_univ a))
  obtain ⟨t, ht⟩ := hdvd
  refine ⟨t * (C a b).num, ?_⟩
  have hq : ((C a b : ℚ) : ℝ) * ((C a b).den : ℝ) = ((C a b).num : ℝ) := by
    exact_mod_cast Rat.mul_den_eq_num (C a b)
  rw [ht]; push_cast
  linear_combination (t : ℝ) * hq

/-- The clearing integer is at most `H^(d²)` for entries of height at most `H`. -/
theorem clearInt_le {d : ℕ} (C : Matrix (Fin d) (Fin d) ℚ) {Hed : ℝ}
    (hC : ∀ a b, (rationalHeight (C a b) : ℝ) ≤ Hed) : (clearInt C : ℝ) ≤ Hed ^ (d * d) := by
  unfold clearInt
  push_cast
  have hden : ∀ a b, ((C a b).den : ℝ) ≤ Hed := fun a b =>
    le_trans (by exact_mod_cast (by unfold rationalHeight; exact le_max_right _ _ :
      (C a b).den ≤ rationalHeight (C a b))) (hC a b)
  calc ∏ a, ∏ b, ((C a b).den : ℝ) ≤ ∏ _a : Fin d, ∏ _b : Fin d, Hed := by
        gcongr with a _ b _; exact hden a b
    _ = Hed ^ (d * d) := by
        rw [Finset.prod_const, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]

/-! ### Groups and main uses along a path (blueprint lines 1728-1730 and 1934) -/

namespace ColorSetup
variable {V : Type*} [DecidableEq V] (K : ColorSetup V) (T : AdmTree V)

/-- The change counter does not decrease from an ancestor to a cell, and when it is unchanged the
color data are unchanged. -/
theorem changes_anc {I₀ I : T.Cell} (h : T.Anc I₀ I) {v : V} (hv : v ∈ T.X I₀) :
    K.changes T I₀ v ≤ K.changes T I v ∧
      (K.changes T I₀ v = K.changes T I v →
        K.colorData (T.st I₀) v = K.colorData (T.st I) v) := by
  obtain ⟨n, hn⟩ := h
  induction n generalizing I with
  | zero => subst hn; exact ⟨le_rfl, fun _ => rfl⟩
  | succ n ih =>
    rw [Function.iterate_succ_apply] at hn
    have hvp : v ∈ T.X (T.par I) := (T.anc_le ⟨n, hn⟩).2.1 hv
    have hvI : v ∈ T.X I := (T.le_par I).2.1 hvp
    obtain ⟨h1, h2⟩ := ih hn
    have hrec := K.changes_par T hvI
    by_cases hc : K.colorData (T.st (T.par I)) v ≠ K.colorData (T.st I) v
    · have hcond : v ∈ T.X (T.par I) ∧
          K.colorData (T.st (T.par I)) v ≠ K.colorData (T.st I) v := ⟨hvp, hc⟩
      rw [ite_eq_left_of_eq_true _ _ (eq_true hcond)] at hrec
      exact ⟨by omega, fun he => by omega⟩
    · rw [not_not] at hc
      have hcond : ¬ (v ∈ T.X (T.par I) ∧
          K.colorData (T.st (T.par I)) v ≠ K.colorData (T.st I) v) := fun h => h.2 hc
      rw [ite_eq_right_of_eq_false _ _ (eq_false hcond), add_zero] at hrec
      exact ⟨by omega, fun he => (h2 (by omega)).trans hc⟩

variable [Fintype V]

/-- The groups of the present central vertices along a chain of cells number at most
`N_v (potMax + 1)`: each of the at most `N_v` vertices of the chain changes its color data fewer
than `potMax` times (blueprint lines 1728-1730; line 1934: "actual main uses along a path across
groups"). -/
theorem card_grp_chain_le
    [DecidableEq (ℕ × Option (Fin K.d0 × V × ℤ) × ℕ × (ℕ × ℕ) × Option (Fin K.d0 × V × ℤ))]
    {C : Finset T.Cell} (htot : ∀ I ∈ C, ∀ J ∈ C, T.Anc I J ∨ T.Anc J I)
    {Nv : ℕ} (hN : ∀ I, (T.X I).card ≤ Nv) :
    (((C ×ˢ (Finset.univ : Finset V)).filter (fun p : T.Cell × V => p.2 ∈ T.X p.1)).image
      (fun p : T.Cell × V => K.grp T Nv p.1 p.2)).card ≤ Nv * (K.potMax Nv + 1) := by
  rcases C.eq_empty_or_nonempty with rfl | hC
  · simp
  obtain ⟨I₁, hI₁, hmax⟩ := C.exists_max_image (fun I => (T.X I).card) hC
  have hsub : ∀ I ∈ C, T.X I ⊆ T.X I₁ := by
    intro I hI
    rcases htot I hI I₁ hI₁ with h | h
    · exact (T.anc_le h).2.1
    · exact (Finset.eq_of_subset_of_card_le (T.anc_le h).2.1 (hmax I hI)).symm.subset
  calc _ ≤ ((T.X I₁).biUnion (fun v => (C.filter (fun I => v ∈ T.X I)).image
        (fun I => K.grp T Nv I v))).card := by
        apply Finset.card_le_card
        intro σ hσ
        obtain ⟨⟨I, v⟩, hp, rfl⟩ := Finset.mem_image.mp hσ
        obtain ⟨hIv, hv⟩ := Finset.mem_filter.mp hp
        have hIC := (Finset.mem_product.mp hIv).1
        exact Finset.mem_biUnion.mpr ⟨v, hsub I hIC hv, Finset.mem_image.mpr
          ⟨I, Finset.mem_filter.mpr ⟨hIC, hv⟩, rfl⟩⟩
    _ ≤ ∑ v ∈ T.X I₁, ((C.filter (fun I => v ∈ T.X I)).image (fun I => K.grp T Nv I v)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _v ∈ T.X I₁, (K.potMax Nv + 1) := by
        apply Finset.sum_le_sum
        intro v _
        apply card_image_le_of_potential T.Anc
          (fun I hI J hJ => htot I (Finset.mem_filter.mp hI).1 J (Finset.mem_filter.mp hJ).1)
          (fun I => K.changes T I v)
        · intro I hI J _ hIJ he
          have hcd := (K.changes_anc T hIJ (Finset.mem_filter.mp hI).2).2 he
          simp only [grp, color, he, hcd]
        · intro I hI
          exact (K.changes_lt T hN (Finset.mem_filter.mp hI).2).le
    _ = (T.X I₁).card * (K.potMax Nv + 1) := by simp
    _ ≤ Nv * (K.potMax Nv + 1) := Nat.mul_le_mul_right _ (hN I₁)

end ColorSetup

namespace ActiveSetup.BasicFamilies.FamParams
variable {κ : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ c₀} {bf : A.BasicFamilies}
  (fp : bf.FamParams)

open Classical in
/-- The groups of the attempt with a present central vertex at an active cell containing a point
number at most `D (potMax + 1)`, `D` the vertex bound (blueprint line 1934: "actual main uses
along a path across groups"). -/
theorem card_groups_path_le (y : ℝ) :
    (((((A.cells.filter fun I => y ∈ dyadicGridCell A.G I.1 I.2).image bf.admAt) ×ˢ
      (Finset.univ : Finset bf.Vtx)).filter (fun p => p.2 ∈ bf.admT.X p.1)).image
        (fun p => fp.K.grp bf.admT A.famVtxBound p.1 p.2)).card ≤
      A.famVtxBound * (fp.K.potMax A.famVtxBound + 1) := by
  refine fp.K.card_grp_chain_le bf.admT (fun I hI J hJ => ?_) bf.admT_X_card_le
  obtain ⟨I', hI', rfl⟩ := Finset.mem_image.mp hI
  obtain ⟨J', hJ', rfl⟩ := Finset.mem_image.mp hJ
  obtain ⟨hI'c, hyI⟩ := Finset.mem_filter.mp hI'
  obtain ⟨hJ'c, hyJ⟩ := Finset.mem_filter.mp hJ'
  rcases le_total I'.1 J'.1 with h | h
  · exact Or.inl (bf.admAt_anc hJ'c hI'c (dyadicGridCell_subset_of_common_point A.G hyJ hyI h))
  · exact Or.inr (bf.admAt_anc hI'c hJ'c (dyadicGridCell_subset_of_common_point A.G hyI hyJ h))

end ActiveSetup.BasicFamilies.FamParams

namespace ActiveSetup.BasicFamilies.FamParams
variable {κ : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ c₀} {bf : A.BasicFamilies}
  (fp : bf.FamParams)

/-! ### The uniform first-match size and the budget `D_*` (blueprint line 1934) -/

/-- For a nonnegative top score, a ball level `j ≤ 4` and a pad `p ≤ P`, the ball radius is at
most `b₁ d₀ + b₁ + bbase 4 + P`. -/
theorem ballRadius_le {g : ℤ} (hg : 0 ≤ g) {j : ℕ} (hj : j ≤ 4) {p : ℕ} (hp : p ≤ fp.P) :
    fp.ballRadius g (fp.bbase j + p) ≤ fp.K.b1 * fp.K.d0 + fp.K.b1 + fp.bbase 4 + fp.P := by
  have hb : fp.bbase j ≤ fp.bbase 4 := by
    unfold bbase
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))) _
  unfold ballRadius
  refine Int.toNat_le.mpr ?_
  have hgb : (0 : ℤ) ≤ g * fp.K.b1 := mul_nonneg hg (Int.natCast_nonneg _)
  push_cast
  have : ((fp.bbase j : ℕ) : ℤ) ≤ fp.bbase 4 := by exact_mod_cast hb
  have : ((p : ℕ) : ℤ) ≤ fp.P := by exact_mod_cast hp
  nlinarith

/-- The edge height increases with the radius. -/
theorem ballEdgeH_mono (hHed : 2 ≤ fp.Hed) (dB : ℕ) {n n' : ℕ} (h : n ≤ n') :
    fp.ballEdgeH dB n ≤ fp.ballEdgeH dB n' := by
  unfold ballEdgeH
  apply Real.exp_le_exp.mpr
  have hl : 0 ≤ Real.log (2 * fp.Hed) := Real.log_nonneg (by linarith)
  have hnn : (n : ℝ) ≤ n' := by exact_mod_cast h
  have h1 : ((n + 1) * (dB + 1) : ℝ) ≤ (n' + 1) * (dB + 1) := by
    have : (0 : ℝ) ≤ dB + 1 := by positivity
    nlinarith
  have h2 := pow_le_pow_left₀ (by positivity) h1 8
  have := mul_le_mul_of_nonneg_right h2 hl
  nlinarith only [hl, h2]

/-- The uniform first-match size of the attempt: the size `X` of `mainFirstMatch_finite` at the
largest ball radius `b₁ d₀ + b₁ + bbase 4 + P` of the four ball levels (blueprint line 1934: the
bounds are uniform in the groups and the branch offsets). -/
noncomputable def Xmax (dB : ℕ) (H : ℝ) : ℝ :=
  1 + Real.log (chartTranslationBudget (H ^ 6)) +
    Real.log (3 * fp.ballEdgeH dB (fp.K.b1 * fp.K.d0 + fp.K.b1 + fp.bbase 4 + fp.P))

/-- The first-match size of a role is at least one. -/
theorem one_le_X (hHed : 2 ≤ fp.Hed) (dB : ℕ) {H : ℝ} (hH : 1 ≤ H) (n : ℕ) :
    1 ≤ 1 + Real.log (chartTranslationBudget (H ^ 6)) + Real.log (3 * fp.ballEdgeH dB n) := by
  have h1 : 0 ≤ Real.log (chartTranslationBudget (H ^ 6)) := by
    unfold chartTranslationBudget
    rw [Real.log_exp]
    have : 0 ≤ logarithmicSize (H ^ 6) := by
      unfold logarithmicSize
      have := Real.log_nonneg (one_le_pow₀ hH : (1 : ℝ) ≤ H ^ 6)
      linarith
    positivity
  have h2 : 0 ≤ Real.log (3 * fp.ballEdgeH dB n) := by
    have := fp.two_le_ballEdgeH hHed dB n
    exact Real.log_nonneg (by linarith)
  linarith

/-- The first-match size of a role with a nonnegative top score at a level `j ≤ 4` is at most the
uniform size. -/
theorem X_le_Xmax (hHed : 2 ≤ fp.Hed) (dB : ℕ) (H : ℝ) {g : ℤ} (hg : 0 ≤ g) {j : ℕ}
    (hj : j ≤ 4) :
    1 + Real.log (chartTranslationBudget (H ^ 6)) +
      Real.log (3 * fp.ballEdgeH dB (fp.ballRadius g (fp.bbase j + fp.P))) ≤ fp.Xmax dB H := by
  unfold Xmax
  have h0 : 0 < 3 * fp.ballEdgeH dB (fp.ballRadius g (fp.bbase j + fp.P)) := by
    have := fp.two_le_ballEdgeH hHed dB (fp.ballRadius g (fp.bbase j + fp.P)); linarith
  have := Real.log_le_log h0 (mul_le_mul_of_nonneg_left
    (fp.ballEdgeH_mono hHed dB (fp.ballRadius_le hg hj le_rfl)) (by norm_num : (0 : ℝ) ≤ 3))
  linarith

/-- The mode budget `D_*` of the attempt (blueprint line 1934), for the first-match degree `D`,
the dimension bound `d_B`, the source complexity `H`, the precision `δ_c`, a bound `N` for the main
labels at one cell, and the parameter `k`. With `B = exp(D X_max^D)` and the count
`M₁ = B (4 max(1, 4B/δ_c) + 1)^(4 d_B)` of the modes of one primary at one branch, it is the sum of
`e^k`; the modes and main uses of all groups along a path, `D (potMax + 1) (N + 1) M₁`; the
rational heights of `eq:mode-differences`; the inverse private weights `colBudget² (B² + 1)`; the
bound `H_ed^(d_B²)` of the clearing integer `Q₀`; and the absolute coefficient sums
`(√N + 1) colBudget B` of the lifted main outputs on normalized cells. It does not depend on the
branch offsets. -/
noncomputable def modeStar (D dB : ℕ) (H δc N k : ℝ) : ℝ :=
  Real.exp k +
    A.famVtxBound * (fp.K.potMax A.famVtxBound + 1) * (N + 1) *
      (Real.exp (D * fp.Xmax dB H ^ D) *
        (4 * max 1 (4 * Real.exp (D * fp.Xmax dB H ^ D) / δc) + 1) ^ (4 * dB)) +
    Real.exp (D * fp.Xmax dB H ^ D) *
      (1 + 4 * (2 * dB + 1) * max 1 (4 * Real.exp (D * fp.Xmax dB H ^ D) / δc)) +
    A.colBudget ^ 2 * (Real.exp (D * fp.Xmax dB H ^ D) ^ 2 + 1) +
    fp.Hed ^ (dB * dB) +
    (Real.sqrt N + 1) * A.colBudget * Real.exp (D * fp.Xmax dB H ^ D)

/-- Blueprint line 1934: the budget `D_*` dominates `e^k`, the first-match bound `B`, the modes of
all groups along a path (`D (potMax + 1)` groups, at most `N` matched primaries, at most the
bound of `mainAttemptLift` modes for each), the main uses along a path (`D (potMax + 1) N`), the
rational heights, the inverse private weights, the coefficient sums, and the modes of one role at
a point and of one primary at one branch, for a role with a nonnegative top score at a level
`j ≤ 4`, uniformly in the branch offsets. -/
theorem le_modeStar (D dB : ℕ) {H δc N : ℝ} (k : ℝ) (hHed : 2 ≤ fp.Hed) (hH : 1 ≤ H)
    (hδc : 0 < δc) (hN0 : 0 ≤ N) {g : ℤ} (hg : 0 ≤ g) {j : ℕ} (hj : j ≤ 4) :
    let X := 1 + Real.log (chartTranslationBudget (H ^ 6)) +
      Real.log (3 * fp.ballEdgeH dB (fp.ballRadius g (fp.bbase j + fp.P)))
    let B := Real.exp (D * X ^ D)
    Real.exp k ≤ fp.modeStar D dB H δc N k ∧ B ≤ fp.modeStar D dB H δc N k ∧
    A.famVtxBound * (fp.K.potMax A.famVtxBound + 1) *
      (N * (B * (4 * max 1 (4 * B / δc) + 1) ^ (4 * dB))) ≤ fp.modeStar D dB H δc N k ∧
    A.famVtxBound * (fp.K.potMax A.famVtxBound + 1) * N ≤ fp.modeStar D dB H δc N k ∧
    B * (1 + 4 * (2 * dB + 1) * max 1 (4 * B / δc)) ≤ fp.modeStar D dB H δc N k ∧
    A.colBudget ^ 2 * (B ^ 2 + 1) ≤ fp.modeStar D dB H δc N k ∧
    Real.sqrt N * A.colBudget * B ≤ fp.modeStar D dB H δc N k ∧
    N * (B * (4 * max 1 (4 * B / δc) + 1) ^ (4 * dB)) ≤ fp.modeStar D dB H δc N k ∧
    B * (4 * max 1 (4 * B / δc) + 1) ^ (4 * dB) ≤ fp.modeStar D dB H δc N k := by
  intro X B
  have hX1 : 1 ≤ X := fp.one_le_X hHed dB hH _
  have hXm : X ≤ fp.Xmax dB H := fp.X_le_Xmax hHed dB H hg hj
  set Bm := Real.exp (D * fp.Xmax dB H ^ D) with hBm
  have hB1 : 1 ≤ B := Real.one_le_exp (by positivity)
  have hBB : B ≤ Bm := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by linarith) hXm D) (Nat.cast_nonneg _))
  have hBm1 : 1 ≤ Bm := hB1.trans hBB
  have hcb : 2 ≤ A.colBudget := by
    have := A.Dc_nonneg; unfold ActiveSetup.colBudget
    have : (0 : ℝ) ≤ Fintype.card A.L * (1 + A.Dc) := by positivity
    linarith
  have hmax : max 1 (4 * B / δc) ≤ max 1 (4 * Bm / δc) :=
    max_le_max le_rfl (div_le_div_of_nonneg_right (by linarith) hδc.le)
  have hbase : (1 : ℝ) ≤ 4 * max 1 (4 * B / δc) + 1 := by
    have := le_max_left (1 : ℝ) (4 * B / δc); linarith
  have hM1 : B * (4 * max 1 (4 * B / δc) + 1) ^ (4 * dB) ≤
      Bm * (4 * max 1 (4 * Bm / δc) + 1) ^ (4 * dB) :=
    mul_le_mul hBB (pow_le_pow_left₀ (by linarith) (by linarith) _) (by positivity)
      (by linarith)
  have hM1m : 1 ≤ Bm * (4 * max 1 (4 * Bm / δc) + 1) ^ (4 * dB) :=
    one_le_mul_of_one_le_of_one_le hBm1 (one_le_pow₀ (by
      have := le_max_left (1 : ℝ) (4 * Bm / δc); linarith))
  have hNg : (0 : ℝ) ≤ A.famVtxBound * (fp.K.potMax A.famVtxBound + 1) := by positivity
  set t1 := Real.exp k
  set! t2 := (A.famVtxBound : ℝ) * (fp.K.potMax A.famVtxBound + 1) * (N + 1) *
    (Bm * (4 * max 1 (4 * Bm / δc) + 1) ^ (4 * dB))
  set! t3 := Bm * (1 + 4 * (2 * dB + 1) * max 1 (4 * Bm / δc))
  set! t4 := A.colBudget ^ 2 * (Bm ^ 2 + 1)
  set! t5 := fp.Hed ^ (dB * dB)
  set! t6 := (Real.sqrt N + 1) * A.colBudget * Bm
  have hS : fp.modeStar D dB H δc N k = t1 + t2 + t3 + t4 + t5 + t6 := rfl
  have h1 : 0 ≤ t1 := (Real.exp_pos _).le
  have h2 : 0 ≤ t2 := by positivity
  have h3 : 0 ≤ t3 := by positivity
  have h4 : 0 ≤ t4 := by positivity
  have h5 : 0 ≤ t5 := pow_nonneg (by linarith) _
  have h6 : 0 ≤ t6 := by positivity
  have hNg1 : (1 : ℝ) ≤ A.famVtxBound * (fp.K.potMax A.famVtxBound + 1) := by
    have h1 : (1 : ℝ) ≤ A.famVtxBound := by exact_mod_cast A.one_le_famVtxBound
    have h2 : (1 : ℝ) ≤ fp.K.potMax A.famVtxBound + 1 := by
      have : (0 : ℝ) ≤ fp.K.potMax A.famVtxBound := Nat.cast_nonneg _
      linarith
    exact one_le_mul_of_one_le_of_one_le h1 h2
  have hM1N : N * (B * (4 * max 1 (4 * B / δc) + 1) ^ (4 * dB)) ≤ t2 := by
    have hNN : N * (B * (4 * max 1 (4 * B / δc) + 1) ^ (4 * dB)) ≤
        (N + 1) * (Bm * (4 * max 1 (4 * Bm / δc) + 1) ^ (4 * dB)) :=
      mul_le_mul (by linarith) hM1 (by positivity) (by linarith)
    have hNM : (0 : ℝ) ≤ (N + 1) * (Bm * (4 * max 1 (4 * Bm / δc) + 1) ^ (4 * dB)) := by
      positivity
    calc _ ≤ (N + 1) * (Bm * (4 * max 1 (4 * Bm / δc) + 1) ^ (4 * dB)) := hNN
      _ ≤ (A.famVtxBound : ℝ) * (fp.K.potMax A.famVtxBound + 1) *
            ((N + 1) * (Bm * (4 * max 1 (4 * Bm / δc) + 1) ^ (4 * dB))) :=
          le_mul_of_one_le_left hNM hNg1
      _ = t2 := by ring
  have hM11 : B * (4 * max 1 (4 * B / δc) + 1) ^ (4 * dB) ≤ t2 := by
    have hNM : (0 : ℝ) ≤ Bm * (4 * max 1 (4 * Bm / δc) + 1) ^ (4 * dB) := by positivity
    calc _ ≤ Bm * (4 * max 1 (4 * Bm / δc) + 1) ^ (4 * dB) := hM1
      _ ≤ (A.famVtxBound : ℝ) * (fp.K.potMax A.famVtxBound + 1) * (N + 1) *
            (Bm * (4 * max 1 (4 * Bm / δc) + 1) ^ (4 * dB)) := by
          refine le_mul_of_one_le_left hNM ?_
          have : (1 : ℝ) ≤ N + 1 := by linarith
          exact one_le_mul_of_one_le_of_one_le hNg1 this
  rw [hS]
  refine ⟨by linarith, ?_, ?_, ?_, ?_, ?_, ?_, by linarith, by linarith⟩
  · have : B ≤ t3 := by
      have hm := le_max_left (1 : ℝ) (4 * Bm / δc)
      have : (0 : ℝ) ≤ 4 * (2 * dB + 1) * max 1 (4 * Bm / δc) := by positivity
      nlinarith only [hB1, hBB, this]
    linarith
  · have : (A.famVtxBound : ℝ) * (fp.K.potMax A.famVtxBound + 1) *
        (N * (B * (4 * max 1 (4 * B / δc) + 1) ^ (4 * dB))) ≤ t2 := by
      have hNN : N * (B * (4 * max 1 (4 * B / δc) + 1) ^ (4 * dB)) ≤
          (N + 1) * (Bm * (4 * max 1 (4 * Bm / δc) + 1) ^ (4 * dB)) :=
        mul_le_mul (by linarith) hM1 (by positivity) (by linarith)
      calc _ ≤ (A.famVtxBound : ℝ) * (fp.K.potMax A.famVtxBound + 1) *
            ((N + 1) * (Bm * (4 * max 1 (4 * Bm / δc) + 1) ^ (4 * dB))) :=
            mul_le_mul_of_nonneg_left hNN hNg
        _ = t2 := by ring
    linarith
  · have : (A.famVtxBound : ℝ) * (fp.K.potMax A.famVtxBound + 1) * N ≤ t2 := by
      have hNN : N ≤ (N + 1) * (Bm * (4 * max 1 (4 * Bm / δc) + 1) ^ (4 * dB)) := by
        nlinarith only [hN0, hM1m]
      calc _ ≤ (A.famVtxBound : ℝ) * (fp.K.potMax A.famVtxBound + 1) *
            ((N + 1) * (Bm * (4 * max 1 (4 * Bm / δc) + 1) ^ (4 * dB))) :=
            mul_le_mul_of_nonneg_left hNN hNg
        _ = t2 := by ring
    linarith
  · have : B * (1 + 4 * (2 * dB + 1) * max 1 (4 * B / δc)) ≤ t3 :=
      mul_le_mul hBB (by
        have : (0 : ℝ) ≤ 4 * (2 * dB + 1) := by positivity
        nlinarith only [hmax]) (by positivity) (by linarith)
    linarith
  · have : A.colBudget ^ 2 * (B ^ 2 + 1) ≤ t4 :=
      mul_le_mul_of_nonneg_left (by nlinarith only [hB1, hBB]) (sq_nonneg _)
    linarith
  · have : Real.sqrt N * A.colBudget * B ≤ t6 := by
      have hsq := Real.sqrt_nonneg N
      have : Real.sqrt N * A.colBudget ≤ (Real.sqrt N + 1) * A.colBudget := by nlinarith only [hcb]
      exact mul_le_mul this hBB (by linarith) (by positivity)
    linarith

end ActiveSetup.BasicFamilies.FamParams

namespace ActiveSetup.BasicFamilies.FamParams
variable {κ : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ c₀} {bf : A.BasicFamilies}
  (fp : bf.FamParams)

theorem two_le_colBudget : (2 : ℝ) ≤ A.colBudget := by
  have := A.Dc_nonneg; unfold ActiveSetup.colBudget
  have : (0 : ℝ) ≤ Fintype.card A.L * (1 + A.Dc) := by positivity
  linarith

/-- The logarithm of the budget `D_*` in terms of `E` bounding `d_B`, `log H_ed`, `log colBudget`,
`log N` and `log (1/δ_c)`: `log D_* ≤ 4 (d_B + 1) (L_B + E + 6) + E³ + k + L_p + 2E + 7`, where
`L_B = D X_max^D` and `L_p = log (potMax + 1)` (blueprint line 1934). -/
theorem log_modeStar_le_aux (D dB : ℕ) {H δc N k E : ℝ} (hk : 0 ≤ k) (hE : 1 ≤ E)
    (hdB : (dB : ℝ) ≤ E) (hHed : 2 ≤ fp.Hed) (hHedE : Real.log fp.Hed ≤ E) (hH : 1 ≤ H)
    (hδcE : δc⁻¹ ≤ Real.exp E) (hN0 : 0 ≤ N) (hNE : N ≤ Real.exp E)
    (hcB : A.colBudget ≤ Real.exp E) :
    Real.log (fp.modeStar D dB H δc N k) ≤
      4 * (dB + 1) * (D * fp.Xmax dB H ^ D + E + 6) + E ^ 3 + k +
        Real.log (fp.K.potMax A.famVtxBound + 1) + 2 * E + 7 := by
  set LB := (D : ℝ) * fp.Xmax dB H ^ D with hLB
  set Lp := Real.log (fp.K.potMax A.famVtxBound + 1) with hLp
  set! T0 := 4 * (dB + 1) * (LB + E + 6) + E ^ 3 + k + Lp + 2 * E + 5 with hT0
  have hX1 : 1 ≤ fp.Xmax dB H := fp.one_le_X hHed dB hH _
  have hLB0 : 0 ≤ LB := by positivity
  have hLp0 : 0 ≤ Lp := Real.log_nonneg (by
    have : (0 : ℝ) ≤ fp.K.potMax A.famVtxBound := Nat.cast_nonneg _
    linarith)
  have hdB0 : (0 : ℝ) ≤ dB := Nat.cast_nonneg _
  have he1 : (2 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
  have he2 : (7 : ℝ) ≤ Real.exp 2 := by
    have h := Real.exp_one_gt_d9
    have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    rw [this]; nlinarith only [h]
  have he3 : (9 : ℝ) ≤ Real.exp 3 := by
    have : Real.exp 3 = Real.exp 1 * Real.exp 2 := by rw [← Real.exp_add]; norm_num
    rw [this]; nlinarith only [he1, he2]
  have hexpE : 1 ≤ Real.exp E := Real.one_le_exp (by linarith)
  set! B := Real.exp LB with hB
  have hB1 : 1 ≤ B := Real.one_le_exp hLB0
  have hcb := two_le_colBudget (A := A)
  -- the vertex bound
  have hNv : (A.famVtxBound : ℝ) ≤ Real.exp (E + 3) := by
    have h1 : (A.famVtxBound : ℝ) ≤ 8 * A.colBudget + 1 := by
      unfold ActiveSetup.famVtxBound
      push_cast
      have := Nat.floor_le (by linarith : (0 : ℝ) ≤ 8 * A.colBudget)
      linarith
    rw [Real.exp_add]
    linarith [mul_le_mul_of_nonneg_left he3 (Real.exp_pos E).le]
  -- the factor `max 1 (4 B / δ_c)`
  have hmax : max 1 (4 * B / δc) ≤ Real.exp (LB + E + 2) := by
    have h4 : 4 * B / δc ≤ Real.exp (LB + E + 2) := by
      rw [div_eq_mul_inv, Real.exp_add, Real.exp_add]
      have : (4 : ℝ) ≤ Real.exp 2 := by linarith
      have hBE : 0 ≤ B * Real.exp E := by positivity
      calc 4 * B * δc⁻¹ ≤ 4 * B * Real.exp E :=
            mul_le_mul_of_nonneg_left hδcE (by positivity)
        _ = 4 * (B * Real.exp E) := by ring
        _ ≤ Real.exp 2 * (B * Real.exp E) := mul_le_mul_of_nonneg_right this hBE
        _ = B * Real.exp E * Real.exp 2 := by ring
    exact max_le (Real.one_le_exp (by linarith)) h4
  have hmax1 : 1 ≤ max 1 (4 * B / δc) := le_max_left _ _
  have hbase : 4 * max 1 (4 * B / δc) + 1 ≤ Real.exp (LB + E + 4) := by
    have : Real.exp (LB + E + 4) = Real.exp (LB + E + 2) * Real.exp 2 := by
      rw [← Real.exp_add]; ring_nf
    rw [this]
    have hx := Real.one_le_exp (by linarith : (0 : ℝ) ≤ LB + E + 2)
    linarith [mul_le_mul_of_nonneg_left he2 (Real.exp_pos (LB + E + 2)).le]
  have hpowb : (4 * max 1 (4 * B / δc) + 1) ^ (4 * dB) ≤ Real.exp (4 * dB * (LB + E + 4)) := by
    calc (4 * max 1 (4 * B / δc) + 1) ^ (4 * dB) ≤ Real.exp (LB + E + 4) ^ (4 * dB) :=
          pow_le_pow_left₀ (by linarith) hbase _
      _ = Real.exp (4 * dB * (LB + E + 4)) := by
          rw [← Real.exp_nat_mul]; push_cast; ring_nf
  -- the comparison with `T0`
  have hdL : 0 ≤ (dB : ℝ) * LB := mul_nonneg hdB0 hLB0
  have hdE : 0 ≤ (dB : ℝ) * E := mul_nonneg hdB0 (by linarith)
  have hE3 : 0 ≤ E ^ 3 := by positivity
  have key : 4 * ((dB : ℝ) + 1) * (LB + E + 6) =
      4 * (dB * LB) + 4 * (dB * E) + 24 * dB + 4 * LB + 4 * E + 24 := by ring
  -- the six terms
  set! t1 := Real.exp k
  set! t2 := (A.famVtxBound : ℝ) * (fp.K.potMax A.famVtxBound + 1) * (N + 1) *
    (B * (4 * max 1 (4 * B / δc) + 1) ^ (4 * dB))
  set! t3 := B * (1 + 4 * (2 * dB + 1) * max 1 (4 * B / δc))
  set! t4 := A.colBudget ^ 2 * (B ^ 2 + 1)
  set! t5 := fp.Hed ^ (dB * dB)
  set! t6 := (Real.sqrt N + 1) * A.colBudget * B
  have hS : fp.modeStar D dB H δc N k = t1 + t2 + t3 + t4 + t5 + t6 := rfl
  have hT1 : t1 ≤ Real.exp T0 := Real.exp_le_exp.mpr (by linarith)
  have hT2 : t2 ≤ Real.exp T0 := by
    have hp : (fp.K.potMax A.famVtxBound + 1 : ℝ) = Real.exp Lp := by
      rw [hLp, Real.exp_log (by positivity)]
    have hN1 : N + 1 ≤ Real.exp (E + 1) := by
      rw [Real.exp_add]; linarith [mul_le_mul_of_nonneg_left he1 (Real.exp_pos E).le]
    calc t2 ≤ Real.exp (E + 3) * Real.exp Lp * Real.exp (E + 1) *
          (B * Real.exp (4 * dB * (LB + E + 4))) := by
          simp only [t2]
          rw [hp]
          gcongr
      _ = Real.exp (E + 3 + Lp + (E + 1) + (LB + 4 * dB * (LB + E + 4))) := by
          simp only [B, Real.exp_add]
      _ ≤ Real.exp T0 := Real.exp_le_exp.mpr (by
          have : 4 * (dB : ℝ) * (LB + E + 4) = 4 * (dB * LB) + 4 * (dB * E) + 16 * dB := by ring
          linarith)
  have hT3 : t3 ≤ Real.exp T0 := by
    have h2d : 2 * (dB : ℝ) + 1 ≤ Real.exp (2 * dB) := by
      have := Real.add_one_le_exp (2 * (dB : ℝ)); linarith
    have hin : 1 + 4 * (2 * dB + 1) * max 1 (4 * B / δc) ≤
        Real.exp (2 * dB + 2) * Real.exp (LB + E + 2) := by
      have h5 : 1 + 4 * (2 * dB + 1) * max 1 (4 * B / δc) ≤
          5 * (2 * dB + 1) * max 1 (4 * B / δc) := by
        have := one_le_mul_of_one_le_of_one_le (by linarith : (1 : ℝ) ≤ 2 * dB + 1) hmax1
        linarith
      have h6 : 5 * (2 * (dB : ℝ) + 1) ≤ Real.exp (2 * dB + 2) := by
        rw [Real.exp_add]
        linarith [mul_le_mul_of_nonneg_left he2 (Real.exp_pos (2 * (dB : ℝ))).le,
          Real.one_le_exp (by positivity : (0 : ℝ) ≤ 2 * dB)]
      calc _ ≤ 5 * (2 * dB + 1) * max 1 (4 * B / δc) := h5
        _ ≤ Real.exp (2 * dB + 2) * Real.exp (LB + E + 2) :=
            mul_le_mul h6 hmax (by linarith) (Real.exp_pos _).le
    calc t3 ≤ B * (Real.exp (2 * dB + 2) * Real.exp (LB + E + 2)) :=
          mul_le_mul_of_nonneg_left hin (by linarith)
      _ = Real.exp (LB + (2 * dB + 2) + (LB + E + 2)) := by simp only [B, Real.exp_add]; try ring
      _ ≤ Real.exp T0 := Real.exp_le_exp.mpr (by linarith)
  have hT4 : t4 ≤ Real.exp T0 := by
    have hc2 : A.colBudget ^ 2 ≤ Real.exp (2 * E) := by
      rw [show 2 * E = E + E by ring, Real.exp_add, sq]
      exact mul_le_mul hcB hcB (by linarith) (Real.exp_pos _).le
    have hB2 : B ^ 2 + 1 ≤ Real.exp (2 * LB + 1) := by
      rw [Real.exp_add, show 2 * LB = LB + LB by ring, Real.exp_add, ← hB, sq]
      have hBB : 1 ≤ B * B := one_le_mul_of_one_le_of_one_le hB1 hB1
      linarith [mul_le_mul_of_nonneg_left he1 (by positivity : (0 : ℝ) ≤ B * B)]
    calc t4 ≤ Real.exp (2 * E) * Real.exp (2 * LB + 1) :=
          mul_le_mul hc2 hB2 (by positivity) (Real.exp_pos _).le
      _ = Real.exp (2 * E + (2 * LB + 1)) := (Real.exp_add _ _).symm
      _ ≤ Real.exp T0 := Real.exp_le_exp.mpr (by linarith)
  have hT5 : t5 ≤ Real.exp T0 := by
    have hl : 0 ≤ Real.log fp.Hed := Real.log_nonneg (by linarith)
    have : t5 = Real.exp ((dB * dB : ℕ) * Real.log fp.Hed) := by
      simp only [t5]
      rw [Real.exp_nat_mul, Real.exp_log (by linarith)]
    rw [this]
    refine Real.exp_le_exp.mpr ?_
    push_cast
    have h1 : (dB : ℝ) * dB ≤ E * E := mul_le_mul hdB hdB hdB0 (by linarith)
    have h2 : (dB : ℝ) * dB * Real.log fp.Hed ≤ E * E * E :=
      mul_le_mul h1 hHedE hl (by positivity)
    have : E ^ 3 = E * E * E := by ring
    linarith
  have hT6 : t6 ≤ Real.exp T0 := by
    have hsq : Real.sqrt N + 1 ≤ Real.exp (E + 2) := by
      have h1 : Real.sqrt N ≤ N + 1 := by
        have he : (Real.sqrt N - 1) ^ 2 = N - 2 * Real.sqrt N + 1 := by
          rw [sub_sq, Real.sq_sqrt hN0]; ring
        linarith [sq_nonneg (Real.sqrt N - 1), Real.sqrt_nonneg N]
      rw [Real.exp_add]; linarith [mul_le_mul_of_nonneg_left he2 (Real.exp_pos E).le]
    calc t6 ≤ Real.exp (E + 2) * Real.exp E * B := by
          simp only [t6]; gcongr
      _ = Real.exp (E + 2 + E + LB) := by simp only [B, Real.exp_add]
      _ ≤ Real.exp T0 := Real.exp_le_exp.mpr (by linarith)
  have hpos : 0 < fp.modeStar D dB H δc N k := by
    rw [hS]
    have : 0 ≤ t2 := by positivity
    have : 0 ≤ t3 := by positivity
    have : 0 ≤ t4 := by positivity
    have : 0 ≤ t5 := pow_nonneg (by linarith) _
    have : 0 ≤ t6 := by positivity
    have := Real.exp_pos k
    linarith
  have hsum : fp.modeStar D dB H δc N k ≤ Real.exp (T0 + 2) := by
    rw [hS, Real.exp_add]
    linarith [mul_le_mul_of_nonneg_left he2 (Real.exp_pos T0).le]
  calc Real.log (fp.modeStar D dB H δc N k) ≤ T0 + 2 := by
        rw [Real.log_le_iff_le_exp hpos]; exact hsum
    _ = _ := by simp only [hT0]; ring

end ActiveSetup.BasicFamilies.FamParams

namespace ActiveSetup.BasicFamilies.FamParams
variable {κ : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ c₀} {bf : A.BasicFamilies}
  (fp : bf.FamParams)

theorem famVtxBound_le : (A.famVtxBound : ℝ) ≤ 8 * A.colBudget + 1 := by
  unfold ActiveSetup.famVtxBound
  push_cast
  have := Nat.floor_le (by linarith [two_le_colBudget (A := A)] : (0 : ℝ) ≤ 8 * A.colBudget)
  linarith

theorem famVtxBound_le_exp {E : ℝ} (hE : 1 ≤ E) (hcB : A.colBudget ≤ Real.exp E) :
    (A.famVtxBound : ℝ) ≤ Real.exp (E + 3) := by
  have he3 : (9 : ℝ) ≤ Real.exp 3 := by
    have h := Real.exp_one_gt_d9
    have : Real.exp 3 = Real.exp 1 * Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add, ← Real.exp_add]; norm_num
    rw [this]; nlinarith
  have hexpE : 1 ≤ Real.exp E := Real.one_le_exp (by linarith)
  rw [Real.exp_add]
  linarith [famVtxBound_le (A := A), mul_le_mul_of_nonneg_left he3 (Real.exp_pos E).le]

/-- The number of color degrees is at most `5001 k^c` when `colBudget ≤ exp(k^c)`. -/
theorem d0_le {k : ℝ} {c : ℕ} (hk : 1 ≤ k) (hcB : A.colBudget ≤ Real.exp (k ^ c)) :
    (fp.K.d0 : ℝ) ≤ 5001 * k ^ c := by
  have hE1 : 1 ≤ k ^ c := one_le_pow₀ hk
  have hNv1 : (1 : ℝ) ≤ A.famVtxBound := by exact_mod_cast A.one_le_famVtxBound
  have hNv := famVtxBound_le_exp hE1 hcB
  have hlog : Real.log (2 * A.famVtxBound) ≤ k ^ c + 4 := by
    rw [Real.log_mul (by norm_num) (by linarith)]
    have h2 : Real.log 2 ≤ 1 := by
      rw [Real.log_le_iff_le_exp (by norm_num)]; linarith [Real.add_one_le_exp (1 : ℝ)]
    have h3 : Real.log A.famVtxBound ≤ k ^ c + 3 := by
      rw [Real.log_le_iff_le_exp (by linarith)]; exact hNv
    linarith
  have hl0 : 0 ≤ 1000 * Real.log (2 * A.famVtxBound) := by
    have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ 2 * A.famVtxBound); linarith
  have hceil := Nat.ceil_lt_add_one hl0
  change ((colorDegree A.famVtxBound : ℕ) : ℝ) ≤ _
  unfold colorDegree
  linarith

/-- The logarithm of `potMax + 1` for the vertex bound: at most `2 d₀ (2 d₀ + 1) + d₀ + 2E + 9`. -/
theorem log_potMax_le {E : ℝ} (hE : 1 ≤ E) (hcB : A.colBudget ≤ Real.exp E) :
    Real.log (fp.K.potMax A.famVtxBound + 1) ≤
      2 * ((fp.K.d0 : ℝ) * (2 * fp.K.d0 + 1)) + fp.K.d0 + 2 * E + 9 := by
  set d := (fp.K.d0 : ℝ) with hd
  set Nv := A.famVtxBound
  have hd0 : 0 ≤ d := Nat.cast_nonneg _
  have hNv := famVtxBound_le_exp hE hcB
  have he1 : (2 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
  have hexp3 : 1 ≤ Real.exp (E + 3) := Real.one_le_exp (by linarith)
  have hNv1 : (Nv : ℝ) + 1 ≤ Real.exp (E + 4) := by
    rw [show E + 4 = (E + 3) + 1 by ring, Real.exp_add]
    linarith [mul_le_mul_of_nonneg_left he1 (Real.exp_pos (E + 3)).le]
  have ha : d * (2 * d + 1) + 1 ≤ Real.exp (d * (2 * d + 1)) := by
    have := Real.add_one_le_exp (d * (2 * d + 1)); linarith
  have hb : ((Nat.size Nv : ℕ) : ℝ) + 1 ≤ Real.exp (E + 4) := by
    have : Nat.size Nv ≤ Nv := Nat.size_le.mpr Nat.lt_two_pow_self
    have : ((Nat.size Nv : ℕ) : ℝ) ≤ Nv := by exact_mod_cast this
    linarith
  have hc : d * ((flog32 Nv : ℕ) : ℝ) + 1 ≤ Real.exp d * Real.exp (E + 4) := by
    have hf : ((flog32 Nv : ℕ) : ℝ) ≤ Nv := by exact_mod_cast flog32_le Nv
    have h1 : d * ((flog32 Nv : ℕ) : ℝ) + 1 ≤ (d + 1) * ((Nv : ℝ) + 1) := by
      have : d * ((flog32 Nv : ℕ) : ℝ) ≤ d * Nv := mul_le_mul_of_nonneg_left hf hd0
      have : (0 : ℝ) ≤ Nv := Nat.cast_nonneg _
      nlinarith only [hd, hf]
    have h2 : d + 1 ≤ Real.exp d := Real.add_one_le_exp d
    exact h1.trans (mul_le_mul h2 hNv1 (by positivity) (Real.exp_pos _).le)
  have hpm : ((fp.K.potMax Nv : ℕ) : ℝ) ≤
      Real.exp (2 * (d * (2 * d + 1)) + d + 2 * (E + 4)) := by
    unfold ColorSetup.potMax
    push_cast
    have e : Real.exp (2 * (d * (2 * d + 1)) + d + 2 * (E + 4)) =
        Real.exp (d * (2 * d + 1)) * Real.exp (E + 4) * (Real.exp d * Real.exp (E + 4)) *
          Real.exp (d * (2 * d + 1)) := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; ring_nf
    rw [e]
    have hp1 : (0 : ℝ) ≤ d * (2 * d + 1) + 1 := by positivity
    gcongr
  have hQ : 0 ≤ 2 * (d * (2 * d + 1)) + d + 2 * (E + 4) := by positivity
  have hpos : (0 : ℝ) < (fp.K.potMax Nv : ℕ) + 1 := by positivity
  rw [Real.log_le_iff_le_exp hpos]
  set Q' := 2 * (d * (2 * d + 1)) + d + 2 * (E + 4) with hQ'
  have h1 : 1 ≤ Real.exp Q' := Real.one_le_exp hQ
  have e2 : 2 * (d * (2 * d + 1)) + d + 2 * E + 9 = Q' + 1 := by rw [hQ']; ring
  rw [e2, Real.exp_add]
  linarith [mul_le_mul_of_nonneg_left he1 (Real.exp_pos Q').le]

end ActiveSetup.BasicFamilies.FamParams

namespace ActiveSetup.BasicFamilies.FamParams
variable {κ : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ c₀} {bf : A.BasicFamilies}
  (fp : bf.FamParams)

/-- The uniform first-match size is at most `w^(113c+116)`, `w = 5002 k P`, under the standing
bounds of `log_modeStar_poly`. -/
theorem Xmax_le_pow {c dB : ℕ} {H k : ℝ} (hk : 1 ≤ k) (hL : (fp.Lc : ℝ) + 6 ≤ k ^ c)
    (hHm : (fp.Hmax : ℝ) + 1 ≤ (k * fp.P) ^ c) (hdB : (dB : ℝ) ≤ k ^ c) (hHed : 2 ≤ fp.Hed)
    (hHedk : Real.log fp.Hed ≤ k ^ c) (hH : 1 ≤ H) (hHk : Real.log H ≤ k ^ c)
    (hcB : A.colBudget ≤ Real.exp (k ^ c)) :
    fp.Xmax dB H ≤ (5002 * (k * fp.P)) ^ (113 * c + 116) := by
  set E := k ^ c with hE
  set u := k * (fp.P : ℝ) with hu
  set w := 5002 * u with hw
  have hP1 : (1 : ℝ) ≤ fp.P := by exact_mod_cast fp.hP
  have hE1 : 1 ≤ E := one_le_pow₀ hk
  have hku : k ≤ u := le_mul_of_one_le_right (by linarith) hP1
  have hPu : (fp.P : ℝ) ≤ u := le_mul_of_one_le_left (by linarith) hk
  have hu1 : 1 ≤ u := hk.trans hku
  have huw : u ≤ w := by linarith
  have hw5 : 5002 ≤ w := by linarith
  have hw1 : 1 ≤ w := by linarith
  have hw0 : 0 ≤ w := by linarith
  have hEw : E ≤ w ^ c := pow_le_pow_left₀ (by linarith) (hku.trans huw) c
  have hpw : ∀ a b : ℕ, a ≤ b → w ^ a ≤ w ^ b := fun a b h => pow_le_pow_right₀ hw1 h
  have hw2 : (100000 : ℝ) ≤ w ^ 2 := by nlinarith only [hk, hku]
  have hstep : ∀ (a b : ℕ) (r : ℝ), a + 1 = b → r ≤ 5002 → r * w ^ a ≤ w ^ b :=
      fun a b r hab hr => by
    rw [← hab, pow_succ]
    have := mul_le_mul_of_nonneg_left (by linarith : r ≤ w) (pow_nonneg hw0 a)
    linarith
  -- `r E ≤ w^(c+1)` for constants `0 ≤ r ≤ 5002`
  have hcE : ∀ r : ℝ, 0 ≤ r → r ≤ 5002 → r * E ≤ w ^ (c + 1) := fun r hr0 hr => by
    have := mul_le_mul_of_nonneg_left hEw hr0
    linarith [hstep c (c + 1) r rfl hr]
  -- the color degree and the pad bound
  have hd0 := fp.d0_le hk hcB
  have hd0w : (fp.K.d0 : ℝ) + 1 ≤ w ^ (c + 1) := by
    have := hcE 5002 (by norm_num) le_rfl; linarith
  have hd0w' : (fp.K.d0 : ℝ) ≤ w ^ (c + 1) := by linarith
  have hHw : (fp.Hmax : ℝ) + 1 ≤ w ^ c :=
    hHm.trans (pow_le_pow_left₀ (by linarith) huw c)
  have hb1 : (fp.K.b1 : ℝ) ≤ w ^ (12 * c + 11) := by
    change ((A.fcb1 fp.Hmax : ℕ) : ℝ) ≤ _
    unfold ActiveSetup.fcb1 ActiveSetup.cb2
    push_cast
    have h1 : (A.fcd0 : ℝ) ^ 10 ≤ (w ^ (c + 1)) ^ 10 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hd0w' 10
    have h2 : 100 * ((fp.Hmax : ℝ) + 1) ≤ w * w ^ c :=
      mul_le_mul (by linarith) hHw (by positivity) hw0
    calc (A.fcd0 : ℝ) ^ 10 * (100 * ((fp.Hmax : ℝ) + 1)) * ((fp.Hmax : ℝ) + 1) ≤
          (w ^ (c + 1)) ^ 10 * (w * w ^ c) * w ^ c := by
          gcongr
      _ = w ^ (12 * c + 11) := by ring
  -- the largest ball radius
  set! n0 : ℕ := fp.K.b1 * fp.K.d0 + fp.K.b1 + fp.bbase 4 + fp.P with hn0
  have hbb : (fp.bbase 4 : ℝ) = 20 * fp.P * (fp.Lc + 1) + 30 * fp.P := by
    have : fp.bbase 4 = 20 * fp.P * (fp.Lc + 1) + 30 * fp.P := by
      change 20 * fp.P * (fp.Lc + 1) + 10 * (4 - 1) * fp.P = _
      ring
    rw [this]; push_cast; ring
  have hn0w : (n0 : ℝ) + 1 ≤ w ^ (13 * c + 13) := by
    have hLE : (fp.Lc : ℝ) + 1 ≤ E := by linarith
    have hrest : (fp.bbase 4 : ℝ) + fp.P + 1 ≤ w ^ (c + 1) := by
      rw [hbb]
      have h1 : (fp.P : ℝ) * (fp.Lc + 1) ≤ fp.P * E :=
        mul_le_mul_of_nonneg_left hLE (by linarith)
      have h2 : (fp.P : ℝ) ≤ fp.P * E := le_mul_of_one_le_right (by linarith) hE1
      have h3 : (1 : ℝ) ≤ fp.P * E := one_le_mul_of_one_le_of_one_le hP1 hE1
      have h4 : 52 * ((fp.P : ℝ) * E) ≤ w * w ^ c := by
        calc 52 * ((fp.P : ℝ) * E) = (52 * fp.P) * E := by ring
          _ ≤ w * w ^ c := mul_le_mul (by linarith) hEw (by linarith) hw0
      rw [pow_succ]
      linarith
    have hmain : (fp.K.b1 : ℝ) * (fp.K.d0 + 1) ≤ w ^ (13 * c + 12) := by
      calc (fp.K.b1 : ℝ) * (fp.K.d0 + 1) ≤ w ^ (12 * c + 11) * w ^ (c + 1) :=
            mul_le_mul hb1 hd0w (by positivity) (by positivity)
        _ = w ^ (13 * c + 12) := by ring
    have hsplit : (n0 : ℝ) + 1 =
        (fp.K.b1 : ℝ) * (fp.K.d0 + 1) + ((fp.bbase 4 : ℝ) + fp.P + 1) := by
      simp only [hn0]; push_cast; ring
    have h5 : w ^ (c + 1) ≤ w ^ (13 * c + 12) := hpw _ _ (by omega)
    have h6 := hstep (13 * c + 12) (13 * c + 13) 2 (by omega) (by norm_num)
    linarith
  -- the uniform first-match size
  have hlogbe : Real.log (3 * fp.ballEdgeH dB n0) ≤ 2 + w ^ (113 * c + 115) := by
    have hbe0 : 0 < fp.ballEdgeH dB n0 := by unfold ballEdgeH; exact Real.exp_pos _
    rw [Real.log_mul (by norm_num) hbe0.ne']
    have hl3 : Real.log 3 ≤ 2 := by
      rw [Real.log_le_iff_le_exp (by norm_num)]
      have h := Real.exp_one_gt_d9
      have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      nlinarith only [h, this]
    unfold ballEdgeH
    rw [Real.log_exp]
    have hdB1 : (dB : ℝ) + 1 ≤ w ^ (c + 1) := by
      have := hcE 2 (by norm_num) (by norm_num); linarith
    have hnd : ((n0 : ℝ) + 1) * ((dB : ℝ) + 1) ≤ w ^ (14 * c + 14) := by
      calc ((n0 : ℝ) + 1) * ((dB : ℝ) + 1) ≤ w ^ (13 * c + 13) * w ^ (c + 1) :=
            mul_le_mul hn0w hdB1 (by positivity) (by positivity)
        _ = w ^ (14 * c + 14) := by ring
    have hnd8 : (((n0 : ℝ) + 1) * ((dB : ℝ) + 1)) ^ 8 ≤ w ^ (112 * c + 112) := by
      calc _ ≤ (w ^ (14 * c + 14)) ^ 8 := pow_le_pow_left₀ (by positivity) hnd 8
        _ = w ^ (112 * c + 112) := by ring
    have hl2H : Real.log (2 * fp.Hed) ≤ w ^ (c + 1) := by
      rw [Real.log_mul (by norm_num) (by linarith)]
      have h2 : Real.log 2 ≤ 1 := by
        rw [Real.log_le_iff_le_exp (by norm_num)]; linarith [Real.add_one_le_exp (1 : ℝ)]
      have := hcE 2 (by norm_num) (by norm_num); linarith
    have hl2H0 : 0 ≤ Real.log (2 * fp.Hed) := Real.log_nonneg (by linarith)
    have hprod : 100000 * (((n0 : ℝ) + 1) * ((dB : ℝ) + 1)) ^ 8 * Real.log (2 * fp.Hed) ≤
        w ^ 2 * w ^ (112 * c + 112) * w ^ (c + 1) :=
      mul_le_mul (mul_le_mul hw2 hnd8 (by positivity) (by positivity)) hl2H hl2H0
        (by positivity)
    have he : w ^ 2 * w ^ (112 * c + 112) * w ^ (c + 1) = w ^ (113 * c + 115) := by ring
    linarith only [hl3, hprod, he]
  have hctb : Real.log (chartTranslationBudget (H ^ 6)) ≤ w ^ (3 * c + 2) := by
    unfold chartTranslationBudget logarithmicSize
    rw [Real.log_exp, Real.log_pow]
    have hl0 : 0 ≤ Real.log H := Real.log_nonneg hH
    have h1 : 1 + ((6 : ℕ) : ℝ) * Real.log H ≤ 7 * E := by push_cast; linarith
    have h2 : (1 + ((6 : ℕ) : ℝ) * Real.log H) ^ 3 ≤ (7 * E) ^ 3 :=
      pow_le_pow_left₀ (by positivity) h1 3
    have hE3 : E ^ 3 ≤ (w ^ c) ^ 3 := pow_le_pow_left₀ (by linarith) hEw 3
    have h34 : (34300 : ℝ) ≤ w ^ 2 := by linarith
    have h3 : 100 * (7 * E) ^ 3 ≤ w ^ 2 * (w ^ c) ^ 3 := by
      calc 100 * (7 * E) ^ 3 = 34300 * E ^ 3 := by ring
        _ ≤ w ^ 2 * (w ^ c) ^ 3 := mul_le_mul h34 hE3 (by positivity) (by positivity)
    calc 100 * (1 + ((6 : ℕ) : ℝ) * Real.log H) ^ 3 ≤ 100 * (7 * E) ^ 3 := by linarith
      _ ≤ w ^ 2 * (w ^ c) ^ 3 := h3
      _ = w ^ (3 * c + 2) := by ring
  change fp.Xmax dB H ≤ w ^ (113 * c + 116)
  unfold Xmax
  rw [← hn0]
  have h1 : w ^ (3 * c + 2) ≤ w ^ (113 * c + 115) := hpw _ _ (by omega)
  have h2 := hstep (113 * c + 115) (113 * c + 116) 5 (by omega) (by norm_num)
  have h3 : 1 ≤ w ^ (113 * c + 115) := one_le_pow₀ hw1
  linarith

/-- `log (potMax + 1) ≤ w^(2c+3)`, `w = 5002 k P`, when `colBudget ≤ exp(k^c)`. -/
theorem log_potMax_le_pow {c : ℕ} {k : ℝ} (hk : 1 ≤ k) (hcB : A.colBudget ≤ Real.exp (k ^ c)) :
    Real.log (fp.K.potMax A.famVtxBound + 1) ≤ (5002 * (k * fp.P)) ^ (2 * c + 3) := by
  set E := k ^ c with hE
  set u := k * (fp.P : ℝ) with hu
  set w := 5002 * u with hw
  have hP1 : (1 : ℝ) ≤ fp.P := by exact_mod_cast fp.hP
  have hE1 : 1 ≤ E := one_le_pow₀ hk
  have hku : k ≤ u := le_mul_of_one_le_right (by linarith) hP1
  have hPu : (fp.P : ℝ) ≤ u := le_mul_of_one_le_left (by linarith) hk
  have hu1 : 1 ≤ u := hk.trans hku
  have huw : u ≤ w := by linarith
  have hw5 : 5002 ≤ w := by linarith
  have hw1 : 1 ≤ w := by linarith
  have hw0 : 0 ≤ w := by linarith
  have hEw : E ≤ w ^ c := pow_le_pow_left₀ (by linarith) (hku.trans huw) c
  have hpw : ∀ a b : ℕ, a ≤ b → w ^ a ≤ w ^ b := fun a b h => pow_le_pow_right₀ hw1 h
  have hw2 : (100000 : ℝ) ≤ w ^ 2 := by nlinarith only [hk, hku]
  have hstep : ∀ (a b : ℕ) (r : ℝ), a + 1 = b → r ≤ 5002 → r * w ^ a ≤ w ^ b :=
      fun a b r hab hr => by
    rw [← hab, pow_succ]
    have := mul_le_mul_of_nonneg_left (by linarith : r ≤ w) (pow_nonneg hw0 a)
    linarith
  -- `r E ≤ w^(c+1)` for constants `0 ≤ r ≤ 5002`
  have hcE : ∀ r : ℝ, 0 ≤ r → r ≤ 5002 → r * E ≤ w ^ (c + 1) := fun r hr0 hr => by
    have := mul_le_mul_of_nonneg_left hEw hr0
    linarith [hstep c (c + 1) r rfl hr]
  -- the color degree
  have hd0 := fp.d0_le hk hcB
  have hd0w : (fp.K.d0 : ℝ) + 1 ≤ w ^ (c + 1) := by
    have := hcE 5002 (by norm_num) le_rfl; linarith
  have hd0w' : (fp.K.d0 : ℝ) ≤ w ^ (c + 1) := by linarith
  have h := fp.log_potMax_le hE1 hcB
  have hd0' : (0 : ℝ) ≤ fp.K.d0 := Nat.cast_nonneg _
  have hW1 : 1 ≤ w ^ (c + 1) := one_le_pow₀ hw1
  have h1 : (fp.K.d0 : ℝ) * (2 * fp.K.d0 + 1) ≤ w ^ (c + 1) * (3 * w ^ (c + 1)) :=
    mul_le_mul hd0w' (by linarith) (by positivity) (by positivity)
  have h2 : w ^ (c + 1) * (3 * w ^ (c + 1)) = 3 * w ^ (2 * c + 2) := by ring
  have h3 : w ^ (c + 1) ≤ w ^ (2 * c + 2) := hpw _ _ (by omega)
  have h4 : w ^ c ≤ w ^ (2 * c + 2) := hpw _ _ (by omega)
  have h5 : 1 ≤ w ^ (2 * c + 2) := one_le_pow₀ hw1
  have h6 := hstep (2 * c + 2) (2 * c + 3) 18 (by omega) (by norm_num)
  linarith

end ActiveSetup.BasicFamilies.FamParams

open ActiveSetup.BasicFamilies.FamParams in
/-- Blueprint line 1934: `log D_* ≤ P^C`. For fixed degrees `c` (of the standing bounds) and `D`
(of the first-match expansion) there is a degree `C` such that, whenever `L + 6`, the dimension
bound `d_B`, `log H_ed`, `log H`, `log (1/δ_c)`, `log N` and `log colBudget` are at most `k^c`
and `H_max + 1 ≤ (k P)^c`, the budget `D_*` of the attempt satisfies `log D_* ≤ C (k P)^C`
(line 1673: "all later bounds polynomial in `P, k` will be written `P^C`"). -/
theorem log_modeStar_poly (c D : ℕ) :
    ∃ C : ℕ, ∀ {κ : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ c₀} {bf : A.BasicFamilies}
      (fp : bf.FamParams) (dB : ℕ) {H δc N k : ℝ}, 1 ≤ k → (fp.Lc : ℝ) + 6 ≤ k ^ c →
      (fp.Hmax : ℝ) + 1 ≤ (k * fp.P) ^ c → (dB : ℝ) ≤ k ^ c → 2 ≤ fp.Hed →
      Real.log fp.Hed ≤ k ^ c → 1 ≤ H → Real.log H ≤ k ^ c → δc⁻¹ ≤ Real.exp (k ^ c) →
      0 ≤ N → N ≤ Real.exp (k ^ c) → A.colBudget ≤ Real.exp (k ^ c) →
      Real.log (fp.modeStar D dB H δc N k) ≤ C * (k * fp.P) ^ C := by
  obtain ⟨Q, hQ⟩ : ∃ Q : ℕ, Q = (113 * c + 117) * D := ⟨_, rfl⟩
  refine ⟨5002 ^ (Q + 4 * c + 4) + (Q + 4 * c + 4), ?_⟩
  intro κ c₀ A bf fp dB H δc N k hk hL hHm hdB hHed hHedk hH hHk hδck hN0 hNk hcB
  set E := k ^ c with hE
  set u := k * (fp.P : ℝ) with hu
  set! w := 5002 * u with hw
  have hP1 : (1 : ℝ) ≤ fp.P := by exact_mod_cast fp.hP
  have hE1 : 1 ≤ E := one_le_pow₀ hk
  have hku : k ≤ u := le_mul_of_one_le_right (by linarith) hP1
  have hPu : (fp.P : ℝ) ≤ u := le_mul_of_one_le_left (by linarith) hk
  have hu1 : 1 ≤ u := hk.trans hku
  have huw : u ≤ w := by linarith
  have hw5 : 5002 ≤ w := by linarith
  have hw1 : 1 ≤ w := by linarith
  have hw0 : 0 ≤ w := by linarith
  have hEw : E ≤ w ^ c := pow_le_pow_left₀ (by linarith) (hku.trans huw) c
  have hpw : ∀ a b : ℕ, a ≤ b → w ^ a ≤ w ^ b := fun a b h => pow_le_pow_right₀ hw1 h
  have hw2 : (100000 : ℝ) ≤ w ^ 2 := by nlinarith only [hk, hku]
  have hstep : ∀ (a b : ℕ) (r : ℝ), a + 1 = b → r ≤ 5002 → r * w ^ a ≤ w ^ b :=
      fun a b r hab hr => by
    rw [← hab, pow_succ]
    have := mul_le_mul_of_nonneg_left (by linarith : r ≤ w) (pow_nonneg hw0 a)
    linarith
  -- `r E ≤ w^(c+1)` for constants `0 ≤ r ≤ 5002`
  have hcE : ∀ r : ℝ, 0 ≤ r → r ≤ 5002 → r * E ≤ w ^ (c + 1) := fun r hr0 hr => by
    have := mul_le_mul_of_nonneg_left hEw hr0
    linarith [hstep c (c + 1) r rfl hr]
  have hX := fp.Xmax_le_pow (dB := dB) hk hL hHm hdB hHed hHedk hH hHk hcB
  have hLp := fp.log_potMax_le_pow hk hcB
  have hXX1 : 1 ≤ fp.Xmax dB H := fp.one_le_X hHed dB hH _
  have hLB0 : 0 ≤ (D : ℝ) * fp.Xmax dB H ^ D :=
    mul_nonneg (Nat.cast_nonneg D) (pow_nonneg (by linarith) D)
  have hLB : (D : ℝ) * fp.Xmax dB H ^ D ≤ w ^ Q := by
    have hX1 : 1 ≤ fp.Xmax dB H := fp.one_le_X hHed dB hH _
    have hD2 : (D : ℝ) ≤ 2 ^ D := by exact_mod_cast (Nat.lt_two_pow_self).le
    have h2w : (2 : ℝ) ^ D ≤ w ^ D := pow_le_pow_left₀ (by norm_num) (by linarith) D
    have hXD : fp.Xmax dB H ^ D ≤ (w ^ (113 * c + 116)) ^ D :=
      pow_le_pow_left₀ (by linarith) hX D
    calc (D : ℝ) * fp.Xmax dB H ^ D ≤ w ^ D * (w ^ (113 * c + 116)) ^ D :=
          mul_le_mul (hD2.trans h2w) hXD (by positivity) (by positivity)
      _ = w ^ D * w ^ ((113 * c + 116) * D) := by rw [← pow_mul]
      _ = w ^ Q := by rw [← pow_add, hQ]; congr 1; ring
  -- the final comparison
  have haux := fp.log_modeStar_le_aux D dB (H := H) (δc := δc) (N := N) (k := k) (E := E)
    (by linarith) hE1 hdB hHed hHedk hH hδck hN0 hNk hcB
  have hdB1 : (dB : ℝ) + 1 ≤ w ^ (c + 1) := by
    have := hcE 2 (by norm_num) (by norm_num); linarith
  have hsum1 : (D : ℝ) * fp.Xmax dB H ^ D + E + 6 ≤ w ^ (Q + c + 1) := by
    have a1 : w ^ Q ≤ w ^ (Q + c) := hpw _ _ (by omega)
    have a2 : w ^ c ≤ w ^ (Q + c) := hpw _ _ (by omega)
    have a3 : 1 ≤ w ^ (Q + c) := one_le_pow₀ hw1
    have a4 := hstep (Q + c) (Q + c + 1) 8 (by omega) (by norm_num)
    linarith
  have hT1 : 4 * ((dB : ℝ) + 1) * ((D : ℝ) * fp.Xmax dB H ^ D + E + 6) ≤
      w ^ (Q + 2 * c + 3) := by
    calc 4 * ((dB : ℝ) + 1) * ((D : ℝ) * fp.Xmax dB H ^ D + E + 6) ≤
          w * w ^ (c + 1) * w ^ (Q + c + 1) :=
          mul_le_mul (mul_le_mul (by linarith) hdB1 (by positivity) hw0) hsum1
            (by linarith) (by positivity)
      _ = w ^ (Q + 2 * c + 3) := by ring
  have hE3 : E ^ 3 ≤ w ^ (3 * c) := by
    calc E ^ 3 ≤ (w ^ c) ^ 3 := pow_le_pow_left₀ (by linarith) hEw 3
      _ = w ^ (3 * c) := by ring
  have b1 : w ^ (Q + 2 * c + 3) ≤ w ^ (Q + 4 * c + 3) := hpw _ _ (by omega)
  have b2 : w ^ (3 * c) ≤ w ^ (Q + 4 * c + 3) := hpw _ _ (by omega)
  have b3 : w ≤ w ^ (Q + 4 * c + 3) := by
    calc w = w ^ 1 := (pow_one w).symm
      _ ≤ w ^ (Q + 4 * c + 3) := hpw _ _ (by omega)
  have b4 : w ^ (2 * c + 3) ≤ w ^ (Q + 4 * c + 3) := hpw _ _ (by omega)
  have b5 : w ^ c ≤ w ^ (Q + 4 * c + 3) := hpw _ _ (by omega)
  have b6 : 1 ≤ w ^ (Q + 4 * c + 3) := one_le_pow₀ hw1
  have b7 := hstep (Q + 4 * c + 3) (Q + 4 * c + 4) 13 (by omega) (by norm_num)
  have hkw : k ≤ w := hku.trans huw
  have hlog : Real.log (fp.modeStar D dB H δc N k) ≤ w ^ (Q + 4 * c + 4) := by
    linarith
  calc Real.log (fp.modeStar D dB H δc N k) ≤ w ^ (Q + 4 * c + 4) := hlog
    _ = 5002 ^ (Q + 4 * c + 4) * u ^ (Q + 4 * c + 4) := by rw [hw, mul_pow]
    _ ≤ ((5002 ^ (Q + 4 * c + 4) + (Q + 4 * c + 4) : ℕ) : ℝ) *
          u ^ (5002 ^ (Q + 4 * c + 4) + (Q + 4 * c + 4)) := by
        push_cast
        exact mul_le_mul (le_add_of_nonneg_right (by positivity))
          (pow_le_pow_right₀ hu1 (Nat.le_add_left _ _)) (by positivity) (by positivity)

namespace ColorSetup
variable {V : Type*} [DecidableEq V] (K : ColorSetup V) (T : AdmTree V)

/-- The top score of the group of a present central vertex is nonnegative (blueprint line 1934:
the ball radii of the actual groups are at most the uniform radius). -/
theorem grp_top_nonneg {Nv : ℕ} {I : T.Cell} {v : V} (hv : v ∈ T.X I) {ρ : Fin K.d0} {z : V}
    {g : ℤ} (h : (K.grp T Nv I v).2.1 = some (ρ, z, g)) : 0 ≤ g := by
  have hp : K.prim (T.st I) v = some (ρ, z, g) := by
    rw [← K.colorData_fst]; exact h
  obtain ⟨-, hg, -⟩ := sigData_spec hp
  rw [hg]
  exact (K.roundTop_psc_mem (A := T.st I) hv ρ).1

end ColorSetup

/-! ### The Fourier expansion of the squared gauge `(ζ^ρ)²` (blueprint lines 1944 and 2056) -/

/-- The periodic branch profile `t ↦ b(fract t)`. -/
noncomputable def fractProfile (δ t : ℝ) : ℝ := branchProfile δ (Int.fract t)

/-- Near any point the periodic profile is a sum of two translates of the profile. -/
theorem fractProfile_eventuallyEq {δ : ℝ} (hδ : 0 < δ) (t₀ : ℝ) :
    fractProfile δ =ᶠ[nhds t₀] fun t =>
      branchProfile δ (t - ⌊t₀⌋) + branchProfile δ (t - ⌊t₀⌋ + 1) := by
  have hU : Set.Ioo ((⌊t₀⌋ : ℝ) - 1) (⌊t₀⌋ + 1) ∈ nhds t₀ := by
    refine Ioo_mem_nhds ?_ ?_
    · linarith [Int.floor_le t₀]
    · exact Int.lt_floor_add_one t₀
  filter_upwards [hU] with t ht
  unfold fractProfile
  rcases le_or_gt (⌊t₀⌋ : ℝ) t with h | h
  · have hf : Int.fract t = t - ⌊t₀⌋ := by
      rw [Int.fract, Int.floor_eq_iff.mpr ⟨h, ht.2⟩]
    rw [hf, branchProfile_eq_zero_of_ge (s := t - ⌊t₀⌋ + 1) hδ (by linarith), add_zero]
  · have hfl : ⌊t⌋ = ⌊t₀⌋ - 1 := by
      rw [Int.floor_eq_iff]; push_cast; constructor <;> linarith [ht.1]
    have hf : Int.fract t = t - ⌊t₀⌋ + 1 := by
      rw [Int.fract, hfl]; push_cast; ring
    rw [hf, branchProfile_eq_zero_of_le (s := t - ⌊t₀⌋) hδ (by linarith), zero_add]

theorem fractProfile_contDiff {δ : ℝ} (hδ : 0 < δ) :
    ContDiff ℝ (⊤ : ℕ∞) (fractProfile δ) := by
  refine contDiff_iff_contDiffAt.mpr fun t₀ => ?_
  refine ContDiffAt.congr_of_eventuallyEq ?_ (fractProfile_eventuallyEq hδ t₀)
  refine (ContDiff.add ?_ ?_).contDiffAt
  · exact (branchProfile_contDiff δ).comp (contDiff_id.sub contDiff_const)
  · exact (branchProfile_contDiff δ).comp ((contDiff_id.sub contDiff_const).add contDiff_const)

/-- Derivative bounds for the periodic profile: `|D^i| ≤ (2B)^i` for `i ≤ m`. -/
theorem fractProfile_deriv_le {δ : ℝ} (hδ : 0 < δ) {m i : ℕ} (hi : i ≤ m) (t₀ : ℝ) :
    |iteratedDeriv i (fractProfile δ) t₀| ≤
      (2 * (bumpConst * (8 * ((m : ℝ) + 1)) ^ 32 * (2 / δ))) ^ i := by
  set B := bumpConst * (8 * ((m : ℝ) + 1)) ^ 32 * (2 / δ)
  have hB0 : 0 ≤ B := by have := one_le_bumpConst; positivity
  rcases Nat.eq_zero_or_pos i with rfl | hi1
  · simp only [iteratedDeriv_zero, pow_zero, fractProfile]
    have := branchProfile_mem δ (Int.fract t₀)
    rw [abs_of_nonneg this.1]; exact this.2
  rw [(fractProfile_eventuallyEq hδ t₀).iteratedDeriv_eq]
  have hs := branchProfile_contDiff δ
  have e : (fun t => branchProfile δ (t - ⌊t₀⌋) + branchProfile δ (t - ⌊t₀⌋ + 1)) =
      (fun t => branchProfile δ (t - ⌊t₀⌋)) + fun t => branchProfile δ (t - (⌊t₀⌋ - 1)) := by
    funext t; simp only [Pi.add_apply]; congr 2; ring
  have hc : ∀ c : ℝ, ContDiffAt ℝ i (fun t => branchProfile δ (t - c)) t₀ := fun c =>
    ((hs.comp (contDiff_id.sub contDiff_const)).of_le (by exact_mod_cast le_top)).contDiffAt
  rw [e, iteratedDeriv_add (hc _) (hc _), iteratedDeriv_comp_sub_const,
    iteratedDeriv_comp_sub_const]
  have h1 := branchProfile_deriv_le hδ hi (t₀ - ⌊t₀⌋)
  have h2 := branchProfile_deriv_le hδ hi (t₀ - (⌊t₀⌋ - 1))
  have h3 : (2 : ℝ) ≤ 2 ^ i := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ i := pow_le_pow_right₀ (by norm_num) hi1
  rw [mul_pow]
  calc _ ≤ |iteratedDeriv i (branchProfile δ) (t₀ - ⌊t₀⌋)| +
        |iteratedDeriv i (branchProfile δ) (t₀ - (⌊t₀⌋ - 1))| := abs_add_le _ _
    _ ≤ B ^ i + B ^ i := add_le_add h1 h2
    _ ≤ 2 ^ i * B ^ i := by nlinarith only [pow_nonneg hB0 i, h3]

/-- The squared periodic gauge `w ↦ (Π_i b({w_i - ρ_i}))²` on `ℝ^d`. -/
noncomputable def gaugeSq {d : ℕ} (δ : ℝ) (ρ : Fin d → ℝ) (w : Fin d → ℝ) : ℂ :=
  chartCoordinateProduct (fractProfile δ) (w - ρ) * chartCoordinateProduct (fractProfile δ) (w - ρ)

theorem centerCut_sq_eq (z : ChartTag) (δ : ℝ) (ρ : Fin z.dim → ℝ) (y : ℝ) :
    ((centerCut z δ ρ y : ℝ) : ℂ) ^ 2 = gaugeSq δ ρ (fun i => z.θ i * y) := by
  simp only [gaugeSq, centerCut, branchCutoffValue, chartCoordinateProduct, fractProfile,
    Pi.sub_apply]
  push_cast
  ring

theorem gaugeSq_periodic {d : ℕ} (δ : ℝ) (ρ w : Fin d → ℝ) (j : Fin d → ℤ) :
    gaugeSq δ ρ (w + fun i => (j i : ℝ)) = gaugeSq δ ρ w := by
  have : ∀ i, fractProfile δ ((w + fun i => (j i : ℝ)) i - ρ i) = fractProfile δ (w i - ρ i) :=
    fun i => by
      simp only [fractProfile, Pi.add_apply,
        show w i + (j i : ℝ) - ρ i = (w i - ρ i) + (j i : ℤ) by ring, Int.fract_add_intCast]
  simp only [gaugeSq, chartCoordinateProduct, Pi.sub_apply, this]

theorem gaugeSq_contDiff {d : ℕ} {δ : ℝ} (hδ : 0 < δ) (ρ : Fin d → ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (gaugeSq δ ρ) := by
  have h : ContDiff ℝ (⊤ : ℕ∞) fun w : Fin d → ℝ =>
      chartCoordinateProduct (fractProfile δ) (w - ρ) :=
    (chartCoordinateProduct_smooth (d := d) (fractProfile_contDiff hδ)).comp
      (contDiff_id.sub contDiff_const)
  exact h.mul h

theorem gaugeSq_norm_le {d : ℕ} (δ : ℝ) (ρ w : Fin d → ℝ) : ‖gaugeSq δ ρ w‖ ≤ 1 := by
  have h : ‖chartCoordinateProduct (fractProfile δ) (w - ρ)‖ ≤ 1 := by
    simp only [chartCoordinateProduct, norm_prod, Complex.norm_real, Real.norm_eq_abs]
    refine Finset.prod_le_one₀ (fun i _ => abs_nonneg _) fun i _ => ?_
    have := branchProfile_mem δ (Int.fract ((w - ρ) i))
    rw [fractProfile, abs_of_nonneg this.1]; exact this.2
  simp only [gaugeSq, norm_mul]
  calc _ ≤ 1 * 1 := mul_le_mul h h (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

/-- The derivative bound `‖D^m (ζ²)‖ ≤ (4dB)^m` of the squared gauge. -/
theorem gaugeSq_iteratedFDeriv_le {d : ℕ} {δ : ℝ} (hδ : 0 < δ) (ρ w : Fin d → ℝ) (m : ℕ) :
    ‖iteratedFDeriv ℝ m (gaugeSq δ ρ) w‖ ≤
      (2 * ((d : ℝ) * (2 * (bumpConst * (8 * ((m : ℝ) + 1)) ^ 32 * (2 / δ))))) ^ m := by
  set R := 2 * (bumpConst * (8 * ((m : ℝ) + 1)) ^ 32 * (2 / δ))
  have hR : 0 ≤ R := by have := one_le_bumpConst; positivity
  set F : (Fin d → ℝ) → ℂ := fun w => chartCoordinateProduct (fractProfile δ) (w - ρ)
  have hF : ContDiff ℝ (⊤ : ℕ∞) F := (chartCoordinateProduct_smooth (d := d)
    (fractProfile_contDiff hδ)).comp (contDiff_id.sub contDiff_const)
  have hFi : ∀ i ≤ m, ‖iteratedFDeriv ℝ i F w‖ ≤ ((d : ℝ) * R) ^ i := by
    intro i hi
    have e : F = fun w => chartCoordinateProduct (fractProfile δ) (w - ρ) := rfl
    rw [e, iteratedFDeriv_comp_sub]
    refine (chartCoordinateProduct_derivative_geometric (fractProfile_contDiff hδ) (w - ρ) hR
      fun j hj x => ?_)
    exact (fractProfile_deriv_le hδ (hj.trans hi) x).trans (le_of_eq rfl)
  have h := norm_iteratedFDeriv_mul_le (N := (⊤ : ℕ∞)) hF hF w (n := m) (by exact_mod_cast le_top)
  refine h.trans ?_
  have hdR : 0 ≤ (d : ℝ) * R := by positivity
  calc ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * ‖iteratedFDeriv ℝ i F w‖ *
        ‖iteratedFDeriv ℝ (m - i) F w‖ ≤
      ∑ i ∈ Finset.range (m + 1), (m.choose i : ℝ) * ((d : ℝ) * R) ^ i *
        ((d : ℝ) * R) ^ (m - i) := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hi' : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        gcongr
        · exact hFi i hi'
        · exact hFi (m - i) (Nat.sub_le _ _)
    _ = (2 * ((d : ℝ) * R)) ^ m := by
        rw [two_mul, add_pow]
        refine Finset.sum_congr rfl fun i _ => by ring

/-- Blueprint line 2056: the squared gauge is, uniformly in `w` and in the offset, the sum of its
Fourier modes in the box `|v|_∞ ≤ 2^(K+1)` up to `2B/2^K`, with coefficients bounded by one and
`B = 7^d A √d^(d+1)` for the derivative constant `A` of order `d + 1`. -/
theorem gaugeSq_truncate {d : ℕ} (hd : 1 ≤ d) {δ : ℝ} (hδ : 0 < δ) (ρ : Fin d → ℝ) (K : ℕ) :
    ∃ c : (Fin d → ℤ) → ℂ, (∀ v, ‖c v‖ ≤ 1) ∧ ∀ w,
      ‖gaugeSq δ ρ w - ∑ v ∈ frequencyBox d (2 ^ (K + 1)),
        c v * (Real.fourierChar (∑ i, (v i : ℝ) * w i) : ℂ)‖ ≤
      2 * ((7 : ℝ) ^ d * (2 * ((d : ℝ) * (2 * (bumpConst * (8 * (((d + 1 : ℕ) : ℝ) + 1)) ^ 32 *
        (2 / δ))))) ^ (d + 1) * Real.sqrt d ^ (d + 1)) / 2 ^ K := by
  set A := (2 * ((d : ℝ) * (2 * (bumpConst * (8 * (((d + 1 : ℕ) : ℝ) + 1)) ^ 32 *
    (2 / δ))))) ^ (d + 1)
  have hA : 0 ≤ A := by have := one_le_bumpConst; positivity
  obtain ⟨hsum, hsumm, hdecay, hbd⟩ := periodic_fourier_expansion_of_fderiv (m := d + 1) (A := A)
    (B := 1) hd (Nat.lt_succ_self d) (gaugeSq δ ρ) (gaugeSq_contDiff hδ ρ)
    (fun w j => gaugeSq_periodic δ ρ w j) (fun w => gaugeSq_iteratedFDeriv_le hδ ρ w (d + 1))
    (fun w => gaugeSq_norm_le δ ρ w)
  set c := periodicFourierCoeff (gaugeSq δ ρ)
  clear_value c A
  refine ⟨c, hbd, fun w => ?_⟩
  have hB0 : 0 ≤ (7 : ℝ) ^ d * A * Real.sqrt d ^ (d + 1) := by positivity
  have hshell : ∀ T : ℝ, 1 ≤ T → (∑ f : Unit, ∑ v ∈ frequencyShell d T, ‖c (f, v).2‖) * T ≤
      (7 : ℝ) ^ d * A * Real.sqrt d ^ (d + 1) := by
    intro T hT
    have h := sum_frequencyShell_le hA hT c hdecay
    simp only [Finset.univ_unique, Finset.sum_singleton]
    have hTp : 0 < T := by linarith
    have e : T ^ ((d : ℝ) - ((d + 1 : ℕ) : ℝ)) = T⁻¹ := by
      rw [show (d : ℝ) - ((d + 1 : ℕ) : ℝ) = -1 by push_cast; ring, Real.rpow_neg_one]
    rw [e] at h
    calc (∑ v ∈ frequencyShell d T, ‖c v‖) * T ≤
        (7 : ℝ) ^ d * A * Real.sqrt d ^ (d + 1) * T⁻¹ * T := by gcongr
      _ = _ := by field_simp
  have hsa : Summable fun p : Unit × (Fin d → ℤ) => ‖c p.2‖ := by
    exact (Equiv.punitProd (Fin d → ℤ)).summable_iff.mpr hsumm
  have hF : HasSum (fun p : Unit × (Fin d → ℤ) => c p.2 *
      (Real.fourierChar (∑ i, (p.2 i : ℝ) * w i) : ℂ)) (gaugeSq δ ρ w) :=
    (Equiv.punitProd (Fin d → ℤ)).hasSum_iff (f := fun v => c v *
      (Real.fourierChar (∑ i, (v i : ℝ) * w i) : ℂ)) |>.mpr (hsum w)
  have he : ∀ (p : Unit × (Fin d → ℤ)) (w : Fin d → ℝ),
      ‖(Real.fourierChar (∑ i, (p.2 i : ℝ) * w i) : ℂ)‖ = 1 := fun p w => Circle.norm_coe _
  have h := hasSum_box_truncate (ι := Unit) (T := Fin d → ℝ)
    (fun p : Unit × (Fin d → ℤ) => c p.2) hsa hB0 hshell K
    (fun p w => (Real.fourierChar (∑ i, (p.2 i : ℝ) * w i) : ℂ)) he (gaugeSq δ ρ) w (by exact hF)
  convert h using 3
  rw [Finset.sum_product, Fintype.sum_unique]

/-- The truncation error constant of the squared gauge (`gaugeSq_truncate`). -/
noncomputable def gaugeTail (d : ℕ) (δ : ℝ) : ℝ :=
  (7 : ℝ) ^ d * (2 * ((d : ℝ) * (2 * (bumpConst * (8 * (((d + 1 : ℕ) : ℝ) + 1)) ^ 32 *
    (2 / δ))))) ^ (d + 1) * Real.sqrt d ^ (d + 1)

theorem gaugeTail_nonneg (d : ℕ) {δ : ℝ} (hδ : 0 < δ) : 0 ≤ gaugeTail d δ := by
  unfold gaugeTail; have := one_le_bumpConst; positivity

/-- `gaugeSq_truncate` in every dimension (in dimension zero the gauge is one). -/
theorem gaugeSq_truncate' (d : ℕ) {δ : ℝ} (hδ : 0 < δ) (ρ : Fin d → ℝ) (K : ℕ) :
    ∃ c : (Fin d → ℤ) → ℂ, (∀ v, ‖c v‖ ≤ 1) ∧ ∀ w,
      ‖gaugeSq δ ρ w - ∑ v ∈ frequencyBox d (2 ^ (K + 1)),
        c v * (Real.fourierChar (∑ i, (v i : ℝ) * w i) : ℂ)‖ ≤ 2 * gaugeTail d δ / 2 ^ K := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · refine ⟨fun _ => 1, fun _ => by simp, fun w => ?_⟩
    have hbox : frequencyBox 0 (2 ^ (K + 1)) = {fun i => Fin.elim0 i} := by
      ext v; simp only [Finset.mem_singleton]
      constructor
      · intro _; funext i; exact Fin.elim0 i
      · intro _; simp only [frequencyBox, Fintype.mem_piFinset]; exact fun i => Fin.elim0 i
    rw [hbox, Finset.sum_singleton]
    simp only [gaugeSq, chartCoordinateProduct, Finset.univ_eq_empty, Finset.prod_empty,
      Finset.sum_empty, mul_one, AddChar.map_zero_eq_one, Circle.coe_one, sub_self, norm_zero]
    have := gaugeTail_nonneg 0 hδ
    positivity
  · exact gaugeSq_truncate hd hδ ρ K

/-! ## The gauge multiplier on the true supports (blueprint line 1944) -/

section GaugeExact
variable {d : ℕ}

/-- Blueprint lines 1942-1944 ("slightly enlarge the cutoffs inside each branch region, making them
one on the required supports, and extend by zero at its cuts"): the enlarged cutoff of parameter
`δ/2` is one wherever the true cutoff of parameter `δ` is nonzero (the true cutoff vanishes within
`δ` of each cut, `branchProfile_eq_zero_near_cut`) and zero at the cuts. Hence the four true
cutoffs times the four gauge phases `e(c_j p_{ρ_j}(y_j))` equal exactly the four true cutoffs times
the smooth periodic multiplier `gaugeMult (δ/2)` at the torus point. -/
theorem gauge_factors_eq_mult_exact {δ : ℝ} (hδ : 0 < δ) (θ : Fin d → ℝ)
    (C : Matrix (Fin d) (Fin d) ℚ) (lam : ℝ) {Q0 : ℕ} (hQ0 : 0 < Q0) (l' : Fin 4)
    (ρ : Fin 4 → Fin d → ℝ) (x t : ℝ) :
    (∏ j : Fin 4, (branchCutoffValue δ (ρ j) (fun a => θ a * (x + ((j : ℕ) : ℝ) * t)) : ℂ)) *
        (Real.fourierChar (∑ j : Fin 4, (slotCoeff j : ℝ) * (lam * (x + ((j : ℕ) : ℝ) * t) ^ 2 +
          chartMatrixPhase C (fun a => θ a * (x + ((j : ℕ) : ℝ) * t))
            (branchLift (ρ j) (fun a => θ a * (x + ((j : ℕ) : ℝ) * t))))) : ℂ) =
      (∏ j : Fin 4, (branchCutoffValue δ (ρ j) (fun a => θ a * (x + ((j : ℕ) : ℝ) * t)) : ℂ)) *
        gaugeMult (δ / 2) Q0 l' C ρ (torusPt θ Q0 l' x t) := by
  have hδ2 : 0 < δ / 2 := half_pos hδ
  set s : Fin 4 → Fin d → ℝ := fun j a => Int.fract (θ a * (x + ((j : ℕ) : ℝ) * t) - ρ j a)
  have hW := fun j => torusW_torusPt θ hQ0 l' j x t
  have hWa : ∀ j a, torusW Q0 l' j (torusPt θ Q0 l' x t) a = θ a * (x + ((j : ℕ) : ℝ) * t) :=
    fun j a => congrFun (hW j) a
  have hM : gaugeMult (δ / 2) Q0 l' C ρ (torusPt θ Q0 l' x t) =
      (∏ j : Fin 4, ∏ a, (branchProfile (δ / 2) (s j a) : ℂ)) *
        (Real.fourierChar (∑ j : Fin 4, (slotCoeff j : ℝ) *
          chartMatrixPhase C (fun a => θ a * (x + ((j : ℕ) : ℝ) * t))
            (gaugeCarry θ ρ x t j)) : ℂ) := by
    unfold gaugeMult gaugeTerm
    simp only [gaugeCarry_eq_carryVec θ hQ0 l' ρ x t]
    simp only [hW]
    congr 1
    refine Finset.prod_congr rfl fun j _ => Finset.prod_congr rfl fun a _ => ?_
    simp only [s, gaugeFloor, hWa, Int.fract]
  rw [gauge_cancel θ C lam ρ x t, hM]
  set E := (Real.fourierChar (∑ j : Fin 4, (slotCoeff j : ℝ) *
    chartMatrixPhase C (fun a => θ a * (x + ((j : ℕ) : ℝ) * t)) (gaugeCarry θ ρ x t j)) : ℂ)
  have hχ : ∀ j, branchCutoffValue δ (ρ j) (fun a => θ a * (x + ((j : ℕ) : ℝ) * t)) =
      ∏ a, branchProfile δ (s j a) := fun j => rfl
  by_cases hin : ∀ j a, δ < s j a ∧ s j a < 1 - δ
  · have hone : ∏ j : Fin 4, ∏ a, (branchProfile (δ / 2) (s j a) : ℂ) = 1 := by
      refine Finset.prod_eq_one fun j _ => Finset.prod_eq_one fun a _ => ?_
      rw [branchProfile_eq_one hδ2 (by linarith [(hin j a).1]) (by linarith [(hin j a).2])]
      simp
    rw [hone, one_mul]
  · push Not at hin
    obtain ⟨j, a, hja⟩ := hin
    have hz : branchProfile δ (s j a) = 0 := by
      refine branchProfile_eq_zero_near_cut hδ ?_
      by_cases h : δ < s j a
      · exact Or.inr (hja h)
      · exact Or.inl (not_lt.mp h)
    have hχ0 : (branchCutoffValue δ (ρ j) (fun a => θ a * (x + ((j : ℕ) : ℝ) * t)) : ℂ) = 0 := by
      rw [hχ j, Finset.prod_eq_zero (Finset.mem_univ a) hz]; simp
    rw [Finset.prod_eq_zero (Finset.mem_univ j) hχ0, zero_mul, zero_mul]

end GaugeExact

/-- The full absolute Fourier norm of a smooth `1`-periodic function on `ℝ^d` with supremum bound
`B` and derivative bound `A` of order `d + 1` (blueprint line 1944: "its Gevrey and absolute
Fourier bounds"): it is the sum of its absolutely convergent Fourier series, and
`Σ_v |cHat_v| ≤ 5^d B + 2 · 7^d A √d^(d+1)`. -/
theorem periodic_fourierNorm_le {d : ℕ} (hd : 1 ≤ d) (f : (Fin d → ℝ) → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hper : ∀ x (j : Fin d → ℤ), f (x + fun i => (j i : ℝ)) = f x)
    {A B : ℝ} (hA : 0 ≤ A) (hAd : ∀ x, ‖iteratedFDeriv ℝ (d + 1) f x‖ ≤ A)
    (hB : ∀ x, ‖f x‖ ≤ B) :
    (∀ x, HasSum (fun v => periodicFourierCoeff f v *
        (Real.fourierChar (∑ i, (v i : ℝ) * x i) : ℂ)) (f x)) ∧
      Summable (fun v => ‖periodicFourierCoeff f v‖) ∧
      ∑' v, ‖periodicFourierCoeff f v‖ ≤
        5 ^ d * B + 2 * ((7 : ℝ) ^ d * A * Real.sqrt d ^ (d + 1)) := by
  obtain ⟨hsum, hsumm, hdecay, hbd⟩ := periodic_fourier_expansion_of_fderiv (m := d + 1) (A := A)
    (B := B) hd (Nat.lt_succ_self d) f hf hper hAd hB
  set c := periodicFourierCoeff f
  refine ⟨hsum, hsumm, ?_⟩
  set M := (7 : ℝ) ^ d * A * Real.sqrt d ^ (d + 1)
  have hM0 : 0 ≤ M := by positivity
  have hshell : ∀ T : ℝ, 1 ≤ T → (∑ f : Unit, ∑ v ∈ frequencyShell d T, ‖c (f, v).2‖) * T ≤ M := by
    intro T hT
    have h := sum_frequencyShell_le hA hT c hdecay
    simp only [Finset.univ_unique, Finset.sum_singleton]
    have e : T ^ ((d : ℝ) - ((d + 1 : ℕ) : ℝ)) = T⁻¹ := by
      rw [show (d : ℝ) - ((d + 1 : ℕ) : ℝ) = -1 by push_cast; ring, Real.rpow_neg_one]
    rw [e] at h
    calc (∑ v ∈ frequencyShell d T, ‖c v‖) * T ≤ M * T⁻¹ * T := by gcongr
      _ = M := by field_simp
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hbd 0)
  refine hsumm.tsum_le_of_sum_le fun s => ?_
  rw [← Finset.sum_filter_add_sum_filter_not s (· ∈ frequencyBox d (2 ^ (0 + 1)))]
  have h1 : ∑ v ∈ s.filter (· ∈ frequencyBox d (2 ^ (0 + 1))), ‖c v‖ ≤ 5 ^ d * B := by
    calc ∑ v ∈ s.filter (· ∈ frequencyBox d (2 ^ (0 + 1))), ‖c v‖
        ≤ ∑ v ∈ frequencyBox d (2 ^ (0 + 1)), ‖c v‖ :=
          Finset.sum_le_sum_of_subset_of_nonneg (fun v hv => (Finset.mem_filter.mp hv).2)
            fun _ _ _ => norm_nonneg _
      _ ≤ ∑ _v ∈ frequencyBox d (2 ^ (0 + 1)), B := Finset.sum_le_sum fun v _ => hbd v
      _ = 5 ^ d * B := by
          rw [Finset.sum_const, card_frequencyBox, nsmul_eq_mul]; push_cast; ring
  have h2 : ∑ v ∈ s.filter (· ∉ frequencyBox d (2 ^ (0 + 1))), ‖c v‖ ≤ 2 * M := by
    have h := box_tail_le (ι := Unit) (fun p : Unit × (Fin d → ℤ) => c p.2) hM0 hshell 0
      ((s.filter (· ∉ frequencyBox d (2 ^ (0 + 1)))).map
        ⟨fun v => ((), v), fun _ _ h => (Prod.ext_iff.mp h).2⟩)
      (fun p hp => by
        obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hp
        exact (Finset.mem_filter.mp hv).2)
    rw [Finset.sum_map, pow_zero, div_one] at h
    exact h
  linarith

section GaugeFourier
variable {d : ℕ}

/-- The derivative constant of order `2d + 1` of the multiplier (`gaugeMult_deriv_le`), with
`Q₀` and the entry bound `C_m` as real parameters. -/
noncomputable def gaugeMultA (d : ℕ) (Q0 Cm δ : ℝ) : ℝ :=
  3 ^ (4 * d) * (4 * (4 * Q0 * (d * profR δ (d + d + 1))) +
    2 * Real.pi * (8 * ((d : ℝ) * ((d : ℝ) * (Cm * 18 * (4 * Q0)))))) ^ (d + d + 1)

/-- The truncation constant of the multiplier. -/
noncomputable def gaugeMultTail (d : ℕ) (Q0 Cm δ : ℝ) : ℝ :=
  (7 : ℝ) ^ (d + d) * gaugeMultA d Q0 Cm δ * Real.sqrt (d + d : ℕ) ^ (d + d + 1)

/-- The full Fourier norm bound of the multiplier. -/
noncomputable def gaugeMultNorm (d : ℕ) (Q0 Cm δ : ℝ) : ℝ :=
  5 ^ (d + d) + 2 * gaugeMultTail d Q0 Cm δ

end GaugeFourier

/-- The full Fourier norm bound of the squared gauge `(ζ^ρ)²`. -/
noncomputable def gaugeSqNorm (d : ℕ) (δ : ℝ) : ℝ := 5 ^ d + 2 * gaugeTail d δ

/-- Truncation of a smooth `1`-periodic function with its Fourier coefficients: the coefficients
`cHat_v` are bounded by the supremum bound `B`, every finite absolute coefficient sum is at most the
full norm bound `5^d B + 2 · 7^d A √d^(d+1)`, and the Fourier sum over the box
`|v|_∞ ≤ 2^(K+1)` approximates the function uniformly within `2 · 7^d A √d^(d+1) / 2^K`. -/
theorem periodic_truncate_full {d : ℕ} (hd : 1 ≤ d) (f : (Fin d → ℝ) → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hper : ∀ x (j : Fin d → ℤ), f (x + fun i => (j i : ℝ)) = f x)
    {A B : ℝ} (hA : 0 ≤ A) (hAd : ∀ x, ‖iteratedFDeriv ℝ (d + 1) f x‖ ≤ A)
    (hB : ∀ x, ‖f x‖ ≤ B) (K : ℕ) :
    (∀ v, ‖periodicFourierCoeff f v‖ ≤ B) ∧
      (∀ s : Finset (Fin d → ℤ), ∑ v ∈ s, ‖periodicFourierCoeff f v‖ ≤
        5 ^ d * B + 2 * ((7 : ℝ) ^ d * A * Real.sqrt d ^ (d + 1))) ∧
      ∀ w, ‖f w - ∑ v ∈ frequencyBox d (2 ^ (K + 1)),
        periodicFourierCoeff f v * (Real.fourierChar (∑ i, (v i : ℝ) * w i) : ℂ)‖ ≤
      2 * ((7 : ℝ) ^ d * A * Real.sqrt d ^ (d + 1)) / 2 ^ K := by
  obtain ⟨hsum, hsumm, hdecay, hbd⟩ := periodic_fourier_expansion_of_fderiv (m := d + 1) (A := A)
    (B := B) hd (Nat.lt_succ_self d) f hf hper hAd hB
  obtain ⟨-, -, htsum⟩ := periodic_fourierNorm_le hd f hf hper hA hAd hB
  set c := periodicFourierCoeff f
  refine ⟨hbd, fun s => (hsumm.sum_le_tsum s fun v _ => norm_nonneg _).trans htsum, fun w => ?_⟩
  have hB0 : 0 ≤ (7 : ℝ) ^ d * A * Real.sqrt d ^ (d + 1) := by positivity
  have hshell : ∀ T : ℝ, 1 ≤ T → (∑ f : Unit, ∑ v ∈ frequencyShell d T, ‖c (f, v).2‖) * T ≤
      (7 : ℝ) ^ d * A * Real.sqrt d ^ (d + 1) := by
    intro T hT
    have h := sum_frequencyShell_le hA hT c hdecay
    simp only [Finset.univ_unique, Finset.sum_singleton]
    have e : T ^ ((d : ℝ) - ((d + 1 : ℕ) : ℝ)) = T⁻¹ := by
      rw [show (d : ℝ) - ((d + 1 : ℕ) : ℝ) = -1 by push_cast; ring, Real.rpow_neg_one]
    rw [e] at h
    calc (∑ v ∈ frequencyShell d T, ‖c v‖) * T ≤
        (7 : ℝ) ^ d * A * Real.sqrt d ^ (d + 1) * T⁻¹ * T := by gcongr
      _ = _ := by field_simp
  have hsa : Summable fun p : Unit × (Fin d → ℤ) => ‖c p.2‖ :=
    (Equiv.punitProd (Fin d → ℤ)).summable_iff.mpr hsumm
  have hF : HasSum (fun p : Unit × (Fin d → ℤ) => c p.2 *
      (Real.fourierChar (∑ i, (p.2 i : ℝ) * w i) : ℂ)) (f w) :=
    (Equiv.punitProd (Fin d → ℤ)).hasSum_iff (f := fun v => c v *
      (Real.fourierChar (∑ i, (v i : ℝ) * w i) : ℂ)) |>.mpr (hsum w)
  have he : ∀ (p : Unit × (Fin d → ℤ)) (w : Fin d → ℝ),
      ‖(Real.fourierChar (∑ i, (p.2 i : ℝ) * w i) : ℂ)‖ = 1 := fun p w => Circle.norm_coe _
  have h := hasSum_box_truncate (ι := Unit) (T := Fin d → ℝ)
    (fun p : Unit × (Fin d → ℤ) => c p.2) hsa hB0 hshell K
    (fun p w => (Real.fourierChar (∑ i, (p.2 i : ℝ) * w i) : ℂ)) he f w (by exact hF)
  convert h using 3
  rw [Finset.sum_product, Fintype.sum_unique]

/-! ### Uniformity of the Fourier constants in the center tag (blueprint line 1944) -/

theorem profR_mono {δ : ℝ} (hδ : 0 < δ) {m m' : ℕ} (h : m ≤ m') : profR δ m ≤ profR δ m' := by
  unfold profR
  have := one_le_bumpConst
  have hmm : (8 * ((m : ℝ) + 1)) ≤ 8 * ((m' : ℝ) + 1) := by
    have : (m : ℝ) ≤ m' := by exact_mod_cast h
    linarith
  gcongr

theorem one_le_profR {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (m : ℕ) : 1 ≤ profR δ m := by
  unfold profR
  have hb := one_le_bumpConst
  have h1 : (1 : ℝ) ≤ (8 * ((m : ℝ) + 1)) ^ 32 :=
    one_le_pow₀ (by have : (0 : ℝ) ≤ m := Nat.cast_nonneg m; linarith)
  have h2 : (1 : ℝ) ≤ 2 / δ := by rw [le_div_iff₀ hδ]; linarith
  exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hb h1) h2

theorem gaugeMultA_nonneg {δ : ℝ} (hδ : 0 < δ) (d : ℕ) {Q0 Cm : ℝ} (hQ0 : 0 ≤ Q0)
    (hCm : 0 ≤ Cm) : 0 ≤ gaugeMultA d Q0 Cm δ := by
  unfold gaugeMultA; have := profR_nonneg hδ (d + d + 1); have := Real.pi_pos; positivity

/-- The derivative constant of the multiplier increases with the dimension, `Q₀` and `C_m`. -/
theorem gaugeMultA_mono {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {d d' : ℕ} (hd : 1 ≤ d')
    (hdd : d ≤ d') {Q0 Q0' Cm Cm' : ℝ} (hQ0 : 0 ≤ Q0) (hQQ : Q0 ≤ Q0') (hQ1 : 1 ≤ Q0')
    (hCm0 : 0 ≤ Cm) (hCC : Cm ≤ Cm') : gaugeMultA d Q0 Cm δ ≤ gaugeMultA d' Q0' Cm' δ := by
  unfold gaugeMultA
  have hR0 : 0 ≤ profR δ (d + d + 1) := profR_nonneg hδ _
  have hRR : profR δ (d + d + 1) ≤ profR δ (d' + d' + 1) := profR_mono hδ (by omega)
  have hR1 : 1 ≤ profR δ (d' + d' + 1) := one_le_profR hδ hδ1 _
  have hdr : (d : ℝ) ≤ d' := by exact_mod_cast hdd
  have hd1 : (1 : ℝ) ≤ d' := by exact_mod_cast hd
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hpi := Real.pi_pos
  have h1 : Q0 * (d * profR δ (d + d + 1)) ≤ Q0' * (d' * profR δ (d' + d' + 1)) :=
    mul_le_mul hQQ (mul_le_mul hdr hRR hR0 (by linarith)) (by positivity) (by linarith)
  have h3 : Cm * 18 * (4 * Q0) ≤ Cm' * 18 * (4 * Q0') := by
    have := mul_le_mul hCC hQQ hQ0 (by linarith)
    nlinarith only [hQ0, hQQ, hCm0, hCC]
  have h2 : (d : ℝ) * ((d : ℝ) * (Cm * 18 * (4 * Q0))) ≤
      (d' : ℝ) * ((d' : ℝ) * (Cm' * 18 * (4 * Q0'))) :=
    mul_le_mul hdr (mul_le_mul hdr h3 (by positivity) (by linarith)) (by positivity)
      (by linarith)
  have hb0 : 0 ≤ 4 * (4 * Q0 * (d * profR δ (d + d + 1))) +
      2 * Real.pi * (8 * ((d : ℝ) * ((d : ℝ) * (Cm * 18 * (4 * Q0))))) := by positivity
  have hbb : 4 * (4 * Q0 * (d * profR δ (d + d + 1))) +
      2 * Real.pi * (8 * ((d : ℝ) * ((d : ℝ) * (Cm * 18 * (4 * Q0))))) ≤
      4 * (4 * Q0' * (d' * profR δ (d' + d' + 1))) +
      2 * Real.pi * (8 * ((d' : ℝ) * ((d' : ℝ) * (Cm' * 18 * (4 * Q0'))))) := by
    have e1 : 4 * (4 * Q0 * (d * profR δ (d + d + 1))) =
        16 * (Q0 * (d * profR δ (d + d + 1))) := by ring
    have e2 : 4 * (4 * Q0' * (d' * profR δ (d' + d' + 1))) =
        16 * (Q0' * (d' * profR δ (d' + d' + 1))) := by ring
    rw [e1, e2]
    have := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ 2 * Real.pi * 8)
    nlinarith only [h1, this]
  have hb1 : 1 ≤ 4 * (4 * Q0' * (d' * profR δ (d' + d' + 1))) +
      2 * Real.pi * (8 * ((d' : ℝ) * ((d' : ℝ) * (Cm' * 18 * (4 * Q0'))))) := by
    have : 1 ≤ Q0' * (d' * profR δ (d' + d' + 1)) :=
      one_le_mul_of_one_le_of_one_le hQ1 (one_le_mul_of_one_le_of_one_le hd1 hR1)
    have : 0 ≤ 2 * Real.pi * (8 * ((d' : ℝ) * ((d' : ℝ) * (Cm' * 18 * (4 * Q0'))))) := by
      have : 0 ≤ Cm' := by linarith
      positivity
    nlinarith
  refine mul_le_mul (pow_le_pow_right₀ (by norm_num) (by omega)) ?_ (by positivity)
    (by positivity)
  exact (pow_le_pow_left₀ hb0 hbb _).trans (pow_le_pow_right₀ hb1 (by omega))

theorem gaugeMultTail_mono {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {d d' : ℕ} (hd : 1 ≤ d')
    (hdd : d ≤ d') {Q0 Q0' Cm Cm' : ℝ} (hQ0 : 0 ≤ Q0) (hQQ : Q0 ≤ Q0') (hQ1 : 1 ≤ Q0')
    (hCm0 : 0 ≤ Cm) (hCC : Cm ≤ Cm') :
    gaugeMultTail d Q0 Cm δ ≤ gaugeMultTail d' Q0' Cm' δ := by
  unfold gaugeMultTail
  have hA := gaugeMultA_mono hδ hδ1 hd hdd hQ0 hQQ hQ1 hCm0 hCC
  have hA0 := gaugeMultA_nonneg hδ d hQ0 hCm0
  have hA0' := gaugeMultA_nonneg hδ d' (Q0 := Q0') (Cm := Cm') (by linarith) (by linarith)
  rcases Nat.eq_zero_or_pos d with rfl | hdp
  · simp only [CharP.cast_eq_zero, Real.sqrt_zero, zero_add, pow_one, mul_zero]
    exact mul_nonneg (mul_nonneg (by positivity) hA0') (by positivity)
  · have hs1 : 1 ≤ Real.sqrt (d + d : ℕ) := by
      rw [Real.one_le_sqrt]; push_cast
      have : (1 : ℝ) ≤ d := by exact_mod_cast hdp
      linarith
    have hss : Real.sqrt (d + d : ℕ) ≤ Real.sqrt (d' + d' : ℕ) :=
      Real.sqrt_le_sqrt (by
        have h : (d : ℝ) ≤ d' := (by exact_mod_cast hdd)
        push_cast; linarith)
    have hp : Real.sqrt (d + d : ℕ) ^ (d + d + 1) ≤ Real.sqrt (d' + d' : ℕ) ^ (d' + d' + 1) :=
      (pow_le_pow_left₀ (by positivity) hss _).trans
        (pow_le_pow_right₀ (hs1.trans hss) (by omega))
    have h7 : (7 : ℝ) ^ (d + d) ≤ 7 ^ (d' + d') := pow_le_pow_right₀ (by norm_num) (by omega)
    exact mul_le_mul (mul_le_mul h7 hA hA0 (by positivity)) hp (by positivity)
      (mul_nonneg (by positivity) hA0')

theorem gaugeMultNorm_mono {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {d d' : ℕ} (hd : 1 ≤ d')
    (hdd : d ≤ d') {Q0 Q0' Cm Cm' : ℝ} (hQ0 : 0 ≤ Q0) (hQQ : Q0 ≤ Q0') (hQ1 : 1 ≤ Q0')
    (hCm0 : 0 ≤ Cm) (hCC : Cm ≤ Cm') :
    gaugeMultNorm d Q0 Cm δ ≤ gaugeMultNorm d' Q0' Cm' δ := by
  unfold gaugeMultNorm
  have h1 : (5 : ℝ) ^ (d + d) ≤ 5 ^ (d' + d') := pow_le_pow_right₀ (by norm_num) (by omega)
  have h2 := gaugeMultTail_mono hδ hδ1 hd hdd hQ0 hQQ hQ1 hCm0 hCC
  linarith

theorem gaugeTail_mono {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {d d' : ℕ} (hdd : d ≤ d') :
    gaugeTail d δ ≤ gaugeTail d' δ := by
  unfold gaugeTail
  have hb := one_le_bumpConst
  rcases Nat.eq_zero_or_pos d with rfl | hdp
  · have := gaugeTail_nonneg d' hδ
    unfold gaugeTail at this
    simp only [CharP.cast_eq_zero, zero_mul, mul_zero, zero_add, pow_one, Real.sqrt_zero]
    exact this
  · have hdr : (d : ℝ) ≤ d' := by exact_mod_cast hdd
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hdp
    have hX : (8 * (((d + 1 : ℕ) : ℝ) + 1)) ≤ 8 * (((d' + 1 : ℕ) : ℝ) + 1) := by
      push_cast; linarith
    have hX0 : (0 : ℝ) ≤ 8 * (((d + 1 : ℕ) : ℝ) + 1) := by positivity
    have hδ2 : (1 : ℝ) ≤ 2 / δ := by rw [le_div_iff₀ hδ]; linarith
    have hK1 : (1 : ℝ) ≤ bumpConst * (8 * (((d + 1 : ℕ) : ℝ) + 1)) ^ 32 * (2 / δ) :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hb
        (one_le_pow₀ (by push_cast; linarith))) hδ2
    have hKK : bumpConst * (8 * (((d + 1 : ℕ) : ℝ) + 1)) ^ 32 * (2 / δ) ≤
        bumpConst * (8 * (((d' + 1 : ℕ) : ℝ) + 1)) ^ 32 * (2 / δ) := by gcongr
    have hb1 : 1 ≤ 2 * ((d : ℝ) * (2 * (bumpConst * (8 * (((d + 1 : ℕ) : ℝ) + 1)) ^ 32 *
        (2 / δ)))) :=
      one_le_mul_of_one_le_of_one_le (by norm_num)
        (one_le_mul_of_one_le_of_one_le hd1
          (one_le_mul_of_one_le_of_one_le (by norm_num) hK1))
    have hbb : 2 * ((d : ℝ) * (2 * (bumpConst * (8 * (((d + 1 : ℕ) : ℝ) + 1)) ^ 32 *
        (2 / δ)))) ≤ 2 * ((d' : ℝ) * (2 * (bumpConst * (8 * (((d' + 1 : ℕ) : ℝ) + 1)) ^ 32 *
        (2 / δ)))) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul hdr (mul_le_mul_of_nonneg_left hKK (by norm_num))
          (mul_nonneg (by norm_num) (zero_le_one.trans hK1)) (Nat.cast_nonneg _))
        (by norm_num)
    have hs1 : 1 ≤ Real.sqrt d := by rw [Real.one_le_sqrt]; exact hd1
    have hss : Real.sqrt d ≤ Real.sqrt d' := Real.sqrt_le_sqrt hdr
    refine mul_le_mul (mul_le_mul (pow_le_pow_right₀ (by norm_num) hdd)
      ((pow_le_pow_left₀ (zero_le_one.trans hb1) hbb _).trans
        (pow_le_pow_right₀ (hb1.trans hbb) (by omega)))
      (by positivity) (by positivity))
      ((pow_le_pow_left₀ (by positivity) hss _).trans
        (pow_le_pow_right₀ (hs1.trans hss) (by omega))) (by positivity) (by positivity)

/-- Blueprint lines 1944 and 2055 ("expand `(ζ^ρ)²` on the `ϑ` torus with coefficient sum at most
`D_*` and tail `D_*^{-300}`"): the squared gauge is approximated uniformly within `2 B_ζ/2^K` by its
Fourier sum over the box `|v|_∞ ≤ 2^(K+1)`, and every finite absolute sum of the coefficients is at
most the full Fourier norm `gaugeSqNorm`. -/
theorem gaugeSq_truncate_full (d : ℕ) {δ : ℝ} (hδ : 0 < δ) (ρ : Fin d → ℝ) (K : ℕ) :
    ∃ c : (Fin d → ℤ) → ℂ, (∀ s : Finset (Fin d → ℤ), ∑ v ∈ s, ‖c v‖ ≤ gaugeSqNorm d δ) ∧ ∀ w,
      ‖gaugeSq δ ρ w - ∑ v ∈ frequencyBox d (2 ^ (K + 1)),
        c v * (Real.fourierChar (∑ i, (v i : ℝ) * w i) : ℂ)‖ ≤ 2 * gaugeTail d δ / 2 ^ K := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · obtain ⟨c, hc1, hc⟩ := gaugeSq_truncate' 0 hδ ρ K
    refine ⟨c, fun s => ?_, hc⟩
    have hT := gaugeTail_nonneg 0 hδ
    calc ∑ v ∈ s, ‖c v‖ ≤ ∑ _v ∈ s, (1 : ℝ) := Finset.sum_le_sum fun v _ => hc1 v
      _ = s.card := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ ≤ 1 := by exact_mod_cast Finset.card_le_one_of_subsingleton s
      _ ≤ gaugeSqNorm 0 δ := by unfold gaugeSqNorm; rw [pow_zero]; linarith
  · obtain ⟨-, hs, he⟩ := periodic_truncate_full hd (gaugeSq δ ρ) (gaugeSq_contDiff hδ ρ)
      (fun w j => gaugeSq_periodic δ ρ w j)
      (A := (2 * ((d : ℝ) * (2 * (bumpConst * (8 * (((d + 1 : ℕ) : ℝ) + 1)) ^ 32 *
        (2 / δ))))) ^ (d + 1)) (by have := one_le_bumpConst; positivity)
      (fun w => gaugeSq_iteratedFDeriv_le hδ ρ w (d + 1)) (fun w => gaugeSq_norm_le δ ρ w) K
    refine ⟨periodicFourierCoeff (gaugeSq δ ρ), fun s => (hs s).trans (le_of_eq ?_),
      fun w => (he w).trans (le_of_eq ?_)⟩
    · unfold gaugeSqNorm gaugeTail; ring
    · unfold gaugeTail; ring

theorem gaugeSqNorm_mono {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) {d d' : ℕ} (hdd : d ≤ d') :
    gaugeSqNorm d δ ≤ gaugeSqNorm d' δ := by
  unfold gaugeSqNorm
  have h1 : (5 : ℝ) ^ d ≤ 5 ^ d' := pow_le_pow_right₀ (by norm_num) hdd
  have h2 := gaugeTail_mono hδ hδ1 hdd
  linarith

/-! ### Size of the Fourier constants (blueprint line 1944: `log B_* ≤ P^C`) -/

theorem exp_bounds_small : (2 : ℝ) ≤ Real.exp 1 ∧ (7 : ℝ) ≤ Real.exp 2 ∧ (20 : ℝ) ≤ Real.exp 3 ∧
    (8000 : ℝ) ≤ Real.exp 9 := by
  have h := Real.exp_one_gt_d9
  have h1 : (2 : ℝ) ≤ Real.exp 1 := by linarith
  have e2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  have e3 : Real.exp 3 = Real.exp 2 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
  have e9 : Real.exp 9 = Real.exp 3 * Real.exp 3 * Real.exp 3 := by
    rw [← Real.exp_add, ← Real.exp_add]; norm_num
  have h2 : (7 : ℝ) ≤ Real.exp 2 := by rw [e2]; nlinarith
  have h3 : (20 : ℝ) ≤ Real.exp 3 := by rw [e3]; nlinarith
  refine ⟨h1, h2, h3, ?_⟩
  rw [e9]; nlinarith

/-- `x ≤ exp x` for real `x`, used for crude size bounds. -/
theorem le_exp_self (x : ℝ) : x ≤ Real.exp x := by
  have := Real.add_one_le_exp x; linarith

/-- The full Fourier norm bound of the multipliers is at most `exp(T_G + 2)` with
`T_G = 12E + (2E + 1)(E³ + κ + 514E + 523) + 2E(2E + 1)`, `κ = log bumpConst`, when `d_B`,
`log H_ed` and `log (1/δ)` are at most `E`. -/
theorem gaugeMultNorm_le_exp {dB : ℕ} {Hed δ E : ℝ} (hE : 1 ≤ E) (hdB : (dB : ℝ) ≤ E)
    (hHed : 2 ≤ Hed) (hHedE : Real.log Hed ≤ E) (hδ : 0 < δ) (hδE : δ⁻¹ ≤ Real.exp E) :
    gaugeMultNorm dB (Hed ^ (dB * dB)) Hed (δ / 2) ≤
      Real.exp (12 * E + (2 * E + 1) * (E ^ 3 + Real.log bumpConst + 514 * E + 523) +
        2 * E * (2 * E + 1) + 2) := by
  obtain ⟨he1, he2, he3, he9⟩ := exp_bounds_small
  have hdB0 : (0 : ℝ) ≤ dB := Nat.cast_nonneg _
  have hκ : 0 ≤ Real.log bumpConst := Real.log_nonneg one_le_bumpConst
  have hb1 := one_le_bumpConst
  set κ := Real.log bumpConst with hκdef
  have hbump : bumpConst = Real.exp κ := (Real.exp_log (by linarith)).symm
  -- the clearing bound `Q = H_ed^(d_B²) ≤ exp(E³)`
  have hlH : 0 ≤ Real.log Hed := Real.log_nonneg (by linarith)
  have hQ : Hed ^ (dB * dB) ≤ Real.exp (E ^ 3) := by
    rw [← Real.exp_log (by positivity : 0 < Hed ^ (dB * dB)), Real.log_pow]
    refine Real.exp_le_exp.mpr ?_
    push_cast
    have h1 : (dB : ℝ) * dB ≤ E * E := mul_le_mul hdB hdB hdB0 (by linarith)
    have h2 : (dB : ℝ) * dB * Real.log Hed ≤ E * E * E :=
      mul_le_mul h1 hHedE hlH (by positivity)
    have : E ^ 3 = E * E * E := by ring
    linarith
  have hQ0 : 0 ≤ Hed ^ (dB * dB) := by positivity
  have hHedle : Hed ≤ Real.exp E := by
    rw [← Real.exp_log (by linarith : 0 < Hed)]; exact Real.exp_le_exp.mpr hHedE
  have hdBe : (dB : ℝ) ≤ Real.exp E := hdB.trans (le_exp_self E)
  -- the profile constant
  have hR : profR (δ / 2) (dB + dB + 1) ≤ Real.exp (κ + 513 * E + 514) := by
    unfold profR
    have h1 : (8 * (((dB + dB + 1 : ℕ) : ℝ) + 1)) ^ 32 ≤ Real.exp (512 * E + 512) := by
      have hx : (8 * (((dB + dB + 1 : ℕ) : ℝ) + 1)) ≤ 16 * E + 16 := by push_cast; linarith
      calc (8 * (((dB + dB + 1 : ℕ) : ℝ) + 1)) ^ 32 ≤ Real.exp (16 * E + 16) ^ 32 :=
            pow_le_pow_left₀ (by positivity) (hx.trans (le_exp_self _)) 32
        _ = Real.exp (512 * E + 512) := by rw [← Real.exp_nat_mul]; ring_nf
    have h2 : 2 / (δ / 2) ≤ Real.exp (E + 2) := by
      rw [show 2 / (δ / 2) = 4 * δ⁻¹ by field_simp; ring, Real.exp_add]
      have := mul_le_mul_of_nonneg_left hδE (by norm_num : (0 : ℝ) ≤ 4)
      nlinarith only [Real.exp_pos E, hδE, he2]
    calc bumpConst * (8 * (((dB + dB + 1 : ℕ) : ℝ) + 1)) ^ 32 * (2 / (δ / 2))
        ≤ Real.exp κ * Real.exp (512 * E + 512) * Real.exp (E + 2) := by
          rw [← hbump]; gcongr
      _ = Real.exp (κ + 513 * E + 514) := by rw [← Real.exp_add, ← Real.exp_add]; ring_nf
  have hR0 : 0 ≤ profR (δ / 2) (dB + dB + 1) := profR_nonneg (by linarith) _
  -- the base of the power
  set! b := 4 * (4 * Hed ^ (dB * dB) * (dB * profR (δ / 2) (dB + dB + 1))) +
    2 * Real.pi * (8 * ((dB : ℝ) * ((dB : ℝ) * (Hed * 18 * (4 * Hed ^ (dB * dB))))))
  have hb0 : 0 ≤ b := by have := Real.pi_pos; positivity
  have hb : b ≤ Real.exp (E ^ 3 + κ + 514 * E + 523) := by
    set! X := Real.exp (E ^ 3 + κ + 514 * E + 514)
    have hX1 : Real.exp (E ^ 3) * Real.exp E * Real.exp (κ + 513 * E + 514) ≤ X := by
      rw [← Real.exp_add, ← Real.exp_add]; exact Real.exp_le_exp.mpr (by linarith)
    have hX2 : Real.exp E * (Real.exp E * (Real.exp E * Real.exp (E ^ 3))) ≤ X := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      exact Real.exp_le_exp.mpr (by nlinarith only [hE, hκ])
    have t1 : Hed ^ (dB * dB) * (dB * profR (δ / 2) (dB + dB + 1)) ≤ X :=
      le_trans (by
        rw [← mul_assoc]
        exact mul_le_mul (mul_le_mul hQ hdBe hdB0 (Real.exp_pos _).le) hR hR0 (by positivity))
        hX1
    have t2 : (dB : ℝ) * ((dB : ℝ) * (Hed * Hed ^ (dB * dB))) ≤ X :=
      le_trans (mul_le_mul hdBe (mul_le_mul hdBe (mul_le_mul hHedle hQ hQ0 (Real.exp_pos _).le)
        (by positivity) (Real.exp_pos _).le) (by positivity) (Real.exp_pos _).le) hX2
    have hpi : Real.pi ≤ 4 := Real.pi_le_four
    have e : b = 16 * (Hed ^ (dB * dB) * (dB * profR (δ / 2) (dB + dB + 1))) +
        1152 * Real.pi * ((dB : ℝ) * ((dB : ℝ) * (Hed * Hed ^ (dB * dB)))) := by
      simp only [b]; ring
    have hX0 : 0 ≤ X := (Real.exp_pos _).le
    have ht2 : 0 ≤ (dB : ℝ) * ((dB : ℝ) * (Hed * Hed ^ (dB * dB))) := by positivity
    have h3 : 1152 * Real.pi * ((dB : ℝ) * ((dB : ℝ) * (Hed * Hed ^ (dB * dB)))) ≤ 4608 * X := by
      have := mul_le_mul (mul_le_mul_of_nonneg_left hpi (by norm_num : (0 : ℝ) ≤ 1152)) t2 ht2
        (by norm_num)
      linarith
    have h4 : 4624 * X ≤ Real.exp (E ^ 3 + κ + 514 * E + 523) := by
      rw [show E ^ 3 + κ + 514 * E + 523 = (E ^ 3 + κ + 514 * E + 514) + 9 by ring, Real.exp_add]
      have := mul_le_mul_of_nonneg_left he9 hX0
      linarith
    rw [e]; linarith
  -- assemble
  have hpowb : b ^ (dB + dB + 1) ≤ Real.exp ((2 * E + 1) * (E ^ 3 + κ + 514 * E + 523)) := by
    calc b ^ (dB + dB + 1) ≤ Real.exp (E ^ 3 + κ + 514 * E + 523) ^ (dB + dB + 1) :=
          pow_le_pow_left₀ hb0 hb _
      _ = Real.exp ((dB + dB + 1 : ℕ) * (E ^ 3 + κ + 514 * E + 523)) := by
          rw [← Real.exp_nat_mul]
      _ ≤ Real.exp ((2 * E + 1) * (E ^ 3 + κ + 514 * E + 523)) := by
          refine Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right ?_ (by positivity))
          push_cast; linarith
  have h3 : (3 : ℝ) ^ (4 * dB) ≤ Real.exp (8 * E) := by
    calc (3 : ℝ) ^ (4 * dB) ≤ Real.exp 2 ^ (4 * dB) :=
          pow_le_pow_left₀ (by norm_num) (by linarith) _
      _ = Real.exp ((4 * dB : ℕ) * 2) := by rw [← Real.exp_nat_mul]
      _ ≤ Real.exp (8 * E) := Real.exp_le_exp.mpr (by push_cast; linarith)
  have h7 : (7 : ℝ) ^ (dB + dB) ≤ Real.exp (4 * E) := by
    calc (7 : ℝ) ^ (dB + dB) ≤ Real.exp 2 ^ (dB + dB) := pow_le_pow_left₀ (by norm_num) he2 _
      _ = Real.exp ((dB + dB : ℕ) * 2) := by rw [← Real.exp_nat_mul]
      _ ≤ Real.exp (4 * E) := Real.exp_le_exp.mpr (by push_cast; linarith)
  have h5 : (5 : ℝ) ^ (dB + dB) ≤ Real.exp (4 * E) := by
    calc (5 : ℝ) ^ (dB + dB) ≤ Real.exp 2 ^ (dB + dB) :=
          pow_le_pow_left₀ (by norm_num) (by linarith) _
      _ = Real.exp ((dB + dB : ℕ) * 2) := by rw [← Real.exp_nat_mul]
      _ ≤ Real.exp (4 * E) := Real.exp_le_exp.mpr (by push_cast; linarith)
  have hs : Real.sqrt (dB + dB : ℕ) ^ (dB + dB + 1) ≤ Real.exp (2 * E * (2 * E + 1)) := by
    have h1 : Real.sqrt (dB + dB : ℕ) ≤ Real.exp (2 * E) := by
      have : Real.sqrt (dB + dB : ℕ) ≤ (dB + dB : ℕ) + 1 := by
        have := Real.sqrt_le_sqrt (le_add_of_nonneg_right zero_le_one :
          ((dB + dB : ℕ) : ℝ) ≤ (dB + dB : ℕ) + 1)
        refine le_trans this ?_
        rw [Real.sqrt_le_left (by positivity)]
        nlinarith only [(Nat.cast_nonneg (dB + dB) : (0 : ℝ) ≤ (dB + dB : ℕ))]
      refine this.trans ((Real.add_one_le_exp _).trans (Real.exp_le_exp.mpr ?_))
      push_cast; linarith
    calc Real.sqrt (dB + dB : ℕ) ^ (dB + dB + 1) ≤ Real.exp (2 * E) ^ (dB + dB + 1) :=
          pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 _
      _ = Real.exp ((dB + dB + 1 : ℕ) * (2 * E)) := by rw [← Real.exp_nat_mul]
      _ ≤ Real.exp (2 * E * (2 * E + 1)) := by
          refine Real.exp_le_exp.mpr ?_
          push_cast; nlinarith only [hdB]
  set TG := 12 * E + (2 * E + 1) * (E ^ 3 + κ + 514 * E + 523) + 2 * E * (2 * E + 1)
  have hTG : 4 * E ≤ TG := by
    have : 0 ≤ (2 * E + 1) * (E ^ 3 + κ + 514 * E + 523) := by positivity
    have : 0 ≤ 2 * E * (2 * E + 1) := by positivity
    linarith
  have htail : gaugeMultTail dB (Hed ^ (dB * dB)) Hed (δ / 2) ≤ Real.exp TG := by
    unfold gaugeMultTail gaugeMultA
    calc (7 : ℝ) ^ (dB + dB) * (3 ^ (4 * dB) * b ^ (dB + dB + 1)) *
          Real.sqrt (dB + dB : ℕ) ^ (dB + dB + 1) ≤
        Real.exp (4 * E) * (Real.exp (8 * E) *
          Real.exp ((2 * E + 1) * (E ^ 3 + κ + 514 * E + 523))) *
          Real.exp (2 * E * (2 * E + 1)) := by gcongr
      _ = Real.exp TG := by simp only [TG, ← Real.exp_add]; ring_nf
  unfold gaugeMultNorm
  calc (5 : ℝ) ^ (dB + dB) + 2 * gaugeMultTail dB (Hed ^ (dB * dB)) Hed (δ / 2) ≤
        Real.exp TG + 2 * Real.exp TG := by
        have := h5.trans (Real.exp_le_exp.mpr hTG)
        linarith
    _ ≤ Real.exp (TG + 2) := by
        rw [Real.exp_add TG 2]
        linarith [mul_le_mul_of_nonneg_left he2 (Real.exp_pos TG).le, Real.exp_pos TG]

/-- The full Fourier norm bound of the squared gauge is at most `exp(T_S + 2)` with
`T_S = 2E + (E + 1)(κ + 258E + 515) + E(E + 1)`, `κ = log bumpConst`, when `d_B` and
`log (1/δ)` are at most `E`. -/
theorem gaugeSqNorm_le_exp {dB : ℕ} {δ E : ℝ} (hE : 1 ≤ E) (hdB : (dB : ℝ) ≤ E) (hδ : 0 < δ)
    (hδE : δ⁻¹ ≤ Real.exp E) :
    gaugeSqNorm dB δ ≤
      Real.exp (2 * E + (E + 1) * (Real.log bumpConst + 258 * E + 515) + E * (E + 1) + 2) := by
  obtain ⟨he1, he2, he3, he9⟩ := exp_bounds_small
  have hdB0 : (0 : ℝ) ≤ dB := Nat.cast_nonneg _
  have hκ : 0 ≤ Real.log bumpConst := Real.log_nonneg one_le_bumpConst
  have hb1 := one_le_bumpConst
  set κ := Real.log bumpConst with hκdef
  have hbump : bumpConst = Real.exp κ := (Real.exp_log (by linarith)).symm
  have hdBe : (dB : ℝ) ≤ Real.exp E := hdB.trans (le_exp_self E)
  have hX : (8 * (((dB + 1 : ℕ) : ℝ) + 1)) ^ 32 ≤ Real.exp (256 * E + 512) := by
    have hx : (8 * (((dB + 1 : ℕ) : ℝ) + 1)) ≤ 8 * E + 16 := by push_cast; linarith
    calc (8 * (((dB + 1 : ℕ) : ℝ) + 1)) ^ 32 ≤ Real.exp (8 * E + 16) ^ 32 :=
          pow_le_pow_left₀ (by positivity) (hx.trans (le_exp_self _)) 32
      _ = Real.exp (256 * E + 512) := by rw [← Real.exp_nat_mul]; ring_nf
  have h2δ : 2 / δ ≤ Real.exp (E + 1) := by
    rw [div_eq_mul_inv, Real.exp_add]
    have := mul_le_mul he1 hδE (by positivity) (by positivity)
    linarith [mul_comm (Real.exp E) (Real.exp 1)]
  have hbase : 2 * ((dB : ℝ) * (2 * (bumpConst * (8 * (((dB + 1 : ℕ) : ℝ) + 1)) ^ 32 *
      (2 / δ)))) ≤ Real.exp (κ + 258 * E + 515) := by
    have hprod : (dB : ℝ) * (bumpConst * (8 * (((dB + 1 : ℕ) : ℝ) + 1)) ^ 32 * (2 / δ)) ≤
        Real.exp E * (Real.exp κ * Real.exp (256 * E + 512) * Real.exp (E + 1)) := by
      rw [← hbump]
      gcongr
    have e : Real.exp E * (Real.exp κ * Real.exp (256 * E + 512) * Real.exp (E + 1)) =
        Real.exp (κ + 258 * E + 513) := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]; ring_nf
    rw [e] at hprod
    have h4 : 4 * Real.exp (κ + 258 * E + 513) ≤ Real.exp (κ + 258 * E + 515) := by
      rw [show κ + 258 * E + 515 = (κ + 258 * E + 513) + 2 by ring,
        Real.exp_add (κ + 258 * E + 513) 2]
      linarith [mul_le_mul_of_nonneg_left he2 (Real.exp_pos (κ + 258 * E + 513)).le,
        Real.exp_pos (κ + 258 * E + 513)]
    have e2 : 2 * ((dB : ℝ) * (2 * (bumpConst * (8 * (((dB + 1 : ℕ) : ℝ) + 1)) ^ 32 *
        (2 / δ)))) = 4 * ((dB : ℝ) * (bumpConst * (8 * (((dB + 1 : ℕ) : ℝ) + 1)) ^ 32 *
        (2 / δ))) := by ring
    rw [e2]; linarith only [hprod, h4]
  have hb0 : 0 ≤ 2 * ((dB : ℝ) * (2 * (bumpConst * (8 * (((dB + 1 : ℕ) : ℝ) + 1)) ^ 32 *
      (2 / δ)))) := by positivity
  have hpow : (2 * ((dB : ℝ) * (2 * (bumpConst * (8 * (((dB + 1 : ℕ) : ℝ) + 1)) ^ 32 *
      (2 / δ))))) ^ (dB + 1) ≤ Real.exp ((E + 1) * (κ + 258 * E + 515)) := by
    calc _ ≤ Real.exp (κ + 258 * E + 515) ^ (dB + 1) := pow_le_pow_left₀ hb0 hbase _
      _ = Real.exp ((dB + 1 : ℕ) * (κ + 258 * E + 515)) := by rw [← Real.exp_nat_mul]
      _ ≤ Real.exp ((E + 1) * (κ + 258 * E + 515)) := by
          refine Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right ?_ (by positivity))
          push_cast; linarith
  have h7 : (7 : ℝ) ^ dB ≤ Real.exp (2 * E) := by
    calc (7 : ℝ) ^ dB ≤ Real.exp 2 ^ dB := pow_le_pow_left₀ (by norm_num) he2 _
      _ = Real.exp (dB * 2) := by rw [← Real.exp_nat_mul]
      _ ≤ Real.exp (2 * E) := Real.exp_le_exp.mpr (by linarith)
  have h5 : (5 : ℝ) ^ dB ≤ Real.exp (2 * E) := by
    calc (5 : ℝ) ^ dB ≤ Real.exp 2 ^ dB := pow_le_pow_left₀ (by norm_num) (by linarith) _
      _ = Real.exp (dB * 2) := by rw [← Real.exp_nat_mul]
      _ ≤ Real.exp (2 * E) := Real.exp_le_exp.mpr (by linarith)
  have hs : Real.sqrt dB ^ (dB + 1) ≤ Real.exp (E * (E + 1)) := by
    have h1 : Real.sqrt dB ≤ Real.exp E := by
      have : Real.sqrt dB ≤ dB + 1 := by
        rw [Real.sqrt_le_left (by positivity)]; nlinarith only
      exact this.trans ((Real.add_one_le_exp _).trans (Real.exp_le_exp.mpr hdB))
    calc Real.sqrt dB ^ (dB + 1) ≤ Real.exp E ^ (dB + 1) :=
          pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 _
      _ = Real.exp ((dB + 1 : ℕ) * E) := by rw [← Real.exp_nat_mul]
      _ ≤ Real.exp (E * (E + 1)) := by
          refine Real.exp_le_exp.mpr ?_
          push_cast; nlinarith only [hdB]
  set TS := 2 * E + (E + 1) * (κ + 258 * E + 515) + E * (E + 1)
  have hTS : 2 * E ≤ TS := by
    have : 0 ≤ (E + 1) * (κ + 258 * E + 515) := by positivity
    have : 0 ≤ E * (E + 1) := by positivity
    linarith
  have htail : gaugeTail dB δ ≤ Real.exp TS := by
    unfold gaugeTail
    calc (7 : ℝ) ^ dB * (2 * ((dB : ℝ) * (2 * (bumpConst * (8 * (((dB + 1 : ℕ) : ℝ) + 1)) ^ 32 *
          (2 / δ))))) ^ (dB + 1) * Real.sqrt dB ^ (dB + 1) ≤
        Real.exp (2 * E) * Real.exp ((E + 1) * (κ + 258 * E + 515)) * Real.exp (E * (E + 1)) := by
          gcongr
      _ = Real.exp TS := by simp only [TS, ← Real.exp_add]
  unfold gaugeSqNorm
  calc (5 : ℝ) ^ dB + 2 * gaugeTail dB δ ≤ Real.exp TS + 2 * Real.exp TS := by
        have := h5.trans (Real.exp_le_exp.mpr hTS)
        linarith
    _ ≤ Real.exp (TS + 2) := by
        rw [Real.exp_add TS 2]
        linarith [mul_le_mul_of_nonneg_left he2 (Real.exp_pos TS).le, Real.exp_pos TS]

namespace ActiveSetup.BasicFamilies.FamParams
variable {κ : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ c₀} {bf : A.BasicFamilies}
  (fp : bf.FamParams)

/-! ### The enlarged budget `D_*` and the common cutoff `B_*` (blueprint line 1944) -/

/-- The height bound of the key differences of the modes of every group (the bound `B_σ` of
`exists_mainModeSystem`), `max(1, B (1 + 4 (2 d_B + 1) max(1, 4B/δ_c)))` at the largest curvature
bound `B = exp(D X_max^D)`. -/
noncomputable def keyHgt (D dB : ℕ) (H δc : ℝ) : ℝ :=
  max 1 (Real.exp (D * fp.Xmax dB H ^ D) * (1 + 4 * (2 * dB + 1) *
    max 1 (4 * Real.exp (D * fp.Xmax dB H ^ D) / δc)))

/-- The heights of the rescaled differences of mode differences (blueprint line 1934: `D_*` covers
the rational heights of `eq:mode-differences` and `Q₀`): `2 (Q₀ (3 B_σ²)²)² + 1` with
`Q₀ ≤ H_ed^(d_B²) + 1`. -/
noncomputable def hgtStar (D dB : ℕ) (H δc : ℝ) : ℝ :=
  2 * ((fp.Hed ^ (dB * dB) + 1) * (3 * (fp.keyHgt D dB H δc * fp.keyHgt D dB H δc) ^ 2)) ^ 2 + 1

theorem one_le_keyHgt (D dB : ℕ) (H δc : ℝ) : 1 ≤ fp.keyHgt D dB H δc := le_max_left _ _

theorem one_le_hgtStar (D dB : ℕ) (H δc : ℝ) : 1 ≤ fp.hgtStar D dB H δc := by
  unfold hgtStar; have := sq_nonneg ((fp.Hed ^ (dB * dB) + 1) *
    (3 * (fp.keyHgt D dB H δc * fp.keyHgt D dB H δc) ^ 2)); linarith

/-- The key heights and the clearing bound are at most `modeStar + 1`. -/
theorem keyHgt_le_modeStar (D dB : ℕ) {H δc N : ℝ} (k : ℝ) (hHed : 2 ≤ fp.Hed) (_hH : 1 ≤ H)
    (_hδc : 0 < δc) (hN0 : 0 ≤ N) :
    fp.keyHgt D dB H δc ≤ fp.modeStar D dB H δc N k + 1 ∧
      fp.Hed ^ (dB * dB) + 1 ≤ fp.modeStar D dB H δc N k + 1 := by
  set Bm := Real.exp (D * fp.Xmax dB H ^ D)
  have hBm : 0 < Bm := Real.exp_pos _
  have hmax : 0 ≤ max 1 (4 * Bm / δc) := le_trans zero_le_one (le_max_left _ _)
  have hcb : (2 : ℝ) ≤ A.colBudget := by
    have := A.Dc_nonneg; unfold ActiveSetup.colBudget
    have : (0 : ℝ) ≤ Fintype.card A.L * (1 + A.Dc) := by positivity
    linarith
  have h1 : (0 : ℝ) ≤ A.famVtxBound * (fp.K.potMax A.famVtxBound + 1) * (N + 1) *
      (Bm * (4 * max 1 (4 * Bm / δc) + 1) ^ (4 * dB)) := by positivity
  have h2 : (0 : ℝ) ≤ A.colBudget ^ 2 * (Bm ^ 2 + 1) := by positivity
  have h3 : (0 : ℝ) ≤ (Real.sqrt N + 1) * A.colBudget * Bm := by positivity
  have h4 : (0 : ℝ) ≤ Bm * (1 + 4 * (2 * dB + 1) * max 1 (4 * Bm / δc)) := by positivity
  have h5 : (0 : ℝ) ≤ fp.Hed ^ (dB * dB) := pow_nonneg (by linarith) _
  have h6 := Real.exp_pos k
  unfold keyHgt modeStar
  refine ⟨max_le (by linarith) (by linarith), by linarith⟩

/-- Blueprint line 1944 ("enlarge `D_*` to cover these full Fourier norms, including `(ζ^ρ)²`"):
the budget `modeStar` of line 1934 plus the full Fourier norm bounds of the gauge multipliers
(enlarged cutoff `δ/2`, centers of dimension at most `d_B`, `Q₀ ≤ H_ed^(d_B²)`, entries at most
`H_ed`) and of the squared gauge `(ζ^ρ)²` (cutoff `δ`). -/
noncomputable def modeStarG (D dB : ℕ) (H δc N k δ : ℝ) : ℝ :=
  fp.modeStar D dB H δc N k + gaugeMultNorm dB (fp.Hed ^ (dB * dB)) fp.Hed (δ / 2) +
    gaugeSqNorm dB δ + fp.hgtStar D dB H δc

theorem gaugeMultNorm_nonneg (d : ℕ) {Q0 Cm δ : ℝ} (hδ : 0 < δ) (hQ0 : 0 ≤ Q0) (hCm : 0 ≤ Cm) :
    0 ≤ gaugeMultNorm d Q0 Cm δ := by
  unfold gaugeMultNorm gaugeMultTail
  have := gaugeMultA_nonneg hδ d hQ0 hCm
  positivity

theorem gaugeMultTail_nonneg (d : ℕ) {Q0 Cm δ : ℝ} (hδ : 0 < δ) (hQ0 : 0 ≤ Q0) (hCm : 0 ≤ Cm) :
    0 ≤ gaugeMultTail d Q0 Cm δ := by
  unfold gaugeMultTail
  have := gaugeMultA_nonneg hδ d hQ0 hCm
  positivity

theorem gaugeSqNorm_nonneg (d : ℕ) {δ : ℝ} (hδ : 0 < δ) : 0 ≤ gaugeSqNorm d δ := by
  unfold gaugeSqNorm; have := gaugeTail_nonneg d hδ; positivity

/-- The enlarged budget dominates `e^k`, the budget of line 1934 and the two full Fourier norm
bounds. -/
theorem le_modeStarG (D dB : ℕ) {H δc N : ℝ} (k : ℝ) {δ : ℝ} (hδ : 0 < δ) (hHed : 2 ≤ fp.Hed)
    (hH : 1 ≤ H) (hδc : 0 < δc) (hN0 : 0 ≤ N) :
    Real.exp k ≤ fp.modeStarG D dB H δc N k δ ∧
      fp.modeStar D dB H δc N k ≤ fp.modeStarG D dB H δc N k δ ∧
      gaugeMultNorm dB (fp.Hed ^ (dB * dB)) fp.Hed (δ / 2) ≤ fp.modeStarG D dB H δc N k δ ∧
      gaugeSqNorm dB δ ≤ fp.modeStarG D dB H δc N k δ ∧
      fp.hgtStar D dB H δc ≤ fp.modeStarG D dB H δc N k δ := by
  obtain ⟨hk, -⟩ := fp.le_modeStar D dB k hHed hH hδc hN0 (le_refl (0 : ℤ)) (Nat.zero_le 4)
  have h1 := gaugeMultNorm_nonneg dB (Q0 := fp.Hed ^ (dB * dB)) (Cm := fp.Hed) (half_pos hδ)
    (pow_nonneg (by linarith) _) (by linarith)
  have h2 := gaugeSqNorm_nonneg dB hδ
  have h0 := Real.exp_pos k
  have h3 := fp.one_le_hgtStar D dB H δc
  have h4 : 0 ≤ fp.modeStar D dB H δc N k := h0.le.trans hk
  unfold modeStarG
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩

/-- The uniform truncation constant of the multipliers and of `(ζ^ρ)²`. -/
noncomputable def tailStar (dB : ℕ) (δ : ℝ) : ℝ :=
  gaugeMultTail dB (fp.Hed ^ (dB * dB)) fp.Hed (δ / 2) + gaugeTail dB δ

/-- The cutoff exponent `K_*` (blueprint line 1944): the least `K` with
`2^K ≥ 2 (T_* + 1) D_*^300`, `T_*` the uniform truncation constant. -/
noncomputable def Kstar (D dB : ℕ) (H δc N k δ : ℝ) : ℕ :=
  ⌈Real.logb 2 (2 * (fp.tailStar dB δ + 1) * fp.modeStarG D dB H δc N k δ ^ 300)⌉₊

/-- Truncation tails below `D_*^(-300)`: every truncation constant `T ≤ T_*` gives
`2 T / 2^(K_*) ≤ D_*^(-300)`. -/
theorem tail_le_Kstar (D dB : ℕ) {H δc N : ℝ} (k : ℝ) {δ : ℝ} (hδ : 0 < δ) (hHed : 2 ≤ fp.Hed)
    (hH : 1 ≤ H) (hδc : 0 < δc) (hN0 : 0 ≤ N) {T : ℝ} (hT0 : 0 ≤ T)
    (hT : T ≤ fp.tailStar dB δ) :
    2 * T / 2 ^ fp.Kstar D dB H δc N k δ ≤ (fp.modeStarG D dB H δc N k δ ^ 300)⁻¹ := by
  obtain ⟨hk, -, -, -, -⟩ := fp.le_modeStarG D dB k hδ hHed hH hδc hN0
  set Ds := fp.modeStarG D dB H δc N k δ
  have hDs : 0 < Ds := (Real.exp_pos k).trans_le hk
  set x := 2 * (fp.tailStar dB δ + 1) * Ds ^ 300
  have hx : 0 < x := by
    have : 0 ≤ fp.tailStar dB δ := hT0.trans hT
    positivity
  have h2K : x ≤ 2 ^ fp.Kstar D dB H δc N k δ := by
    have h1 : x = (2 : ℝ) ^ Real.logb 2 x := (Real.rpow_logb (by norm_num) (by norm_num) hx).symm
    rw [h1, ← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (Nat.le_ceil _)
  have hpos : (0 : ℝ) < 2 ^ fp.Kstar D dB H δc N k δ := by positivity
  rw [div_le_iff₀ hpos]
  calc 2 * T ≤ 2 * (fp.tailStar dB δ + 1) := by linarith
    _ = x * (Ds ^ 300)⁻¹ := by
        simp only [x]; field_simp
    _ ≤ (Ds ^ 300)⁻¹ * 2 ^ fp.Kstar D dB H δc N k δ := by
        rw [mul_comm]; exact mul_le_mul_of_nonneg_left h2K (by positivity)

/-- `log B_* ≤ 301 log D_* + 3` for `B_* = 2^(K_* + 1)`. -/
theorem log_Bstar_le (D dB : ℕ) {H δc N : ℝ} {k : ℝ} (hk0 : 0 ≤ k) {δ : ℝ} (hδ : 0 < δ)
    (hHed : 2 ≤ fp.Hed) (hH : 1 ≤ H) (hδc : 0 < δc) (hN0 : 0 ≤ N) :
    Real.log ((2 : ℝ) ^ (fp.Kstar D dB H δc N k δ + 1)) ≤
      301 * Real.log (fp.modeStarG D dB H δc N k δ) + 3 := by
  obtain ⟨hk, -, hGM, hGS, -⟩ := fp.le_modeStarG D dB k hδ hHed hH hδc hN0
  set Ds := fp.modeStarG D dB H δc N k δ
  have hDs1 : 1 ≤ Ds := (Real.one_le_exp hk0).trans hk
  have hT0 : 0 ≤ fp.tailStar dB δ := by
    unfold tailStar gaugeMultTail
    have := gaugeMultA_nonneg (half_pos hδ) dB (Q0 := fp.Hed ^ (dB * dB)) (Cm := fp.Hed)
      (pow_nonneg (by linarith) _) (by linarith)
    have := gaugeTail_nonneg dB hδ
    positivity
  have hTD : fp.tailStar dB δ + 1 ≤ 2 * Ds := by
    unfold tailStar
    have h1 : gaugeMultTail dB (fp.Hed ^ (dB * dB)) fp.Hed (δ / 2) ≤
        gaugeMultNorm dB (fp.Hed ^ (dB * dB)) fp.Hed (δ / 2) := by
      unfold gaugeMultNorm
      have := gaugeMultTail_nonneg dB (Q0 := fp.Hed ^ (dB * dB)) (Cm := fp.Hed) (half_pos hδ)
        (pow_nonneg (by linarith) _) (by linarith)
      have : (0 : ℝ) ≤ 5 ^ (dB + dB) := by positivity
      linarith
    have h2 : gaugeTail dB δ ≤ gaugeSqNorm dB δ := by
      unfold gaugeSqNorm
      have := gaugeTail_nonneg dB hδ
      have : (0 : ℝ) ≤ 5 ^ dB := by positivity
      linarith
    have hms : 0 ≤ fp.modeStar D dB H δc N k := (Real.exp_pos k).le.trans
      (fp.le_modeStar D dB k hHed hH hδc hN0 (le_refl (0 : ℤ)) (Nat.zero_le 4)).1
    have : Ds = fp.modeStar D dB H δc N k + gaugeMultNorm dB (fp.Hed ^ (dB * dB)) fp.Hed (δ / 2) +
        gaugeSqNorm dB δ + fp.hgtStar D dB H δc := rfl
    have := fp.one_le_hgtStar D dB H δc
    linarith
  set! x := 2 * (fp.tailStar dB δ + 1) * Ds ^ 300
  have hx1 : 1 ≤ x := by
    have : 1 ≤ Ds ^ 300 := one_le_pow₀ hDs1
    nlinarith
  have hlx : 0 ≤ Real.logb 2 x := Real.logb_nonneg (by norm_num) hx1
  have hK : (fp.Kstar D dB H δc N k δ : ℝ) < Real.logb 2 x + 1 := Nat.ceil_lt_add_one hlx
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2' : Real.log 2 ≤ 3 / 4 := by
    have := Real.log_two_lt_d9; linarith
  rw [Real.log_pow]
  push_cast
  have hlogb : Real.logb 2 x * Real.log 2 = Real.log x := by
    rw [Real.logb, div_mul_cancel₀ _ hl2.ne']
  have hlx' : Real.log x ≤ Real.log 2 + Real.log (2 * Ds) + 300 * Real.log Ds := by
    rw [show x = 2 * ((fp.tailStar dB δ + 1) * Ds ^ 300) by simp only [x]; ring,
      Real.log_mul (by norm_num) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_pow]
    have := Real.log_le_log (by positivity) hTD
    push_cast; linarith
  have hl2D : Real.log (2 * Ds) = Real.log 2 + Real.log Ds :=
    Real.log_mul (by norm_num) (by positivity)
  calc ((fp.Kstar D dB H δc N k δ : ℝ) + 1) * Real.log 2 ≤ (Real.logb 2 x + 2) * Real.log 2 :=
        mul_le_mul_of_nonneg_right (by linarith) hl2.le
    _ = Real.log x + 2 * Real.log 2 := by rw [add_mul, hlogb]
    _ ≤ 301 * Real.log Ds + 3 := by
        have := Real.log_nonneg hDs1
        linarith

end ActiveSetup.BasicFamilies.FamParams

/-- The polynomial size of the Fourier exponents `T_G + T_S ≤ (5κ + 4682) E⁴` for `E ≥ 1`. -/
theorem fourier_exponents_le {E κb : ℝ} (hE1 : 1 ≤ E) (hκ : 0 ≤ κb) :
    (12 * E + (2 * E + 1) * (E ^ 3 + κb + 514 * E + 523) + 2 * E * (2 * E + 1)) +
      (2 * E + (E + 1) * (κb + 258 * E + 515) + E * (E + 1)) ≤ (5 * κb + 4682) * E ^ 4 := by
  have e : (12 * E + (2 * E + 1) * (E ^ 3 + κb + 514 * E + 523) + 2 * E * (2 * E + 1)) +
      (2 * E + (E + 1) * (κb + 258 * E + 515) + E * (E + 1)) =
      2 * E ^ 4 + E ^ 3 + 1291 * E ^ 2 + 2350 * E + 3 * (κb * E) + 2 * κb + 1038 := by ring
  rw [e]
  have h1 : E ≤ E ^ 4 := by
    calc E = E ^ 1 := (pow_one E).symm
      _ ≤ E ^ 4 := pow_le_pow_right₀ hE1 (by norm_num)
  have h2 : E ^ 2 ≤ E ^ 4 := pow_le_pow_right₀ hE1 (by norm_num)
  have h3 : E ^ 3 ≤ E ^ 4 := pow_le_pow_right₀ hE1 (by norm_num)
  have h0 : 1 ≤ E ^ 4 := one_le_pow₀ hE1
  have h4 : κb * E ≤ κb * E ^ 4 := mul_le_mul_of_nonneg_left h1 hκ
  have h5 : κb ≤ κb * E ^ 4 := le_mul_of_one_le_right hκ h0
  linarith


open ActiveSetup.BasicFamilies.FamParams in
/-- Blueprint line 1944: the enlarged budget and the common cutoff satisfy `log D_* ≤ P^C` and
`log B_* ≤ P^C`. For fixed degrees `c` (of the standing bounds) and `D` (of the first-match
expansion) there is a degree `C` such that, under the standing bounds of `log_modeStar_poly` and
`0 < δ`, `δ⁻¹ ≤ exp(k^c)`, `0 < δ_c`, both `log D_*` and `log B_*`, `B_* = 2^(K_*+1)`, are at most
`C (k P)^C`. -/
theorem log_modeStarG_poly (c D : ℕ) :
    ∃ C : ℕ, ∀ {κ : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ c₀} {bf : A.BasicFamilies}
      (fp : bf.FamParams) (dB : ℕ) {H δc N k δ : ℝ}, 1 ≤ k → (fp.Lc : ℝ) + 6 ≤ k ^ c →
      (fp.Hmax : ℝ) + 1 ≤ (k * fp.P) ^ c → (dB : ℝ) ≤ k ^ c → 2 ≤ fp.Hed →
      Real.log fp.Hed ≤ k ^ c → 1 ≤ H → Real.log H ≤ k ^ c → 0 < δc →
      δc⁻¹ ≤ Real.exp (k ^ c) → 0 ≤ N → N ≤ Real.exp (k ^ c) →
      A.colBudget ≤ Real.exp (k ^ c) → 0 < δ → δ⁻¹ ≤ Real.exp (k ^ c) →
      Real.log (fp.modeStarG D dB H δc N k δ) ≤ C * (k * fp.P) ^ C ∧
        Real.log ((2 : ℝ) ^ (fp.Kstar D dB H δc N k δ + 1)) ≤ C * (k * fp.P) ^ C := by
  obtain ⟨C0, hC0⟩ := log_modeStar_poly c D
  set K1 : ℕ := ⌈5 * Real.log bumpConst + 4682⌉₊ with hK1
  set C1 : ℕ := 10 * C0 + K1 + 4 * c + 15 with hC1
  refine ⟨301 * C1 + 3, ?_⟩
  intro κ c₀ A bf fp dB H δc N k δ hk hL hHm hdB hHed hHedk hH hHk hδc0 hδck hN0 hNk hcB hδ hδk
  set E := k ^ c with hE
  set u := k * (fp.P : ℝ) with hu
  have hP1 : (1 : ℝ) ≤ fp.P := by exact_mod_cast fp.hP
  have hE1 : 1 ≤ E := one_le_pow₀ hk
  have hku : k ≤ u := le_mul_of_one_le_right (by linarith) hP1
  have hu1 : 1 ≤ u := hk.trans hku
  have hEu : E ≤ u ^ c := pow_le_pow_left₀ (by linarith) hku c
  have hκ : 0 ≤ Real.log bumpConst := Real.log_nonneg one_le_bumpConst
  set κb := Real.log bumpConst
  -- the three parts
  have hM := hC0 fp dB (H := H) (δc := δc) (N := N) hk hL hHm hdB hHed hHedk hH hHk hδck hN0
    hNk hcB
  have hGM := gaugeMultNorm_le_exp hE1 hdB hHed hHedk hδ hδk
  have hGS := gaugeSqNorm_le_exp hE1 hdB hδ hδk
  set TG := 12 * E + (2 * E + 1) * (E ^ 3 + κb + 514 * E + 523) + 2 * E * (2 * E + 1)
  set TS := 2 * E + (E + 1) * (κb + 258 * E + 515) + E * (E + 1)
  set TM := (C0 : ℝ) * u ^ C0
  have hTM0 : 0 ≤ TM := by positivity
  have hTG0 : 0 ≤ TG := by positivity
  have hTS0 : 0 ≤ TS := by positivity
  have hMpos : 0 < fp.modeStar D dB H δc N k :=
    (Real.exp_pos k).trans_le (fp.le_modeStar D dB k hHed hH hδc0 hN0 (le_refl (0 : ℤ))
      (Nat.zero_le 4)).1
  have hMle : fp.modeStar D dB H δc N k ≤ Real.exp TM := by
    rw [← Real.exp_log hMpos]; exact Real.exp_le_exp.mpr hM
  -- the height term: at most `19 (modeStar + 1)^10 ≤ exp(10 T_M + 13)`
  have hhgt : fp.hgtStar D dB H δc ≤ Real.exp (10 * TM + 13) := by
    obtain ⟨hkh, hQh⟩ := fp.keyHgt_le_modeStar D dB k hHed hH hδc0 hN0
    set M1 := fp.modeStar D dB H δc N k + 1
    have hM1 : 1 ≤ M1 := by linarith
    have hM1e : M1 ≤ Real.exp (TM + 1) := by
      rw [Real.exp_add]
      have he1 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      have := Real.one_le_exp hTM0
      nlinarith only [hMle, he1, this]
    have hk1 := fp.one_le_keyHgt D dB H δc
    have hH0 : 0 ≤ fp.Hed ^ (dB * dB) + 1 := by positivity
    have hbase : (fp.Hed ^ (dB * dB) + 1) * (3 * (fp.keyHgt D dB H δc *
        fp.keyHgt D dB H δc) ^ 2) ≤ M1 * (3 * (M1 * M1) ^ 2) := by
      gcongr
    have hstep : fp.hgtStar D dB H δc ≤ 19 * M1 ^ 10 := by
      unfold hgtStar
      have h0 : 0 ≤ (fp.Hed ^ (dB * dB) + 1) * (3 * (fp.keyHgt D dB H δc *
          fp.keyHgt D dB H δc) ^ 2) := by positivity
      have hsq := pow_le_pow_left₀ h0 hbase 2
      have hM10 : (1 : ℝ) ≤ M1 ^ 10 := one_le_pow₀ hM1
      have e : (M1 * (3 * (M1 * M1) ^ 2)) ^ 2 = 9 * M1 ^ 10 := by ring
      rw [e] at hsq
      linarith
    have he : M1 ^ 10 ≤ Real.exp (10 * TM + 10) := by
      calc M1 ^ 10 ≤ Real.exp (TM + 1) ^ 10 := pow_le_pow_left₀ (by linarith) hM1e 10
        _ = Real.exp (10 * TM + 10) := by rw [← Real.exp_nat_mul]; push_cast; ring_nf
    have h19 : (19 : ℝ) ≤ Real.exp 3 := by
      have h7 := exp_bounds_small.2.1
      have e3 : Real.exp 3 = Real.exp 2 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      have he1 : (2.718 : ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
      have hm : (7 : ℝ) * 2.718 ≤ Real.exp 2 * Real.exp 1 :=
        mul_le_mul h7 he1 (by norm_num) (Real.exp_pos 2).le
      rw [e3]; linarith
    calc fp.hgtStar D dB H δc ≤ 19 * M1 ^ 10 := hstep
      _ ≤ Real.exp 3 * Real.exp (10 * TM + 10) := by
          have := (Real.exp_pos (10 * TM + 10)).le
          have : (0 : ℝ) ≤ M1 ^ 10 := by positivity
          nlinarith
      _ = Real.exp (10 * TM + 13) := by rw [← Real.exp_add]; ring_nf
  set! T := 10 * TM + TG + TS + 13
  have hsum : fp.modeStarG D dB H δc N k δ ≤ Real.exp (T + 2) := by
    have h1 : Real.exp TM ≤ Real.exp T := Real.exp_le_exp.mpr (by linarith)
    have h2 : Real.exp (TG + 2) ≤ Real.exp T := Real.exp_le_exp.mpr (by linarith)
    have h3 : Real.exp (TS + 2) ≤ Real.exp T := Real.exp_le_exp.mpr (by linarith)
    have h4 : Real.exp (10 * TM + 13) ≤ Real.exp T := Real.exp_le_exp.mpr (by linarith)
    have he2 : (7 : ℝ) ≤ Real.exp 2 := exp_bounds_small.2.1
    have : fp.modeStarG D dB H δc N k δ = fp.modeStar D dB H δc N k +
        gaugeMultNorm dB (fp.Hed ^ (dB * dB)) fp.Hed (δ / 2) + gaugeSqNorm dB δ +
          fp.hgtStar D dB H δc := rfl
    rw [this, Real.exp_add T 2]
    linarith [mul_le_mul_of_nonneg_left he2 (Real.exp_pos T).le, Real.exp_pos T]
  obtain ⟨hk', -, -, -, -⟩ := fp.le_modeStarG D dB k hδ hHed hH hδc0 hN0
  have hDpos : 0 < fp.modeStarG D dB H δc N k δ := (Real.exp_pos k).trans_le hk'
  have hlogD : Real.log (fp.modeStarG D dB H δc N k δ) ≤ T + 2 := by
    rw [Real.log_le_iff_le_exp hDpos]; exact hsum
  -- polynomial bounds for `T_G` and `T_S`
  have hE4 : E ^ 4 ≤ u ^ (4 * c) := by
    calc E ^ 4 ≤ (u ^ c) ^ 4 := pow_le_pow_left₀ (by linarith) hEu 4
      _ = u ^ (4 * c) := by ring
  have hTGS : TG + TS ≤ (5 * κb + 4682) * E ^ 4 := fourier_exponents_le hE1 hκ
  have hK1 : 5 * κb + 4682 ≤ (K1 : ℝ) := Nat.le_ceil _
  have hupw : ∀ a : ℕ, a ≤ C1 → u ^ a ≤ u ^ C1 := fun a h => pow_le_pow_right₀ hu1 h
  have hlogD' : Real.log (fp.modeStarG D dB H δc N k δ) ≤ C1 * u ^ C1 := by
    have a1 : TM ≤ C0 * u ^ C1 := mul_le_mul_of_nonneg_left (hupw C0 (by omega))
      (Nat.cast_nonneg _)
    have a2 : TG + TS ≤ K1 * u ^ C1 := by
      calc TG + TS ≤ (5 * κb + 4682) * E ^ 4 := hTGS
        _ ≤ K1 * u ^ C1 := mul_le_mul hK1 (hE4.trans (hupw _ (by omega)))
            (by positivity) (Nat.cast_nonneg _)
    have a3 : (4 : ℝ) ≤ 4 * u ^ C1 := by
      have := one_le_pow₀ (n := C1) hu1; linarith
    have hC1r : (C1 : ℝ) = 10 * C0 + K1 + 4 * c + 15 := by simp only [C1]; push_cast; ring
    have a4 : (0 : ℝ) ≤ 4 * c * u ^ C1 := by positivity
    have a5 : (15 : ℝ) ≤ 15 * u ^ C1 := by
      have := one_le_pow₀ (n := C1) hu1; linarith
    calc Real.log (fp.modeStarG D dB H δc N k δ) ≤ 10 * TM + TG + TS + 15 := by linarith
      _ ≤ C1 * u ^ C1 := by rw [hC1r]; linarith
  have hB := fp.log_Bstar_le D dB (by linarith) hδ hHed hH hδc0 hN0 (k := k)
  have hupw' : u ^ C1 ≤ u ^ (301 * C1 + 3) := pow_le_pow_right₀ hu1 (by omega)
  have hu0 : 0 ≤ u ^ C1 := by positivity
  push_cast
  constructor
  · calc Real.log (fp.modeStarG D dB H δc N k δ) ≤ C1 * u ^ C1 := hlogD'
      _ ≤ (301 * C1 + 3) * u ^ (301 * C1 + 3) := by
          have : (C1 : ℝ) ≤ 301 * C1 + 3 := by linarith [(Nat.cast_nonneg C1 : (0 : ℝ) ≤ C1)]
          exact mul_le_mul this hupw' hu0 (by positivity)
  · calc Real.log ((2 : ℝ) ^ (fp.Kstar D dB H δc N k δ + 1)) ≤
          301 * Real.log (fp.modeStarG D dB H δc N k δ) + 3 := hB
      _ ≤ 301 * (C1 * u ^ C1) + 3 := by linarith
      _ ≤ (301 * C1 + 3) * u ^ (301 * C1 + 3) := by
          have h1 : (1 : ℝ) ≤ u ^ (301 * C1 + 3) := one_le_pow₀ hu1
          have h2 : (C1 : ℝ) * u ^ C1 ≤ C1 * u ^ (301 * C1 + 3) :=
            mul_le_mul_of_nonneg_left hupw' (Nat.cast_nonneg _)
          linarith

/-! ## Freezing and retention (blueprint line 1967) -/

/-- A finite combination of private columns at one point, as a main augmented value. -/
theorem sum_privateColumnValue_eq {W : Type*} [Fintype W] [DecidableEq W] (φ : W → ℝ → ℂ)
    (ε : W → ℝ) (S : Finset W) (c : W → ℂ) (y : ℝ) :
    ∑ Φ ∈ S, c Φ • privateColumnValue φ ε Φ y =
      augmentedMain (fun Φ => φ Φ y) ε (fun Φ => if Φ ∈ S then c Φ else 0) := by
  ext o
  rcases o with _ | Φ
  · simp only [augmentedMain, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply,
      privateColumnValue, PiLp.add_apply, smul_eq_mul]
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ S)]
    simp only [Finset.filter_mem_eq_inter, Finset.univ_inter]
    rw [Finset.sum_eq_zero (s := Finset.univ.filter fun n => n ∉ S)
      (fun n hn => by simp [(Finset.mem_filter.mp hn).2]), add_zero]
    refine Finset.sum_congr rfl fun n hn => ?_
    simp [hn, mul_comm]
  · simp only [augmentedMain, WithLp.ofLp_sum, Finset.sum_apply, PiLp.smul_apply,
      privateColumnValue, PiLp.add_apply, smul_eq_mul]
    by_cases hΦ : Φ ∈ S
    · rw [Finset.sum_eq_single Φ]
      · simp [hΦ, mul_comm]
      · intro n _ hn; simp [Ne.symm hn]
      · intro h; exact absurd hΦ h
    · rw [Finset.sum_eq_zero]
      · simp [hΦ]
      · intro n hn
        have : Φ ≠ n := fun h => hΦ (h ▸ hn)
        simp [this]

namespace ActiveSetup.BasicFamilies.FamParams
variable {κ : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ c₀} {bf : A.BasicFamilies}
  (fp : bf.FamParams)

open Classical in
/-- The labels of the inherited ball masks of a role at a cell whose deepest active ancestor is
`a` are primaries of the role at `a` (blueprint lines 1859, 1888 and 1967: between actual uses the
inherited projections are retained). -/
theorem ballMaskT_labels_primaries (l : Fin 4) (s : List (CatCol bf.Vtx))
    (mb : bf.MainBudget s) (G : bf.Grp) (j : ℕ) (p : Fin fp.P) (d : bf.Vtx) {U a : ℤ × ℤ}
    (hUa : deepAnc (A := A) U = some a) {v : bf.RLab fp.Mc s}
    (hv : v ∈ (fp.ballMaskT l s mb G j p).labels U) : v.1 ∈ fp.primaries l s G j d a := by
  have haC := (deepAnc_spec hUa).1
  have h1 : v ∈ (fp.ballMaskT l s mb G j p).labels a := by
    unfold ballMaskT at hv ⊢
    rwa [bf.mainMaskT_labels_retain l fp.Mc s mb _ _ _ hUa] at hv
  have h2 : bf.mainPred l s a (fp.brank j) (fp.bmask a G j (p + 1)) v.1 := by
    unfold ballMaskT at h1
    exact (bf.mainMaskT_labels_self l fp.Mc s mb _ _ _ haC v).mp h1
  refine fp.ballLabels_subset_primaries l s G j d a (p := p + 1) (by have := p.2; omega) ?_
  obtain ⟨x | n, hrel⟩ := v
  · obtain ⟨hav, hM⟩ := h2
    exact mem_mainLabelsM.mpr ⟨mem_mainLabels.mpr hav, hM⟩
  · obtain ⟨hn, hb, hr, hM⟩ := h2
    refine mem_mainLabelsM.mpr ⟨mem_mainLabels.mpr ⟨hn, hb, hr⟩, ?_⟩
    simp only [labelTag, Sum.elim_inr, hn, ↓reduceDIte]
    exact hM

open Classical in
/-- Blueprint lines 1859 and 1967: on a cell `U` of a depth partition of the main tree, the
relabeled global ball output of a role vanishes if `U` has no active ancestor (zero before the
attempt); otherwise it is a combination, with constant coefficients on `U`, of the main columns
on `U` of the primaries of the role at the deepest active ancestor `a` of `U` (the retained
inherited projections). -/
theorem gBall_cell_rep (l : Fin 4) (s : List (CatCol bf.Vtx)) (mb : bf.MainBudget s)
    (G : bf.Grp) (j : ℕ) (d : bf.Vtx) {u : ℤ} {U : ℤ × ℤ}
    (hU : U ∈ ((bf.mainBase fp.Mc s mb).partition u).cells) (z : ColumnL2 (bf.RLab fp.Mc s)) :
    (deepAnc (A := A) U = none ∧
      columnL2Restriction (dyadicGridCell A.G U.1 U.2) (dyadicGridCell_measurable A.G U.1 U.2)
        (colRelabel (bf.rv fp.Mc s) (fp.gBall l s mb G j u z)) = 0) ∨
    ∃ a, deepAnc (A := A) U = some a ∧ ∃ c : bf.Lab ⊕ Fin fp.Mc → ℂ,
      columnL2Restriction (dyadicGridCell A.G U.1 U.2) (dyadicGridCell_measurable A.G U.1 U.2)
          (colRelabel (bf.rv fp.Mc s) (fp.gBall l s mb G j u z)) =
        ∑ Φ ∈ fp.primaries l s G j d a, c Φ • mainCol A.G fp.Mc (bf.origCols l) s U Φ := by
  set! cU := dyadicGridCell A.G U.1 U.2
  have hmU : MeasurableSet cU := dyadicGridCell_measurable A.G U.1 U.2
  rcases ha : deepAnc (A := A) U with _ | a
  · refine Or.inl ⟨rfl, ?_⟩
    rw [← colRelabel_restrict, fp.gBall_zero_before l s mb G j u hU ha z, map_zero]
  · refine Or.inr ⟨a, rfl, ?_⟩
    obtain ⟨haC, hUa, -⟩ := deepAnc_spec ha
    set S := fp.primaries l s G j d a
    set! M := Submodule.span ℂ (Set.range fun Φ : {Φ // Φ ∈ S} =>
      mainCol A.G fp.Mc (bf.origCols l) s U Φ.1)
    have hmemS : ∀ Φ ∈ S, MemLp (cU.indicator (privateColumnValue
        (mainScalar fp.Mc (bf.origCols l) s) (mainWeight fp.Mc (bf.origCols l)) Φ)) 2 volume := by
      intro Φ hΦ
      have h := (bf.mainLabel_memLp l s a (fp.brank j)
        (mainLabelsM_subset _ _ _ _ _ hΦ)).indicator hmU
      rwa [Set.indicator_indicator, Set.inter_eq_left.mpr hUa] at h
    have hproj : ∀ p : Fin fp.P, colRelabel (bf.rv fp.Mc s) (columnL2Restriction cU hmU
        (((bf.mainBase fp.Mc s mb).withMask (fp.ballMaskT l s mb G j p)).proj u z)) ∈ M := by
      intro p
      set Ψ := (bf.mainBase fp.Mc s mb).withMask (fp.ballMaskT l s mb G j p)
      have hUΨ : U ∈ (Ψ.partition u).cells := hU
      have hr := DFunLike.congr_fun (Ψ.restrict_proj u hUΨ).1 z
      rw [ContinuousLinearMap.comp_apply] at hr
      change colRelabel (bf.rv fp.Mc s) (columnL2Restriction (dyadicGridCell Ψ.D.grid U.1 U.2)
        (dyadicGridCell_measurable Ψ.D.grid U.1 U.2) (Ψ.proj u z)) ∈ M
      rw [hr]
      have hin := Submodule.mem_map_of_mem (f := (colRelabel (bf.rv fp.Mc s)).toLinearMap)
        (cellColumnProjection_mem Ψ.D Ψ.A ((Ψ.partition u).subset hUΨ) z)
      rw [cellColumnRange_map_relabel Ψ.D Ψ.A ((Ψ.partition u).subset hUΨ) (f := bf.rv fp.Mc s)
        (φ' := mainScalar fp.Mc (bf.origCols l) s) (ε' := mainWeight fp.Mc (bf.origCols l))
        (fun v => rfl) (fun v => rfl) (fun v hv => hmemS _
          (fp.ballMaskT_labels_primaries l s mb G j p d ha hv))] at hin
      refine (Submodule.span_le.mpr ?_) hin
      rintro _ ⟨⟨v, hv⟩, -, rfl⟩
      exact Submodule.subset_span
        ⟨⟨v.1, fp.ballMaskT_labels_primaries l s mb G j p d ha hv⟩, rfl⟩
    have hmem : columnL2Restriction cU hmU
        (colRelabel (bf.rv fp.Mc s) (fp.gBall l s mb G j u z)) ∈ M := by
      rw [← colRelabel_restrict]
      unfold gBall opAvg
      rw [smul_apply, sum_apply, map_smul, map_sum,
        map_smul, map_sum]
      exact M.smul_mem _ (M.sum_mem fun p _ => hproj p)
    obtain ⟨cS, hcS⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hmem
    refine ⟨fun Φ => if h : Φ ∈ S then cS ⟨Φ, h⟩ else 0, ?_⟩
    rw [← hcS, ← Finset.sum_coe_sort S]
    exact Finset.sum_congr rfl fun Φ _ => by simp [Φ.2]

open Classical in
/-- The same representation for the basic coarse output `Z_{l,G,u}` (blueprint lines 1859, 1967). -/
theorem basicOut_cell_rep (l : Fin 4) (s : List (CatCol bf.Vtx)) (mb : bf.MainBudget s)
    (G : bf.Grp) (j : ℕ) (ls : List (ℕ × Bool)) (d : bf.Vtx) {u : ℤ} {U : ℤ × ℤ}
    (hU : U ∈ ((bf.mainBase fp.Mc s mb).partition u).cells) :
    (deepAnc (A := A) U = none ∧
      columnL2Restriction (dyadicGridCell A.G U.1 U.2) (dyadicGridCell_measurable A.G U.1 U.2)
        (fp.basicOut l s mb G j ls u) = 0) ∨
    ∃ a, deepAnc (A := A) U = some a ∧ ∃ c : bf.Lab ⊕ Fin fp.Mc → ℂ,
      columnL2Restriction (dyadicGridCell A.G U.1 U.2) (dyadicGridCell_measurable A.G U.1 U.2)
          (fp.basicOut l s mb G j ls u) =
        ∑ Φ ∈ fp.primaries l s G j d a, c Φ • mainCol A.G fp.Mc (bf.origCols l) s U Φ :=
  fp.gBall_cell_rep l s mb G j d hU _

end ActiveSetup.BasicFamilies.FamParams

/-- The restriction of a column vector to a set agrees almost everywhere with the indicator. -/
theorem columnL2Restriction_coeFn {W : Type*} [Fintype W] (s : Set ℝ) (hs : MeasurableSet s)
    (z : ColumnL2 W) :
    (columnL2Restriction s hs z : ℝ → ColumnHilbert W) =ᵐ[volume] s.indicator z :=
  columnL2Indicator_coeFn s hs z

namespace ActiveSetup.BasicFamilies.FamParams
variable {κ : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ c₀} {bf : A.BasicFamilies}
  (fp : bf.FamParams)

open Classical in
/-- An actual use of the group `G` at a cell (blueprint line 1753: "a group has an actual use
only at a current central assignment"): the cell is active and carries a present central vertex
with successful color data whose group is `G`. -/
def ActualUse (G : bf.Grp) (I : ℤ × ℤ) : Prop :=
  I ∈ A.cells ∧ ∃ x ∈ bf.admT.X (bf.admAt I),
    fp.K.Success (fp.K.colorData (bf.admT.st (bf.admAt I)) x) ∧
      fp.K.grp bf.admT A.famVtxBound (bf.admAt I) x = G

open Classical in
/-- Blueprint line 1967 (retention rule): the `v_b`-cells retained for the group `G` in the block
`[b, b + K)`: the cells of the attempt tree of depth `v_b = b - 2K` containing a cell with an
actual use of `G` at a depth of the block. -/
noncomputable def retainedV (G : bf.Grp) (b : ℤ) (K : ℕ) : Finset (ℤ × ℤ) :=
  (dyadicFiniteTree A.G A.R A.treeDepth).filter fun J => J.1 = b - 2 * K ∧
    ∃ I : ℤ × ℤ, dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G J.1 J.2 ∧ b ≤ I.1 ∧
      I.1 < b + K ∧ fp.ActualUse G I

open Classical in
theorem mem_retainedV {G : bf.Grp} {b : ℤ} {K : ℕ} {J : ℤ × ℤ} :
    J ∈ fp.retainedV G b K ↔ J ∈ dyadicFiniteTree A.G A.R A.treeDepth ∧ J.1 = b - 2 * K ∧
      ∃ I : ℤ × ℤ, dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G J.1 J.2 ∧ b ≤ I.1 ∧
        I.1 < b + K ∧ fp.ActualUse G I := by
  unfold retainedV; rw [Finset.mem_filter]

/-- Blueprint line 1967 ("freeze `Z_{l,G,u_b}`, setting it to zero before the attempt"): the frozen
basic coarse output of the role at the depth `u`; zero at depths before the attempt root. -/
noncomputable def frozenZ (l : Fin 4) (s : List (CatCol bf.Vtx)) (mb : bf.MainBudget s)
    (G : bf.Grp) (j : ℕ) (ls : List (ℕ × Bool)) (u : ℤ) : ColumnL2 (bf.Lab ⊕ Fin fp.Mc) :=
  if u < A.R.1 then 0 else fp.basicOut l s mb G j ls u

open Classical in
/-- The frozen output on a cell of the depth partition: zero, or a constant-coefficient
combination of the main columns of the primaries at the deepest active ancestor. -/
theorem frozenZ_cell_rep (l : Fin 4) (s : List (CatCol bf.Vtx)) (mb : bf.MainBudget s)
    (G : bf.Grp) (j : ℕ) (ls : List (ℕ × Bool)) (d : bf.Vtx) {u : ℤ} {U : ℤ × ℤ}
    (hU : U ∈ ((bf.mainBase fp.Mc s mb).partition u).cells) :
    columnL2Restriction (dyadicGridCell A.G U.1 U.2) (dyadicGridCell_measurable A.G U.1 U.2)
        (fp.frozenZ l s mb G j ls u) = 0 ∨
    ∃ a, deepAnc (A := A) U = some a ∧ ∃ c : bf.Lab ⊕ Fin fp.Mc → ℂ,
      columnL2Restriction (dyadicGridCell A.G U.1 U.2) (dyadicGridCell_measurable A.G U.1 U.2)
          (fp.frozenZ l s mb G j ls u) =
        ∑ Φ ∈ fp.primaries l s G j d a, c Φ • mainCol A.G fp.Mc (bf.origCols l) s U Φ := by
  unfold frozenZ
  split_ifs with hu
  · exact Or.inl (map_zero _)
  · rcases fp.basicOut_cell_rep l s mb G j ls d hU with ⟨-, h⟩ | h
    · exact Or.inl h
    · exact Or.inr h

open Classical in
/-- Blueprint line 1967 ("a mode available at `u_b` has first match no later than `u_b`"): a
first-match cell of a primary at an active cell `a` that meets a subcell `U` of `a` contains `U`. -/
theorem firstCell_contains (l : Fin 4) (s : List (CatCol bf.Vtx)) (G : bf.Grp) (j : ℕ)
    (d : bf.Vtx) {Φ : bf.Lab ⊕ Fin fp.Mc} {a U I₀ : ℤ × ℤ} (ha : a ∈ A.cells)
    (hΦ : Φ ∈ fp.primaries l s G j d a)
    (hUa : dyadicGridCell A.G U.1 U.2 ⊆ dyadicGridCell A.G a.1 a.2)
    (hI₀ : I₀ ∈ fp.firstCells A.cells l s G j d Φ) {y : ℝ}
    (hyU : y ∈ dyadicGridCell A.G U.1 U.2) (hyI : y ∈ dyadicGridCell A.G I₀.1 I₀.2) :
    dyadicGridCell A.G U.1 U.2 ⊆ dyadicGridCell A.G I₀.1 I₀.2 := by
  obtain ⟨I₁, hI₁, haI₁⟩ := fp.exists_firstCell A.cells l s G j d ha hΦ
  have h := fp.firstCell_unique A.cells l s G j d hI₀ hI₁ hyI (haI₁ (hUa hyU))
  subst h
  exact hUa.trans haI₁

open Classical in
/-- Blueprint line 1967 ("the preceding uniform budget applies to these particular endpoint
evaluations, and their coefficients are constant on their `u_b`-cells"): for a lift with the
exports of `mainAttemptLift` (on the family of all active cells), on every cell `U` of the depth
partition at `u` the lifted frozen output is a combination of augmented modes with coefficients
`β_m = c_(Φ(m)) a_m` constant on `U`, supported on the modes alive on `U` ("a mode available at
`u_b` has first match no later than `u_b`"), and `Σ_m |β_m| ≤ B √N colBudget ‖Z‖_U / √|U|`, where
`c` are the coefficients of the frozen output on `U`, `B` bounds the per-primary coefficient sums
and `N` the main labels at the active cells. -/
theorem frozen_endpoint {Md : Type} [Fintype Md] (l : Fin 4) (s : List (CatCol bf.Vtx))
    (mb : bf.MainBudget s) (G : bf.Grp) (j : ℕ) (ls : List (ℕ × Bool)) (d : bf.Vtx)
    (L : LiftData (bf.Lab ⊕ Fin fp.Mc) Md) (ψ : Md → ℝ → ℂ) {B : ℝ} (hB0 : 0 ≤ B)
    (hεP : ∀ Φ, L.εP Φ = mainWeight fp.Mc (bf.origCols l) Φ)
    (hsyn : ∀ y (β : bf.Lab ⊕ Fin fp.Mc → ℂ),
      (∀ Φ, β Φ ≠ 0 → ∃ I ∈ fp.firstCells A.cells l s G j d Φ,
        y ∈ dyadicGridCell A.G I.1 I.2) →
      L.at_ y (augmentedMain (fun Φ => mainScalar fp.Mc (bf.origCols l) s Φ y) L.εP β) =
        ∑ m, (β (L.own m) * L.a m y) • augmentedMode (fun m => ψ m y) L.εM m)
    (hcoef : ∀ Φ y, ∑ m ∈ Finset.univ.filter (fun m => L.own m = Φ), ‖L.a m y‖ ≤ B)
    (cellOf : Md → ℤ × ℤ) (hFM : ∀ m, cellOf m ∈ fp.firstCells A.cells l s G j d (L.own m))
    (hind : ∀ m y, L.a m y = (dyadicGridCell A.G (cellOf m).1 (cellOf m).2).indicator
      (fun _ => L.a m (dyadicGridLeft A.G (cellOf m).1 (cellOf m).2)) y)
    {N : ℝ} (hN : ∀ I ∈ A.cells,
      ((mainLabels A.G fp.Mc (bf.origCols l) s I (fp.brank j)).card : ℝ) ≤ N)
    {u : ℤ} {U : ℤ × ℤ} (hU : U ∈ ((bf.mainBase fp.Mc s mb).partition u).cells) :
    ∃ β : Md → ℂ,
      (∀ᵐ y ∂volume, y ∈ dyadicGridCell A.G U.1 U.2 →
        (L.op (fp.frozenZ l s mb G j ls u) : ℝ → ColumnHilbert Md) y =
          ∑ m, β m • augmentedMode (fun m => ψ m y) L.εM m) ∧
      (∀ m, β m ≠ 0 →
        dyadicGridCell A.G U.1 U.2 ⊆ dyadicGridCell A.G (cellOf m).1 (cellOf m).2) ∧
      ∑ m, ‖β m‖ ≤ B * (Real.sqrt N * A.colBudget *
        (‖columnL2Restriction (dyadicGridCell A.G U.1 U.2) (dyadicGridCell_measurable A.G U.1 U.2)
          (fp.frozenZ l s mb G j ls u)‖ / Real.sqrt (dyadicGridLength A.G U.1))) := by
  set! cU := dyadicGridCell A.G U.1 U.2
  have hmU : MeasurableSet cU := dyadicGridCell_measurable A.G U.1 U.2
  set Z := fp.frozenZ l s mb G j ls u
  have hcb := two_le_colBudget (A := A)
  have hnx : 0 ≤ ‖columnL2Restriction cU hmU Z‖ / Real.sqrt (dyadicGridLength A.G U.1) :=
    div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)
  -- `Z` agrees with its restriction on `U`
  have hZU : ∀ᵐ y ∂volume, y ∈ cU →
      (Z : ℝ → ColumnHilbert (bf.Lab ⊕ Fin fp.Mc)) y =
        (columnL2Restriction cU hmU Z : ℝ → ColumnHilbert (bf.Lab ⊕ Fin fp.Mc)) y := by
    filter_upwards [columnL2Indicator_coeFn cU hmU Z] with y hy hyU
    change _ = (columnL2Indicator cU hmU Z : ℝ → ColumnHilbert (bf.Lab ⊕ Fin fp.Mc)) y
    rw [hy, Set.indicator_of_mem hyU]
  rcases fp.frozenZ_cell_rep l s mb G j ls d hU with h0 | ⟨a, ha, c, hc⟩
  · refine ⟨0, ?_, fun m hm => absurd rfl hm, ?_⟩
    · filter_upwards [L.op_coeFn Z, hZU, Lp.coeFn_zero (E := ColumnHilbert (bf.Lab ⊕ Fin fp.Mc))
        (p := 2) (μ := volume)] with y h1 h2 h3 hyU
      rw [h1, h2 hyU, h0, h3, Pi.zero_apply, map_zero]
      exact (Finset.sum_eq_zero fun m _ => zero_smul ℂ _).symm
    · simp only [Pi.zero_apply, norm_zero, Finset.sum_const_zero]
      exact mul_nonneg hB0 (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (by linarith)) hnx)
  · obtain ⟨haC, hUa, -⟩ := deepAnc_spec ha
    set S := fp.primaries l s G j d a
    have hmemS : ∀ Φ ∈ S, MemLp (cU.indicator (privateColumnValue
        (mainScalar fp.Mc (bf.origCols l) s) (mainWeight fp.Mc (bf.origCols l)) Φ)) 2 volume := by
      intro Φ hΦ
      have h := (bf.mainLabel_memLp l s a (fp.brank j)
        (mainLabelsM_subset _ _ _ _ _ hΦ)).indicator hmU
      rwa [Set.indicator_indicator, Set.inter_eq_left.mpr hUa] at h
    obtain ⟨cS, hcS⟩ : ∃ cS : bf.Lab ⊕ Fin fp.Mc → ℂ,
        cS = fun Φ => if Φ ∈ S then c Φ else 0 := ⟨_, rfl⟩
    have hcSS : ∀ Φ, cS Φ ≠ 0 → Φ ∈ S := fun Φ hΦ => by
      by_contra h; exact hΦ (by rw [hcS]; simp [h])
    set! yU := dyadicGridLeft A.G U.1 U.2
    have hyUmem : yU ∈ cU := dyadicGridCell_left_mem A.G _ _
    -- the mode coefficients of the primaries at `a` are constant on `U`
    have hconst : ∀ m, cS (L.own m) ≠ 0 → ∀ y ∈ cU, L.a m y = L.a m yU := by
      intro m hm y hy
      have hS := hcSS _ hm
      rw [hind m y, hind m yU]
      by_cases hsub : cU ⊆ dyadicGridCell A.G (cellOf m).1 (cellOf m).2
      · rw [Set.indicator_of_mem (hsub hy), Set.indicator_of_mem (hsub hyUmem)]
      · have h1 : y ∉ dyadicGridCell A.G (cellOf m).1 (cellOf m).2 := fun h =>
          hsub (fp.firstCell_contains l s G j d haC hS hUa (hFM m) hy h)
        have h2 : yU ∉ dyadicGridCell A.G (cellOf m).1 (cellOf m).2 := fun h =>
          hsub (fp.firstCell_contains l s G j d haC hS hUa (hFM m) hyUmem h)
        rw [Set.indicator_of_notMem h1, Set.indicator_of_notMem h2]
    refine ⟨fun m => cS (L.own m) * L.a m yU, ?_, fun m hm => ?_, ?_⟩
    · have hcomb := mainCombination_coeFn (G := A.G) (Mc := fp.Mc) (O := bf.origCols l) s U S c
        hmemS
      have hW : mainWeight fp.Mc (bf.origCols l) = L.εP := (funext hεP).symm
      filter_upwards [L.op_coeFn Z, hZU, hcomb] with y h1 h2 h3 hyU
      rw [h1, h2 hyU, hc, h3 hyU, sum_privateColumnValue_eq, hW, ← hcS]
      rw [hsyn y cS (fun Φ hΦ => by
        obtain ⟨I₁, hI₁, haI₁⟩ := fp.exists_firstCell A.cells l s G j d haC (hcSS Φ hΦ)
        exact ⟨I₁, hI₁, haI₁ (hUa hyU)⟩)]
      refine Finset.sum_congr rfl fun m _ => ?_
      by_cases hm : cS (L.own m) = 0
      · simp [hm]
      · rw [hconst m hm y hyU]
    · -- a mode with a nonzero coefficient is alive on `U`
      have hc0 : cS (L.own m) ≠ 0 := fun h => hm (by simp only [h, zero_mul])
      have ha0 : L.a m yU ≠ 0 := fun h => hm (by simp only [h, mul_zero])
      have hy : yU ∈ dyadicGridCell A.G (cellOf m).1 (cellOf m).2 := by
        by_contra hy
        exact ha0 (by rw [hind m yU, Set.indicator_of_notMem hy])
      exact fp.firstCell_contains l s G j d haC (hcSS _ hc0) hUa (hFM m) hyUmem hy
    · have hrec := mainCoeff_sum_le (G := A.G) (Mc := fp.Mc) (O := bf.origCols l) s U S c hmemS
        (by linarith) (fun v _ => bf.inv_mainWeight_le l v)
      have hcard : (S.card : ℝ) ≤ N :=
        (Nat.cast_le.mpr (Finset.card_le_card (mainLabelsM_subset _ _ _ _ _))).trans (hN a haC)
      have hsumc : ∑ Φ ∈ S, ‖c Φ‖ ≤ Real.sqrt N * A.colBudget *
          (‖columnL2Restriction cU hmU Z‖ / Real.sqrt (dyadicGridLength A.G U.1)) := by
        refine hrec.trans ?_
        rw [← hc, mul_div_assoc]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hcard)
          (by linarith)) hnx
      have hcS1 : ∑ Φ, ‖cS Φ‖ = ∑ Φ ∈ S, ‖c Φ‖ := by
        rw [← Finset.sum_subset (Finset.subset_univ S) (fun Φ _ hΦ => by rw [hcS]; simp [hΦ])]
        exact Finset.sum_congr rfl fun Φ hΦ => by rw [hcS]; simp [hΦ]
      have hβ : ∑ m, ‖cS (L.own m) * L.a m yU‖ ≤ B * ∑ Φ, ‖cS Φ‖ := by
        rw [← Finset.sum_fiberwise Finset.univ L.own (fun m => ‖cS (L.own m) * L.a m yU‖),
          Finset.mul_sum]
        refine Finset.sum_le_sum fun Φ _ => ?_
        calc ∑ m ∈ Finset.univ.filter (fun m => L.own m = Φ), ‖cS (L.own m) * L.a m yU‖
            = ‖cS Φ‖ * ∑ m ∈ Finset.univ.filter (fun m => L.own m = Φ), ‖L.a m yU‖ := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun m hm => by
                rw [(Finset.mem_filter.mp hm).2, norm_mul]
          _ ≤ ‖cS Φ‖ * B := mul_le_mul_of_nonneg_left (hcoef Φ yU) (norm_nonneg _)
          _ = B * ‖cS Φ‖ := mul_comm _ _
      calc ∑ m, ‖cS (L.own m) * L.a m yU‖ ≤ B * ∑ Φ, ‖cS Φ‖ := hβ
        _ ≤ B * (Real.sqrt N * A.colBudget *
            (‖columnL2Restriction cU hmU Z‖ / Real.sqrt (dyadicGridLength A.G U.1))) := by
          rw [hcS1]; exact mul_le_mul_of_nonneg_left hsumc hB0

open Classical in
/-- Blueprint line 1967 ("write `ZTilde_(l,G,b) = R_(l,G) Z_(l,G,u_b)` on the retained
  branches"): the
frozen lifted output of the block `b`: the lift of the output frozen at `u_b = b - 4K`, restricted
to the union of the retained `v_b`-cells. -/
noncomputable def frozenLift {Md : Type} [Fintype Md] (L : LiftData (bf.Lab ⊕ Fin fp.Mc) Md)
    (l : Fin 4) (s : List (CatCol bf.Vtx)) (mb : bf.MainBudget s) (G : bf.Grp) (j : ℕ)
    (ls : List (ℕ × Bool)) (b : ℤ) (K : ℕ) : ColumnL2 Md :=
  columnL2Restriction (⋃ J ∈ fp.retainedV G b K, dyadicGridCell A.G J.1 J.2)
    (Finset.measurableSet_biUnion _ fun J _ => dyadicGridCell_measurable A.G J.1 J.2)
    (L.op (fp.frozenZ l s mb G j ls (b - 4 * K)))

open Classical in
/-- Blueprint line 1967: on a retained `v_b`-cell `J` inside a cell `U` of the depth partition at
`u_b = b - 4K`, the frozen lifted output `ZTilde_(l,G,b) = R_(l,G) Z_(l,G,u_b)` is a combination of
augmented modes with coefficients constant on `U` and supported on the modes alive on `U`, of
absolute sum at most the budget `D_*` times the normalized norm of the frozen output on `U` ("the
preceding uniform budget applies to these particular endpoint evaluations, and their coefficients
are constant on their `u_b`-cells"). The
lift is any lift with the exports of `mainAttemptLift` on the family of all active cells, for a
role with a nonnegative top score at a level `j ≤ 4`. -/
theorem frozenLift_retained {Md : Type} [Fintype Md] (D dB : ℕ) {H δc N : ℝ} (k : ℝ)
    (hHed : 2 ≤ fp.Hed) (hH : 1 ≤ H) (hδc : 0 < δc) (hN0 : 0 ≤ N) (l : Fin 4)
    (s : List (CatCol bf.Vtx)) (mb : bf.MainBudget s) (G : bf.Grp) {j : ℕ} (hj : j ≤ 4)
    (ls : List (ℕ × Bool)) (d : bf.Vtx) {g : ℤ} (hg : 0 ≤ g)
    (L : LiftData (bf.Lab ⊕ Fin fp.Mc) Md) (ψ : Md → ℝ → ℂ)
    (hεP : ∀ Φ, L.εP Φ = mainWeight fp.Mc (bf.origCols l) Φ)
    (hsyn : ∀ y (β : bf.Lab ⊕ Fin fp.Mc → ℂ),
      (∀ Φ, β Φ ≠ 0 → ∃ I ∈ fp.firstCells A.cells l s G j d Φ,
        y ∈ dyadicGridCell A.G I.1 I.2) →
      L.at_ y (augmentedMain (fun Φ => mainScalar fp.Mc (bf.origCols l) s Φ y) L.εP β) =
        ∑ m, (β (L.own m) * L.a m y) • augmentedMode (fun m => ψ m y) L.εM m)
    (hcoef : ∀ Φ y, ∑ m ∈ Finset.univ.filter (fun m => L.own m = Φ), ‖L.a m y‖ ≤
      Real.exp (D * (1 + Real.log (chartTranslationBudget (H ^ 6)) +
        Real.log (3 * fp.ballEdgeH dB (fp.ballRadius g (fp.bbase j + fp.P)))) ^ D))
    (cellOf : Md → ℤ × ℤ) (hFM : ∀ m, cellOf m ∈ fp.firstCells A.cells l s G j d (L.own m))
    (hind : ∀ m y, L.a m y = (dyadicGridCell A.G (cellOf m).1 (cellOf m).2).indicator
      (fun _ => L.a m (dyadicGridLeft A.G (cellOf m).1 (cellOf m).2)) y)
    (hN : ∀ I ∈ A.cells,
      ((mainLabels A.G fp.Mc (bf.origCols l) s I (fp.brank j)).card : ℝ) ≤ N)
    {b : ℤ} {K : ℕ} {J U : ℤ × ℤ} (hJ : J ∈ fp.retainedV G b K)
    (hU : U ∈ ((bf.mainBase fp.Mc s mb).partition (b - 4 * K)).cells)
    (hJU : dyadicGridCell A.G J.1 J.2 ⊆ dyadicGridCell A.G U.1 U.2) :
    ∃ β : Md → ℂ,
      (∀ᵐ y ∂volume, y ∈ dyadicGridCell A.G J.1 J.2 →
        (fp.frozenLift L l s mb G j ls b K : ℝ → ColumnHilbert Md) y =
          ∑ m, β m • augmentedMode (fun m => ψ m y) L.εM m) ∧
      (∀ m, β m ≠ 0 →
        dyadicGridCell A.G U.1 U.2 ⊆ dyadicGridCell A.G (cellOf m).1 (cellOf m).2) ∧
      ∑ m, ‖β m‖ ≤ fp.modeStar D dB H δc N k *
        (‖columnL2Restriction (dyadicGridCell A.G U.1 U.2) (dyadicGridCell_measurable A.G U.1 U.2)
          (fp.frozenZ l s mb G j ls (b - 4 * K))‖ / Real.sqrt (dyadicGridLength A.G U.1)) := by
  set B := Real.exp (D * (1 + Real.log (chartTranslationBudget (H ^ 6)) +
    Real.log (3 * fp.ballEdgeH dB (fp.ballRadius g (fp.bbase j + fp.P)))) ^ D)
  obtain ⟨β, hβ, hβa, hβs⟩ := fp.frozen_endpoint l s mb G j ls d L ψ (Real.exp_pos _).le hεP hsyn
    hcoef cellOf hFM hind hN hU (u := b - 4 * K)
  obtain ⟨-, -, -, -, -, -, h7, -, -⟩ := fp.le_modeStar D dB k hHed hH hδc hN0 hg hj
  refine ⟨β, ?_, hβa, ?_⟩
  · filter_upwards [hβ, columnL2Restriction_coeFn (⋃ J ∈ fp.retainedV G b K,
      dyadicGridCell A.G J.1 J.2) (Finset.measurableSet_biUnion _ fun J _ =>
        dyadicGridCell_measurable A.G J.1 J.2)
      (L.op (fp.frozenZ l s mb G j ls (b - 4 * K)))] with y h1 h2 hyJ
    unfold frozenLift
    rw [h2, Set.indicator_of_mem (Set.mem_iUnion₂.mpr ⟨J, hJ, hyJ⟩)]
    exact h1 (hJU hyJ)
  · set x := ‖columnL2Restriction (dyadicGridCell A.G U.1 U.2)
      (dyadicGridCell_measurable A.G U.1 U.2) (fp.frozenZ l s mb G j ls (b - 4 * K))‖ /
        Real.sqrt (dyadicGridLength A.G U.1)
    have hx : 0 ≤ x := div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)
    calc ∑ m, ‖β m‖ ≤ B * (Real.sqrt N * A.colBudget * x) := hβs
      _ = Real.sqrt N * A.colBudget * B * x := by ring
      _ ≤ fp.modeStar D dB H δc N k * x := mul_le_mul_of_nonneg_right h7 hx

end ActiveSetup.BasicFamilies.FamParams

/-! ### The main-column mode systems (blueprint lines 1971-1975) -/

namespace LiftData

/-- The lift with its primary labels transported along an equivalence (the mode data, weights and
coefficients are unchanged). -/
noncomputable def reindex {Pr Pr' Md : Type*} {_ : Fintype Pr} [Fintype Pr'] {_ : Fintype Md}
    {_ : DecidableEq Pr} [DecidableEq Pr'] (L : LiftData Pr Md) (e : Pr ≃ Pr') :
    LiftData Pr' Md where
  own := fun m => e (L.own m)
  s := L.s
  q := fun Φ => L.q (e.symm Φ)
  a := L.a
  εP := fun Φ => L.εP (e.symm Φ)
  εM := L.εM
  δ := L.δ
  a_meas := L.a_meas
  s_meas := L.s_meas
  s_le := L.s_le
  q_meas := fun _ => L.q_meas _
  q_le := fun _ => L.q_le _
  εP_pos := fun _ => L.εP_pos _
  q_sum := fun y => (e.symm.sum_comp fun Φ => ‖L.q Φ y‖ ^ 2 / L.εP Φ).trans_le (L.q_sum y)
  εM_nonneg := L.εM_nonneg
  weights := fun Φ y => by
    have h := L.weights (e.symm Φ) y
    refine le_of_eq_of_le (Finset.sum_congr ?_ fun _ _ => rfl) h
    ext m
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact e.eq_symm_apply.symm

end LiftData

namespace ActiveSetup.BasicFamilies.FamParams
variable {κ : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ c₀} {bf : A.BasicFamilies}
  (fp : bf.FamParams)

open Classical in
/-- The exports of `mainAttemptLift` (blueprint lines 1932-1940) for one role `l`, group `G` with
top score `g`, ball level `j` and catalog `s`, on the family of all active cells: the lift `L` with
the main private weights, its synthesis of main outputs into augmented modes with physical parts
`ψ`, the per-primary coefficient sums at most `exp(D X^D)`, first-match cells `cellOf` and
coefficients constant on them. -/
structure MainLiftExports (l : Fin 4) (s : List (CatCol bf.Vtx)) (G : bf.Grp) (j : ℕ)
    (d : bf.Vtx) (D dB : ℕ) (H : ℝ) (g : ℤ) {Md : Type} [Fintype Md]
    (L : LiftData (bf.Lab ⊕ Fin fp.Mc) Md) (ψ : Md → ℝ → ℂ) (cellOf : Md → ℤ × ℤ) : Prop where
  g_nonneg : 0 ≤ g
  εP_eq : ∀ Φ, L.εP Φ = mainWeight fp.Mc (bf.origCols l) Φ
  syn : ∀ y (β : bf.Lab ⊕ Fin fp.Mc → ℂ),
    (∀ Φ, β Φ ≠ 0 → ∃ I ∈ fp.firstCells A.cells l s G j d Φ,
      y ∈ dyadicGridCell A.G I.1 I.2) →
    L.at_ y (augmentedMain (fun Φ => mainScalar fp.Mc (bf.origCols l) s Φ y) L.εP β) =
      ∑ m, (β (L.own m) * L.a m y) • augmentedMode (fun m => ψ m y) L.εM m
  coef : ∀ Φ y, ∑ m ∈ Finset.univ.filter (fun m => L.own m = Φ), ‖L.a m y‖ ≤
    Real.exp (D * (1 + Real.log (chartTranslationBudget (H ^ 6)) +
      Real.log (3 * fp.ballEdgeH dB (fp.ballRadius g (fp.bbase j + fp.P)))) ^ D)
  first : ∀ m, cellOf m ∈ fp.firstCells A.cells l s G j d (L.own m)
  ind : ∀ m y, L.a m y = (dyadicGridCell A.G (cellOf m).1 (cellOf m).2).indicator
    (fun _ => L.a m (dyadicGridLeft A.G (cellOf m).1 (cellOf m).2)) y
  εM_le : ∀ m, L.εM m ≤ L.εP (L.own m)

end ActiveSetup.BasicFamilies.FamParams

open Classical in
/-- Blueprint lines 1971-1975 (the frozen-mode data interface) for the lift of `mainAttemptLift`:
the modes of one role and group of the attempt, with their first-match cells, curvatures, rational
frequency differences and private indices, form a mode system (`ModeSystem`, primary labels
relabeled by `Fin n`) whose waves are the physical modes of the lift `R_{l,G}` and whose private
weights are those of `R_{l,G}`; the lift has the exports of `mainAttemptLift` on the family of all
active cells, the corrections of size `δ_c` and the gauge `(ζ^ρ)²`. The mode system has the tag
`z` of the group, curvature bound `B = exp(D X^D)`, dimensions at most `d_B`, inverse private
weights at most `colBudget² (B² + 1)`, and at most
`N B (4 max(1, 4B/δ_c) + 1)^(4 d_B)` modes through each point and alive at each cell. -/
theorem exists_mainModeSystem (κ : LocalKernelClass) (c₀ : ℕ) :
    ∃ D : ℕ, 1 ≤ D ∧ ∀ (A : ActiveSetup κ c₀) (bf : A.BasicFamilies) (fp : bf.FamParams)
      (l : Fin 4) (s : List (CatCol bf.Vtx))
      (_hT : ∀ e ∈ s, ∃ R ∈ residueBox (bf.vtag e.tag).dim 9, ∃ γ : ℝ,
        e = templateCol (bf.vtag e.tag) l R γ e.birth e.rank e.tag)
      (_htag : ∀ e ∈ s, bf.occAvail e.tag.2.1 e.tag.1) (d : bf.Vtx)
      {G : bf.Grp} {j : ℕ} {ρ₀ : Fin fp.K.d0} {z : bf.Vtx} {g : ℤ} (_hG : G.2.1 = some (ρ₀, z, g))
      (_hg : 0 ≤ g) (_hHed : 2 ≤ fp.Hed) {dB : ℕ} (_hdim : ∀ w : bf.Vtx, (bf.vtag w).dim ≤ dB)
      (_hC : ∀ (w : bf.Vtx) a c, (rationalHeight ((bf.vtag w).C a c) : ℝ) ≤ fp.Hed)
      {δ : ℝ} (_hδ : 0 < δ) (_hδ' : δ < 1 / 4) (ρ : Fin (bf.vtag z).dim → ℝ)
      (_hρ : ∀ i, ρ i ∈ Set.Icc (0 : ℝ) 1) {H : ℝ} (_hHs : A.Hsrc ≤ H)
      (_hdz : ((bf.vtag z).dim : ℝ) ≤ Real.log H)
      (_hCz : ∀ i k, (chartRationalHeight ((((-slotCoeff l : ℤ) : ℚ) • (bf.vtag z).C) i k) : ℝ) ≤
        H)
      (_hHδ : ((bf.vtag z).dim : ℝ) * (bumpConst * 8 ^ 32 * (2 / δ)) ≤ H) {δc : ℝ} (_hδc : 0 < δc)
      {N : ℝ} (_hN0 : 0 ≤ N) (_hN : ∀ I ∈ A.cells,
        ((mainLabels A.G fp.Mc (bf.origCols l) s I (fp.brank j)).card : ℝ) ≤ N)
      (_hδcN : δc ^ 2 * N * A.colBudget ^ 2 ≤ 1),
      let X := 1 + Real.log (chartTranslationBudget (H ^ 6)) +
        Real.log (3 * fp.ballEdgeH dB (fp.ballRadius g (fp.bbase j + fp.P)))
      let B := Real.exp (D * X ^ D)
      ∃ (Ms : ModeSystem A.G (Fintype.card (bf.Lab ⊕ Fin fp.Mc)))
        (L : LiftData (bf.Lab ⊕ Fin fp.Mc) Ms.Md),
        fp.MainLiftExports l s G j d D dB H g L Ms.wave Ms.cellOf ∧
        (∀ m, L.εM m = Ms.L.εM m) ∧ (∀ m m', Ms.L.own m = Ms.L.own m' ↔ L.own m = L.own m') ∧
        L.δ = δc ∧
        (∀ y, L.s y = ((centerCut (bf.vtag z) δ ρ y : ℝ) : ℂ) ^ 2) ∧
        (∀ y, ∑ Φ, ‖L.q Φ y‖ ^ 2 / L.εP Φ ≤ δc ^ 2 * N * A.colBudget ^ 2) ∧
        Ms.zc = bf.vtag z ∧ Ms.δc = δ ∧ Ms.cl = slotCoeff l ∧
        (∀ i, Ms.ρ i ∈ Set.Icc (0 : ℝ) 1) ∧ Ms.Λ = B ∧
        Ms.Bσ = max 1 (B * (1 + 4 * (2 * dB + 1) * max 1 (4 * B / δc))) ∧
        (∀ p, Ms.dvOf p ≤ dB) ∧
        (∀ m, (Ms.L.εM m)⁻¹ ≤ A.colBudget ^ 2 * (B ^ 2 + 1)) ∧
        (∀ y, ((Finset.univ.filter fun m =>
            y ∈ dyadicGridCell A.G (Ms.cellOf m).1 (Ms.cellOf m).2).card : ℝ) ≤
          N * (B * (4 * max 1 (4 * B / δc) + 1) ^ (4 * dB))) ∧
        ∀ U : ℤ × ℤ, ((Ms.alive U).card : ℝ) ≤
          N * (B * (4 * max 1 (4 * B / δc) + 1) ^ (4 * dB)) := by
  obtain ⟨D, hD, hfin⟩ := ActiveSetup.BasicFamilies.FamParams.mainAttemptLift κ c₀
  refine ⟨D, hD, ?_⟩
  intro A bf fp l s hT htag d G j ρ₀ z g hG hg hHed dB hdim hC δ hδ hδ' ρ hρ H hHs hdz hCz hHδ
    δc hδc N hN0 hN hδcN X B
  obtain ⟨Md, hfinMd, L, ψ, hεP, hLδ, hεMpos, hεMle, hεMinv, hq, hs, -, -, -, hsyn, hcoef,
    ⟨cellOf, lamOf, γOf, hcell, hcount, Key, keyOf, dvOf, θvOf, -, -, hok, hkl, hdv, -, -, hkoc,
      hkd⟩, -⟩ := hfin A bf fp l s hT htag d A.cells subset_rfl hG hHed hdim hC hδ hδ' ρ hρ
    hHs hdz hCz hHδ hδc hN0 hN hδcN
  set! e := Fintype.equivFin (bf.Lab ⊕ Fin fp.Mc)
  set Bk := B * (1 + 4 * (2 * dB + 1) * max 1 (4 * B / δc))
  let Ms : ModeSystem A.G (Fintype.card (bf.Lab ⊕ Fin fp.Mc)) :=
    { Md := Md
      fin := hfinMd
      deq := Classical.decEq _
      L := L.reindex e
      zc := bf.vtag z
      δc := δ
      ρ := ρ
      cl := slotCoeff l
      cellOf := cellOf
      lamOf := lamOf
      γOf := γOf
      Key := Key
      kdeq := Classical.decEq _
      keyOf := keyOf
      dvOf := dvOf
      θvOf := θvOf
      Bσ := max 1 Bk
      one_le_Bσ := le_max_left _ _
      Λ := B
      key_own := fun m m' h => congrArg e (hkoc m m' h).1
      key_cell := fun m m' h => (hkoc m m' h).2
      own_cell_key := fun m m' h1 h2 => hok m m' (e.injective h1) h2
      key_lam := hkl
      key_diff := fun m m' h => by
        obtain ⟨a, b, ha, hb, hab⟩ := hkd m m' h
        exact ⟨a, b, fun i => (ha i).trans (le_max_right _ _),
          fun i => (hb i).trans (le_max_right _ _), hab⟩
      a_ind := fun m y => (hcell m).2.1 y
      lam_le := fun m => (hcell m).2.2.1
      εM_pos := hεMpos }
  have hwave : ∀ m y, Ms.wave m y = ψ m y := fun m y => by
    rw [(hcell m).2.2.2 y]; rfl
  have hpt : ∀ y, ((Finset.univ.filter fun m =>
      y ∈ dyadicGridCell A.G (Ms.cellOf m).1 (Ms.cellOf m).2).card : ℝ) ≤
        N * (B * (4 * max 1 (4 * B / δc) + 1) ^ (4 * dB)) := hcount
  refine ⟨Ms, L, ⟨hg, hεP, fun y β hβ => ?_, hcoef, fun m => (hcell m).1,
    fun m => (hcell m).2.1, hεMle⟩, fun m => rfl,
    fun m m' => e.injective.eq_iff, hLδ, hs, hq, rfl, rfl, rfl, hρ, rfl, rfl, hdv, hεMinv, hpt,
    fun U => ?_⟩
  · rw [hsyn y β hβ]
    simp only [hwave]
    rfl
  · -- the modes alive at `U` pass through its left endpoint
    refine le_trans ?_ (hpt (dyadicGridLeft A.G U.1 U.2))
    refine Nat.cast_le.mpr (Finset.card_le_card fun m hm => ?_)
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      (Ms.mem_alive).mp hm (dyadicGridCell_left_mem A.G U.1 U.2)⟩

end TrilinearHT.Auto

end
