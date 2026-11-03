/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

/- Adapted for Lean Pool from roos-j/lean-trilinearht at
7b4209609e6a7fb9d9935973ee8541495f943660. Imports, names, proof organization and
Mathlib interfaces have been updated; original authorship is retained above. -/

public import LeanPool.TrilinearHilbertTransform.Auto.Sec162QuantitativeInequality.TsideFLe

/-!
# Trilinear Hilbert transform: leaf_final
-/

@[expose] public section

section
namespace TrilinearHT.Auto
open MeasureTheory Metric
open scoped FourierTransform ComplexConjugate ENNReal

open scoped Classical in
private def LeafFinalStage4Statement : Prop :=
  ∀ (κ : LocalKernelClass)
    (q : ℝ)
    (hq2 : (2 : ℝ) < q)
    (hq3 : q < (3 : ℝ))
    (Nd : ℕ)
    (Msch : ℝ)
    (g : ℕ)
    (cT : ℝ)
    (cMc : ℝ)
    (cm : ℝ)
    (ce : ℝ)
    (ce2 : ℝ)
    (cQ : ℝ)
    (CΛ : ℕ)
    (_ : ℕ)
    (Cb : ℕ)
    (Cl : ℕ)
    (k : ℕ)
    (cc : ℕ)
    (_ : (1 : ℕ) ≤ cc)
    (kD : ℝ)
    (P : ℕ)
    (_ : (1 : ℕ) ≤ P)
    (Mp : ℕ)
    (V : ℕ)
    (famFuel : ℕ)
    (E : ℝ)
    (ρ : ℝ)
    (δ : ℝ)
    (η : ℝ)
    (η₀ : ℝ)
    (τ₃ : ℝ)
    (R : ℝ)
    (_ : (0 : ℝ) < ρ)
    (_ : ρ < (1 : ℝ))
    (_ : (0 : ℝ) ≤ η)
    (_ : (0 : ℝ) < η₀)
    (_ : (0 : ℝ) < τ₃)
    (S : ModeSchedule)
    (_ : (1 : ℕ) ≤ S.K)
    (Iw : ℕ)
    (Vl0 : ℝ)
    (TT : ℝ)
    (_ : (0 : ℝ) ≤ TT)
    (U : ℝ)
    (MV : ℝ)
    (ε : ℝ)
    (cB : ℝ)
    (eB : ℝ)
    (cM4 : ℝ)
    (cM3 : ℝ)
    (nearS : ℝ)
    (Γ : ℝ)
    (Os : Finset (Fin (4 : ℕ) × Fin (4 : ℕ) × ℕ × ℕ × ℕ × ℕ))
    (cE : ℝ)
    (Ee : ℝ)
    (fc : ℝ)
    (_ : fc = ((2 : ℝ) * (↑famFuel : ℝ) + (2 : ℝ)) * (((↑P : ℝ) + (1 : ℝ)) ^ (2 : ℕ) * ((16 :
      ℝ) * τ₃ * (2 : ℝ) ^ (2 : ℕ))))
    (_ : cm = (196608 : ℝ) * cT + (83 : ℝ) * ((1 : ℝ) + (81 : ℝ) * localFormUniformConstant κ
      * ((30000 : ℝ) + √cT)) * ((1 : ℝ) + cT) ^ (3 : ℕ) + cMc)
    (_ : ce = (6642 : ℝ) * localFormUniformConstant κ * ((60000 : ℝ) + √cT) ^ (3 : ℕ) * (288
      : ℝ) + (9 : ℝ) * ((16 : ℝ) * fourErrC κ (3 : ℕ) + (648 : ℝ) * threeErrC κ (3 : ℕ)
      (1 : ℕ) + (324 : ℝ) * threeErrC κ (3 : ℕ) (1 : ℕ) * √cT))
    (_ : (0 : ℝ) ≤ R)
    (_ : (20 : ℕ) ≤ Cb)
    (_ : (⌈Msch⌉₊ + (1 : ℕ)) * CΛ ^ (16 : ℕ) + (1 : ℕ) ≤ Cb)
    (_ : ⌈cm * (↑Cb : ℝ) ^ (59 : ℕ) + ce * (↑Cb : ℝ) ^ (18 : ℕ) + ce2 + (3 : ℝ) * (10 : ℝ) ^
      (11 : ℕ) * cQ⌉₊ + (59 : ℕ) * Cb + (4 : ℕ) * g + (8 : ℕ) * cc + (8 : ℕ) ≤ Cl)
    (u : ℝ)
    (_ : u = kD * (↑P : ℝ))
    (_ : (1 : ℝ) ≤ u)
    (B : ℝ)
    (_ : B = (↑Cb : ℝ) * u ^ Cb)
    (_ : (1 : ℝ) ≤ B)
    (X : ℝ)
    (_ : X = ((1 : ℝ) + Real.log ((2 : ℝ) * (↑k : ℝ))) ^ (2 : ℕ))
    (_ : (0 : ℝ) ≤ X)
    (G : ℝ)
    (_ : G = Real.exp ((↑g : ℝ) * X))
    (_ : (1 : ℝ) ≤ G)
    (_ : (1 : ℝ) ≤ (↑k : ℝ) ^ cc)
    (_ : (↑((2 : ℕ) ^ famFuel) : ℝ) ≤ B)
    (_ : (↑((2 : ℕ) * famFuel + (2 : ℕ)) : ℝ) + (1 : ℝ) ≤ B)
    (_ : TT ≤ cT * B ^ (11 : ℕ) * G)
    (_ : cB ≤ (30000 : ℝ) * B ^ (2 : ℕ) * G)
    (_ : (0 : ℝ) ≤ cB)
    (_ : eB ≤ (30000 : ℝ) * B ^ (2 : ℕ) * G)
    (_ : (0 : ℝ) ≤ eB)
    (_ : (1 : ℝ) ≤ cT)
    (_ : cM4 + cM3 ≤ cMc * B ^ (59 : ℕ) * G ^ (2 : ℕ))
    (_ : √((4 : ℝ) * ((↑(Mp * V) : ℝ) * R)) * √Ee ≤ (288 : ℝ) * Real.exp ((4 : ℝ) * (↑k : ℝ)
      ^ cc) * √δ * R)
    (ι : ℝ),
  let Qe : ℝ :=
    (16 : ℝ) * fourErrC κ (3 : ℕ) * ι + K1c * ((2 : ℝ) * fourKC κ (3 : ℕ) * (12 : ℝ) ^
      (4 : ℕ) * ε * U ^ (3 : ℕ) * S.Dstar ^ (4 : ℕ)) + (4 : ℝ) * ((81 : ℝ) * threeErrC κ
      (3 : ℕ) (1 : ℕ) * ι * U + K1c * ((8 : ℝ) * entryCU κ (3 : ℕ) (1 : ℕ) * (2 : ℝ) ^
      ((1 : ℕ) + (4 : ℕ)) * (12 : ℝ) ^ (3 : ℕ) * ε * U ^ (3 : ℕ) * (S.Dstar ^ (3 : ℕ) *
      ((↑Iw : ℝ) + (1 : ℝ)))))
  ∀ (_ : cE ≤ Qe * ((↑(Mp * V) : ℝ) * R))
    (_ : (↑(Mp * V) : ℝ) = MV)
    (_ : Qe * MV ≤ (5 : ℝ) * ((16 : ℝ) * fourErrC κ (3 : ℕ) + (648 : ℝ) * threeErrC κ (3 : ℕ)
      (1 : ℕ) + (324 : ℝ) * threeErrC κ (3 : ℕ) (1 : ℕ) * √cT) * Real.exp ((3 : ℝ) * (↑k
      : ℝ) ^ cc) * B ^ (6 : ℕ) * G * Real.exp (-kD) + ce2 * Real.exp (-(↑k : ℝ)))
    (_ : (0 : ℝ) ≤ localFormUniformConstant κ)
    (_ : (0 : ℝ) ≤ cT)
    (_ : (0 : ℝ) ≤ cMc)
    (_ : (0 : ℝ) ≤ cm)
    (_ : (0 : ℝ) ≤ ce)
    (_ : (0 : ℝ) ≤ ce2),
  let Nb : ℕ :=
    Nat.log (2 : ℕ) S.K + (1 : ℕ)
  ∀ (_ : Nb = Nat.log (2 : ℕ) S.K + (1 : ℕ)),
  let n : ℝ :=
    (↑Nb : ℝ)
  let Cjg : ℝ :=
    ((↑((2 : ℕ) * famFuel + (2 : ℕ)) : ℝ) + (1 : ℝ)) ^ (2 : ℕ) * Real.exp ((2 : ℝ) *
      ((1024 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) * ((1024 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) + (↑cc :
      ℝ) + (7 : ℝ)) * ((1 : ℝ) + Real.log ((2 : ℝ) * (↑k : ℝ))) ^ (2 : ℕ)))
  ∀ (_ : (1 : ℝ) ≤ Cjg),
  let G0e : ℝ :=
    Real.exp (((4096 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) * ((1024 : ℝ) * ((↑cc : ℝ) + (1 : ℝ))
      + (↑cc : ℝ) + (7 : ℝ)) + (↑cc : ℝ) ^ (2 : ℕ) + (3 : ℝ)) * ((1 : ℝ) + Real.log ((2
      : ℝ) * (↑k : ℝ))) ^ (2 : ℕ))
  let W : ℝ :=
    G0e + Vl0 + E + (1 : ℝ)
  ∀ (_ : Γ ≤ (2000 : ℝ) * (↑Os.card : ℝ) * (n ^ (3 : ℕ) * Cjg) * W)
    (_ : (1 : ℝ) ≤ W),
  let Yn : ℝ :=
    (↑Os.card : ℝ) * (↑Mp : ℝ) * (↑V : ℝ)
  ∀ (_ : (0 : ℝ) ≤ Yn),
  let Qk : ℝ :=
    hullCutConstant (ρ / (64 : ℝ) / (2 : ℝ)) * ((1 : ℝ) + Real.log ((2 : ℝ) + Yn)) *
      (↑Os.card : ℝ) * Cjg * W
  ∀ (_ : Qk = hullCutConstant (ρ / (64 : ℝ) / (2 : ℝ)) * ((1 : ℝ) + Real.log ((2 : ℝ) + Yn))
      * (↑Os.card : ℝ) * Cjg * W)
    (_ : (0 : ℝ) ≤ cQ)
    (_ : Qk ≤ cQ * Real.exp X ^ ((8 : ℕ) * cc + (4 : ℕ) + (2 : ℕ) * g)),
  let eq' : ℝ :=
    (2 : ℝ) * (q - (2 : ℝ)) / (q - (1 : ℝ))
  ∀ (_ : nearS ≤ (64 : ℝ) * ((4 : ℝ) * ((nbCM κ hq2 hq3 + nbCUM κ hq2 hq3) * ((1 : ℝ) +
      finiteDepthConstant κ q Nd) * ((1 : ℝ) + Real.log ((↑S.K : ℝ) + (2 : ℝ))) * ((↑S.K
      : ℝ) + (2 : ℝ)) ^ eq' * ((64 : ℝ) * ((2 : ℝ) * ((2 : ℝ) * √(1 : ℝ))) * ((2 : ℝ) *
      ((2 : ℝ) * √(1 : ℝ))))) * (hullCutConstant (ρ / (64 : ℝ) / (2 : ℝ)) * (↑(Nb + (1 :
      ℕ)) : ℝ) * ((1 : ℝ) + Real.log ((2 : ℝ) + (↑(Nb + (1 : ℕ)) : ℝ) * (↑(Nb + (1 : ℕ))
      : ℝ) * Yn))) * Γ / √(↑P : ℝ) * R))
    (_ : eq' = (2 : ℝ) * (q - (2 : ℝ)) / (q - (1 : ℝ))),
  let Kb : ℝ :=
    (↑Cl : ℝ) * u ^ Cl
  ∀ (_ : Kb = (↑Cl : ℝ) * u ^ Cl)
    (_ : (0 : ℝ) ≤ (↑S.K : ℝ))
    (_ : ((↑S.K : ℝ) + (2 : ℝ)) ^ eq' ≤ (Kb + (2 : ℝ)) ^ eq')
    (_ : ((2 : ℝ) + Real.log ((↑S.K : ℝ) + (2 : ℝ))) ^ (6 : ℕ) ≤ ((2 : ℝ) + Real.log (Kb + (2
      : ℝ))) ^ (6 : ℕ)),
  (6 : ℝ) * (256 : ℝ) * ((2 : ℝ) ^ famFuel) ^ (2 : ℕ) * ((2 : ℝ) * η₀ + fc) * TT * R +
    (6 : ℝ) * nearS + η ^ ((1 : ℝ) - ((1 : ℝ) - (1 / 1200 : ℝ))) * (TT ^ (((1 : ℝ) -
    (1 / 1200 : ℝ)) / (2 : ℝ)) * TT ^ (((1 : ℝ) - (1 / 1200 : ℝ)) / (2 : ℝ)) * TT ^
    (((1 : ℝ) - (1 / 1200 : ℝ)) / (2 : ℝ)) * R) + (82 : ℝ) * ((81 : ℝ) *
    (localFormUniformConstant κ * (cB + eB + √TT) ^ (3 : ℕ)) * (√((4 : ℝ) * ((↑(Mp *
    V) : ℝ) * R)) * √Ee)) + (82 : ℝ) * (η ^ ((1 : ℝ) - ((1 : ℝ) - (1 / 1200 : ℝ))) *
    ((81 : ℝ) * localFormUniformConstant κ * max cB √TT) ^ ((1 : ℝ) - (1 / 1200 : ℝ))
    * (TT ^ (((1 : ℝ) - (1 / 1200 : ℝ)) / (2 : ℝ)) * TT ^ (((1 : ℝ) - (1 / 1200 : ℝ))
    / (2 : ℝ)) * TT ^ (((1 : ℝ) - (1 / 1200 : ℝ)) / (2 : ℝ)) * R)) + (η ^ (1 / 1200 :
    ℝ) * (R * (cM4 + cM3)) + cE) ≤ leafBnd Cl kD P k cc η η₀ τ₃ δ (finiteDepthConstant
    κ q Nd) (nbCM κ hq2 hq3 + nbCUM κ hq2 hq3) q R


open scoped Classical in
private def LeafFinalStage3Statement : Prop :=
  ∀ (κ : LocalKernelClass)
    (q : ℝ)
    (hq2 : (2 : ℝ) < q)
    (hq3 : q < (3 : ℝ))
    (Nd : ℕ)
    (_ : ℕ)
    (Msch : ℝ)
    (g : ℕ)
    (cT : ℝ)
    (cL : ℝ)
    (cK : ℝ)
    (cMc : ℝ)
    (cm : ℝ)
    (ce : ℝ)
    (ce2 : ℝ)
    (cQ : ℝ)
    (CΛ : ℕ)
    (_ : ℕ)
    (_ : ℕ)
    (Cb : ℕ)
    (Cl : ℕ)
    (k : ℕ)
    (cc : ℕ)
    (_ : (1 : ℕ) ≤ cc)
    (_ : (2 : ℝ) ≤ (↑k : ℝ))
    (kD : ℝ)
    (P : ℕ)
    (_ : (1 : ℕ) ≤ P)
    (Nl : ℝ)
    (Mp : ℕ)
    (V : ℕ)
    (famFuel : ℕ)
    (_ : (↑((2 : ℕ) * famFuel + (2 : ℕ)) : ℝ) ≤ (↑cc : ℝ) * (Real.log (↑k : ℝ) + (1 : ℝ)))
    (dB : ℕ)
    (_ : (↑dB : ℝ) ≤ (↑k : ℝ) ^ cc)
    (E : ℝ)
    (ρ : ℝ)
    (δ : ℝ)
    (η : ℝ)
    (η₀ : ℝ)
    (τ₃ : ℝ)
    (R : ℝ)
    (_ : (0 : ℝ) ≤ E)
    (_ : E ≤ (↑k : ℝ) ^ cc)
    (_ : (0 : ℝ) < ρ)
    (_ : ρ < (1 : ℝ))
    (_ : ρ⁻¹ ≤ (↑k : ℝ) ^ cc)
    (_ : (0 : ℝ) ≤ η)
    (_ : (0 : ℝ) < η₀)
    (_ : (0 : ℝ) < τ₃)
    (S : ModeSchedule)
    (_ : (1 : ℕ) ≤ S.K)
    (_ : S.dmax = (2 : ℕ) * dB + (2 : ℕ))
    (_ : S.Dm = max (2 : ℝ) Nl)
    (Iw : ℕ)
    (Vl0 : ℝ)
    (TT : ℝ)
    (_ : (0 : ℝ) ≤ TT)
    (_ : TT ≤ (10 : ℝ) ^ (14 : ℕ) * ((1 : ℝ) + localFormUniformConstant κ) ^ (2 : ℕ) * (↑((2
      : ℕ) ^ famFuel) : ℝ) ^ (4 : ℕ) * ((1 : ℝ) + (↑((2 : ℕ) * famFuel + (2 : ℕ)) : ℝ))
      ^ (2 : ℕ) * ((1 : ℝ) + (↑S.K : ℝ)) ^ (2 : ℕ) * (Real.exp (((4096 : ℝ) * ((↑cc : ℝ)
      + (1 : ℝ)) * ((1024 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) + (↑cc : ℝ) + (7 : ℝ)) + (↑cc :
      ℝ) ^ (2 : ℕ) + (3 : ℝ)) * ((1 : ℝ) + Real.log ((2 : ℝ) * (↑k : ℝ))) ^ (2 : ℕ)) + E
      + Vl0 + (1 : ℝ)) / ρ)
    (U : ℝ)
    (MV : ℝ)
    (ε : ℝ)
    (T2v : ℝ)
    (_ : T2v ≤ (4 : ℝ) * ((↑S.K : ℝ) * ((20 : ℝ) * Real.exp (((4096 : ℝ) * ((↑cc : ℝ) + (1 :
      ℝ)) * ((1024 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) + (↑cc : ℝ) + (7 : ℝ)) + (↑cc : ℝ) ^ (2
      : ℕ) + (3 : ℝ)) * ((1 : ℝ) + Real.log ((2 : ℝ) * (↑k : ℝ))) ^ (2 : ℕ)) + (32 : ℝ))
      + (↑S.K : ℝ) * Vl0) / ρ)
    (cB : ℝ)
    (eB : ℝ)
    (cM4 : ℝ)
    (cM3 : ℝ)
    (nearS : ℝ)
    (Γ : ℝ)
    (Os : Finset (Fin (4 : ℕ) × Fin (4 : ℕ) × ℕ × ℕ × ℕ × ℕ))
    (_ : Os = ActiveSetup.BasicFamilies.FamParams.SideLeafM.nOs ((2 : ℕ) ^ famFuel) ((2 : ℕ)
      * famFuel + (2 : ℕ)))
    (_ : Γ ≤ (2000 : ℝ) * (↑Os.card : ℝ) * ((↑(Nat.log (2 : ℕ) S.K + (1 : ℕ)) : ℝ) ^ (3 : ℕ)
      * (((↑((2 : ℕ) * famFuel + (2 : ℕ)) : ℝ) + (1 : ℝ)) ^ (2 : ℕ) * Real.exp ((2 : ℝ)
      * ((1024 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) * ((1024 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) + (↑cc
      : ℝ) + (7 : ℝ)) * ((1 : ℝ) + Real.log ((2 : ℝ) * (↑k : ℝ))) ^ (2 : ℕ))))) *
      (Real.exp (((4096 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) * ((1024 : ℝ) * ((↑cc : ℝ) + (1 :
      ℝ)) + (↑cc : ℝ) + (7 : ℝ)) + (↑cc : ℝ) ^ (2 : ℕ) + (3 : ℝ)) * ((1 : ℝ) + Real.log
      ((2 : ℝ) * (↑k : ℝ))) ^ (2 : ℕ)) + Vl0 + E + (1 : ℝ)))
    (_ : nearS ≤ (64 : ℝ) * ((4 : ℝ) * ((nbCM κ hq2 hq3 + nbCUM κ hq2 hq3) * ((1 : ℝ) +
      finiteDepthConstant κ q Nd) * ((1 : ℝ) + Real.log ((↑S.K : ℝ) + (2 : ℝ))) * ((↑S.K
      : ℝ) + (2 : ℝ)) ^ ((2 : ℝ) * (q - (2 : ℝ)) / (q - (1 : ℝ))) * ((64 : ℝ) * ((2 : ℝ)
      * ((2 : ℝ) * √(1 : ℝ))) * ((2 : ℝ) * ((2 : ℝ) * √(1 : ℝ))))) * (hullCutConstant (ρ
      / (64 : ℝ) / (2 : ℝ)) * (↑(Nat.log (2 : ℕ) S.K + (1 : ℕ) + (1 : ℕ)) : ℝ) * ((1 :
      ℝ) + Real.log ((2 : ℝ) + (↑(Nat.log (2 : ℕ) S.K + (1 : ℕ) + (1 : ℕ)) : ℝ) *
      (↑(Nat.log (2 : ℕ) S.K + (1 : ℕ) + (1 : ℕ)) : ℝ) * ((↑Os.card : ℝ) * (↑Mp : ℝ) *
      (↑V : ℝ))))) * Γ / √(↑P : ℝ) * R))
    (cE : ℝ)
    (Ee : ℝ)
    (fc : ℝ)
    (_ : fc = ((2 : ℝ) * (↑famFuel : ℝ) + (2 : ℝ)) * (((↑P : ℝ) + (1 : ℝ)) ^ (2 : ℕ) * ((16 :
      ℝ) * τ₃ * (2 : ℝ) ^ (2 : ℕ))))
    (_ : cT = (10 : ℝ) ^ (22 : ℕ) * ((1 : ℝ) + localFormUniformConstant κ) ^ (2 : ℕ))
    (_ : cMc = (C4c κ + (4 : ℝ) * C3c κ) * cL ^ (4 : ℕ) * cK ^ (2 : ℕ))
    (_ : cm = (196608 : ℝ) * cT + (83 : ℝ) * ((1 : ℝ) + (81 : ℝ) * localFormUniformConstant κ
      * ((30000 : ℝ) + √cT)) * ((1 : ℝ) + cT) ^ (3 : ℕ) + cMc)
    (_ : ce = (6642 : ℝ) * localFormUniformConstant κ * ((60000 : ℝ) + √cT) ^ (3 : ℕ) * (288
      : ℝ) + (9 : ℝ) * ((16 : ℝ) * fourErrC κ (3 : ℕ) + (648 : ℝ) * threeErrC κ (3 : ℕ)
      (1 : ℕ) + (324 : ℝ) * threeErrC κ (3 : ℕ) (1 : ℕ) * √cT))
    (_ : ce2 = K1c * ((2 : ℝ) * fourKC κ (3 : ℕ) * (12 : ℝ) ^ (4 : ℕ)) + (4 : ℝ) * (K1c * ((8
      : ℝ) * entryCU κ (3 : ℕ) (1 : ℕ) * (2 : ℝ) ^ ((1 : ℕ) + (4 : ℕ)) * (12 : ℝ) ^ (3 :
      ℕ))) * (501 : ℝ))
    (_ : cQ = (65536 : ℝ) * ((8 : ℝ) + (80 : ℝ) * (9 : ℝ) ^ cc * (↑cc : ℝ)) * ((80 : ℝ) * (9
      : ℝ) ^ cc * (↑cc : ℝ)) * ((4 : ℝ) * (↑cc : ℝ) ^ (2 : ℕ)) * ((17 : ℝ) * (10 : ℝ) ^
      (7 : ℕ)))
    (_ : (1 : ℝ) ≤ (↑k : ℝ))
    (_ : (0 : ℝ) ≤ R)
    (_ : (20 : ℕ) ≤ Cb)
    (_ : (⌈Msch⌉₊ + (1 : ℕ)) * CΛ ^ (16 : ℕ) + (1 : ℕ) ≤ Cb)
    (_ : (↑g : ℝ) = (8192 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) * ((1024 : ℝ) * ((↑cc : ℝ) + (1 : ℝ))
      + (↑cc : ℝ) + (7 : ℝ)) + (↑cc : ℝ) ^ (2 : ℕ) + (8 : ℝ))
    (_ : ⌈cm * (↑Cb : ℝ) ^ (59 : ℕ) + ce * (↑Cb : ℝ) ^ (18 : ℕ) + ce2 + (3 : ℝ) * (10 : ℝ) ^
      (11 : ℕ) * cQ⌉₊ + (59 : ℕ) * Cb + (4 : ℕ) * g + (8 : ℕ) * cc + (8 : ℕ) ≤ Cl)
    (u : ℝ)
    (_ : u = kD * (↑P : ℝ))
    (_ : (1 : ℝ) ≤ u)
    (B : ℝ)
    (_ : B = (↑Cb : ℝ) * u ^ Cb)
    (_ : (1 : ℝ) ≤ B)
    (X : ℝ)
    (_ : X = ((1 : ℝ) + Real.log ((2 : ℝ) * (↑k : ℝ))) ^ (2 : ℕ))
    (_ : (0 : ℝ) ≤ X)
    (G : ℝ)
    (_ : G = Real.exp ((↑g : ℝ) * X))
    (_ : (1 : ℝ) ≤ G)
    (_ : ∀ c ≤ (↑g : ℝ), Real.exp (c * X) ≤ G)
    (_ : Real.exp (((4096 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) * ((1024 : ℝ) * ((↑cc : ℝ) + (1 : ℝ))
      + (↑cc : ℝ) + (7 : ℝ)) + (↑cc : ℝ) ^ (2 : ℕ) + (3 : ℝ)) * ((1 : ℝ) + Real.log ((2
      : ℝ) * (↑k : ℝ))) ^ (2 : ℕ)) ≤ G)
    (_ : (1 : ℝ) ≤ (↑k : ℝ) ^ cc)
    (_ : (1 : ℝ) ≤ S.Dstar)
    (_ : Real.log (max (2 : ℝ) Nl) ≤ (↑k : ℝ) ^ cc)
    (_ : (2 : ℝ) ≤ S.Dm)
    (_ : (↑S.K : ℝ) ≤ B)
    (_ : (↑((2 : ℕ) ^ famFuel) : ℝ) ≤ B)
    (_ : (↑((2 : ℕ) * famFuel + (2 : ℕ)) : ℝ) + (1 : ℝ) ≤ B)
    (_ : (0 : ℝ) ≤ Vl0)
    (_ : TT ≤ cT * B ^ (11 : ℕ) * G)
    (_ : cB ≤ (30000 : ℝ) * B ^ (2 : ℕ) * G)
    (_ : (0 : ℝ) ≤ cB)
    (_ : eB ≤ (30000 : ℝ) * B ^ (2 : ℕ) * G)
    (_ : (0 : ℝ) ≤ eB)
    (_ : (1 : ℝ) ≤ cT),
  let Gq : ℝ :=
    Real.exp (((6144 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) * ((1024 : ℝ) * ((↑cc : ℝ) + (1 : ℝ))
      + (↑cc : ℝ) + (7 : ℝ)) + (4 : ℝ)) * ((1 : ℝ) + Real.log ((2 : ℝ) * (↑k : ℝ))) ^ (2
      : ℕ))
  ∀ (_ : Gq ≤ G)
    (_ : Vl0 = (24 : ℝ) * ((↑⌊(180 : ℝ) * (↑S.dmax : ℝ) * Real.log ((2 : ℝ) * S.Dm) / (1 /
      1024 : ℝ)⌋₊ : ℝ) + (1 : ℝ)) * (Gq + (2 : ℝ) * (1 : ℝ) / S.Dstar ^ (394 : ℕ)))
    (_ : Gq = Real.exp (((6144 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) * ((1024 : ℝ) * ((↑cc : ℝ) + (1 :
      ℝ)) + (↑cc : ℝ) + (7 : ℝ)) + (4 : ℝ)) * ((1 : ℝ) + Real.log ((2 : ℝ) * (↑k : ℝ)))
      ^ (2 : ℕ)))
    (_ : cM4 + cM3 ≤ cMc * B ^ (59 : ℕ) * G ^ (2 : ℕ))
    (E1 : ℝ)
    (_ : E1 = Real.exp ((↑k : ℝ) ^ cc))
    (_ : (1 : ℝ) ≤ E1)
    (_ : (↑Mp : ℝ) ≤ E1)
    (_ : (↑V : ℝ) ≤ (5 : ℝ) * E1)
    (_ : √((4 : ℝ) * ((↑(Mp * V) : ℝ) * R)) * √Ee ≤ (288 : ℝ) * Real.exp ((4 : ℝ) * (↑k : ℝ)
      ^ cc) * √δ * R)
    (ι : ℝ),
  let Qe : ℝ :=
    (16 : ℝ) * fourErrC κ (3 : ℕ) * ι + K1c * ((2 : ℝ) * fourKC κ (3 : ℕ) * (12 : ℝ) ^
      (4 : ℕ) * ε * U ^ (3 : ℕ) * S.Dstar ^ (4 : ℕ)) + (4 : ℝ) * ((81 : ℝ) * threeErrC κ
      (3 : ℕ) (1 : ℕ) * ι * U + K1c * ((8 : ℝ) * entryCU κ (3 : ℕ) (1 : ℕ) * (2 : ℝ) ^
      ((1 : ℕ) + (4 : ℕ)) * (12 : ℝ) ^ (3 : ℕ) * ε * U ^ (3 : ℕ) * (S.Dstar ^ (3 : ℕ) *
      ((↑Iw : ℝ) + (1 : ℝ)))))
  ∀ (_ : cE ≤ Qe * ((↑(Mp * V) : ℝ) * R))
    (_ : (↑(Mp * V) : ℝ) = MV)
    (_ : Qe * MV ≤ (5 : ℝ) * ((16 : ℝ) * fourErrC κ (3 : ℕ) + (648 : ℝ) * threeErrC κ (3 : ℕ)
      (1 : ℕ) + (324 : ℝ) * threeErrC κ (3 : ℕ) (1 : ℕ) * √cT) * Real.exp ((3 : ℝ) * (↑k
      : ℝ) ^ cc) * B ^ (6 : ℕ) * G * Real.exp (-kD) + ce2 * Real.exp (-(↑k : ℝ))),
  (6 : ℝ) * (256 : ℝ) * ((2 : ℝ) ^ famFuel) ^ (2 : ℕ) * ((2 : ℝ) * η₀ + fc) * TT * R +
    (6 : ℝ) * nearS + η ^ ((1 : ℝ) - ((1 : ℝ) - (1 / 1200 : ℝ))) * (TT ^ (((1 : ℝ) -
    (1 / 1200 : ℝ)) / (2 : ℝ)) * TT ^ (((1 : ℝ) - (1 / 1200 : ℝ)) / (2 : ℝ)) * TT ^
    (((1 : ℝ) - (1 / 1200 : ℝ)) / (2 : ℝ)) * R) + (82 : ℝ) * ((81 : ℝ) *
    (localFormUniformConstant κ * (cB + eB + √TT) ^ (3 : ℕ)) * (√((4 : ℝ) * ((↑(Mp *
    V) : ℝ) * R)) * √Ee)) + (82 : ℝ) * (η ^ ((1 : ℝ) - ((1 : ℝ) - (1 / 1200 : ℝ))) *
    ((81 : ℝ) * localFormUniformConstant κ * max cB √TT) ^ ((1 : ℝ) - (1 / 1200 : ℝ))
    * (TT ^ (((1 : ℝ) - (1 / 1200 : ℝ)) / (2 : ℝ)) * TT ^ (((1 : ℝ) - (1 / 1200 : ℝ))
    / (2 : ℝ)) * TT ^ (((1 : ℝ) - (1 / 1200 : ℝ)) / (2 : ℝ)) * R)) + (η ^ (1 / 1200 :
    ℝ) * (R * (cM4 + cM3)) + cE) ≤ leafBnd Cl kD P k cc η η₀ τ₃ δ (finiteDepthConstant
    κ q Nd) (nbCM κ hq2 hq3 + nbCUM κ hq2 hq3) q R


open scoped Classical in
private def LeafFinalStage2Statement : Prop :=
  ∀ (κ : LocalKernelClass)
    (q : ℝ)
    (hq2 : (2 : ℝ) < q)
    (hq3 : q < (3 : ℝ))
    (Nd : ℕ)
    (_ : ℕ)
    (Msch : ℝ)
    (g : ℕ)
    (cT : ℝ)
    (cL : ℝ)
    (cK : ℝ)
    (cMc : ℝ)
    (cm : ℝ)
    (ce : ℝ)
    (ce2 : ℝ)
    (cQ : ℝ)
    (CΛ : ℕ)
    (_ : ℕ)
    (_ : ℕ)
    (Cb : ℕ)
    (Cl : ℕ)
    (k : ℕ)
    (cc : ℕ)
    (_ : (1 : ℕ) ≤ cc)
    (_ : (2 : ℝ) ≤ (↑k : ℝ))
    (kD : ℝ)
    (P : ℕ)
    (_ : (1 : ℕ) ≤ P)
    (cb : ℝ)
    (Nl : ℝ)
    (Mp : ℕ)
    (V : ℕ)
    (_ : (2 : ℝ) ≤ cb)
    (_ : (4 : ℝ) ≤ Nl)
    (famFuel : ℕ)
    (_ : (↑((2 : ℕ) * famFuel + (2 : ℕ)) : ℝ) ≤ (↑cc : ℝ) * (Real.log (↑k : ℝ) + (1 : ℝ)))
    (dB : ℕ)
    (_ : (1 : ℕ) ≤ dB)
    (_ : (↑dB : ℝ) ≤ (↑k : ℝ) ^ cc)
    (E : ℝ)
    (ρ : ℝ)
    (δ : ℝ)
    (η : ℝ)
    (η₀ : ℝ)
    (τ₃ : ℝ)
    (R : ℝ)
    (_ : (0 : ℝ) ≤ E)
    (_ : E ≤ (↑k : ℝ) ^ cc)
    (_ : (0 : ℝ) < ρ)
    (_ : ρ < (1 : ℝ))
    (_ : ρ⁻¹ ≤ (↑k : ℝ) ^ cc)
    (_ : (0 : ℝ) < δ)
    (_ : δ ≤ (1 / 8 : ℝ))
    (_ : (0 : ℝ) ≤ η)
    (_ : (0 : ℝ) < η₀)
    (_ : (0 : ℝ) < τ₃)
    (_ : (0 : ℝ) < R)
    (S : ModeSchedule)
    (_ : (2 : ℝ) ≤ S.Dstar)
    (_ : (2 : ℝ) ≤ S.H)
    (_ : (1 : ℕ) ≤ S.K)
    (_ : S.dmax = (2 : ℕ) * dB + (2 : ℕ))
    (_ : S.Dm = max (2 : ℝ) Nl)
    (_ : Real.exp kD ≤ S.Dstar)
    (Iw : ℕ)
    (_ : Iw = ⌊Real.logb (2 : ℝ) (S.Dstar ^ (250 : ℕ))⌋₊)
    (Vl0 : ℝ)
    (_ : Vl0 = (24 : ℝ) * ((↑⌊(180 : ℝ) * (↑S.dmax : ℝ) * Real.log ((2 : ℝ) * S.Dm) / (1 /
      1024 : ℝ)⌋₊ : ℝ) + (1 : ℝ)) * (Real.exp (((6144 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) *
      ((1024 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) + (↑cc : ℝ) + (7 : ℝ)) + (4 : ℝ)) * ((1 : ℝ) +
      Real.log ((2 : ℝ) * (↑k : ℝ))) ^ (2 : ℕ)) + (2 : ℝ) * (1 : ℝ) / S.Dstar ^ (394 :
      ℕ)))
    (TT : ℝ)
    (_ : (0 : ℝ) ≤ TT)
    (_ : TT ≤ (10 : ℝ) ^ (14 : ℕ) * ((1 : ℝ) + localFormUniformConstant κ) ^ (2 : ℕ) * (↑((2
      : ℕ) ^ famFuel) : ℝ) ^ (4 : ℕ) * ((1 : ℝ) + (↑((2 : ℕ) * famFuel + (2 : ℕ)) : ℝ))
      ^ (2 : ℕ) * ((1 : ℝ) + (↑S.K : ℝ)) ^ (2 : ℕ) * (Real.exp (((4096 : ℝ) * ((↑cc : ℝ)
      + (1 : ℝ)) * ((1024 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) + (↑cc : ℝ) + (7 : ℝ)) + (↑cc :
      ℝ) ^ (2 : ℕ) + (3 : ℝ)) * ((1 : ℝ) + Real.log ((2 : ℝ) * (↑k : ℝ))) ^ (2 : ℕ)) + E
      + Vl0 + (1 : ℝ)) / ρ)
    (U : ℝ)
    (_ : U = max ((2 : ℝ) * (cb + (2 : ℝ)) * S.Dstar ^ (2 : ℕ)) √TT)
    (MV : ℝ)
    (_ : MV = (↑Mp : ℝ) * (↑V : ℝ))
    (ε : ℝ)
    (_ : ε = (U ^ (3 : ℕ) * S.Dstar ^ (5 : ℕ) * Real.exp (↑k : ℝ) * ((1 : ℝ) + MV))⁻¹)
    (Mt : ℝ)
    (_ : Mt = (24 : ℝ) * ((2 : ℝ) * Real.exp (((6144 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) * ((1024 :
      ℝ) * ((↑cc : ℝ) + (1 : ℝ)) + (↑cc : ℝ) + (7 : ℝ)) + (4 : ℝ)) * ((1 : ℝ) + Real.log
      ((2 : ℝ) * (↑k : ℝ))) ^ (2 : ℕ)) + (2 : ℝ) * (↑S.K : ℝ) * Vl0) * (↑(Finset.range
      (S.Jstar + (1 : ℕ)) ×ˢ (Finset.range (Nat.log (2 : ℕ) ⌊S.Dstar⌋₊ + (1 : ℕ)) ×ˢ
      Finset.range (Nat.log (2 : ℕ) ⌊S.Dstar⌋₊ + (1 : ℕ))) ×ˢ dyThr ε U S.Dstar).card :
      ℝ) / ρ)
    (T2v : ℝ)
    (_ : T2v ≤ (4 : ℝ) * ((↑S.K : ℝ) * ((20 : ℝ) * Real.exp (((4096 : ℝ) * ((↑cc : ℝ) + (1 :
      ℝ)) * ((1024 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) + (↑cc : ℝ) + (7 : ℝ)) + (↑cc : ℝ) ^ (2
      : ℕ) + (3 : ℝ)) * ((1 : ℝ) + Real.log ((2 : ℝ) * (↑k : ℝ))) ^ (2 : ℕ)) + (32 : ℝ))
      + (↑S.K : ℝ) * Vl0) / ρ)
    (cB : ℝ)
    (eB : ℝ)
    (cM4 : ℝ)
    (cM3 : ℝ)
    (_ : cM4 = coreM4F κ S (1 / 1024 : ℝ) (3 : ℕ) U ε (max (max (1 : ℝ) Mt) TT))
    (_ : cM3 = ∑ l : Fin (4 : ℕ), coreM3F κ S (1 / 1024 : ℝ) (3 : ℕ) (1 : ℕ) Iw U ε (max (max
      (1 : ℝ) Mt) TT) l)
    (nearS : ℝ)
    (Γ : ℝ)
    (Os : Finset (Fin (4 : ℕ) × Fin (4 : ℕ) × ℕ × ℕ × ℕ × ℕ))
    (_ : Os = ActiveSetup.BasicFamilies.FamParams.SideLeafM.nOs ((2 : ℕ) ^ famFuel) ((2 : ℕ)
      * famFuel + (2 : ℕ)))
    (_ : Γ ≤ (2000 : ℝ) * (↑Os.card : ℝ) * ((↑(Nat.log (2 : ℕ) S.K + (1 : ℕ)) : ℝ) ^ (3 : ℕ)
      * (((↑((2 : ℕ) * famFuel + (2 : ℕ)) : ℝ) + (1 : ℝ)) ^ (2 : ℕ) * Real.exp ((2 : ℝ)
      * ((1024 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) * ((1024 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) + (↑cc
      : ℝ) + (7 : ℝ)) * ((1 : ℝ) + Real.log ((2 : ℝ) * (↑k : ℝ))) ^ (2 : ℕ))))) *
      (Real.exp (((4096 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) * ((1024 : ℝ) * ((↑cc : ℝ) + (1 :
      ℝ)) + (↑cc : ℝ) + (7 : ℝ)) + (↑cc : ℝ) ^ (2 : ℕ) + (3 : ℝ)) * ((1 : ℝ) + Real.log
      ((2 : ℝ) * (↑k : ℝ))) ^ (2 : ℕ)) + Vl0 + E + (1 : ℝ)))
    (_ : nearS ≤ (64 : ℝ) * ((4 : ℝ) * ((nbCM κ hq2 hq3 + nbCUM κ hq2 hq3) * ((1 : ℝ) +
      finiteDepthConstant κ q Nd) * ((1 : ℝ) + Real.log ((↑S.K : ℝ) + (2 : ℝ))) * ((↑S.K
      : ℝ) + (2 : ℝ)) ^ ((2 : ℝ) * (q - (2 : ℝ)) / (q - (1 : ℝ))) * ((64 : ℝ) * ((2 : ℝ)
      * ((2 : ℝ) * √(1 : ℝ))) * ((2 : ℝ) * ((2 : ℝ) * √(1 : ℝ))))) * (hullCutConstant (ρ
      / (64 : ℝ) / (2 : ℝ)) * (↑(Nat.log (2 : ℕ) S.K + (1 : ℕ) + (1 : ℕ)) : ℝ) * ((1 :
      ℝ) + Real.log ((2 : ℝ) + (↑(Nat.log (2 : ℕ) S.K + (1 : ℕ) + (1 : ℕ)) : ℝ) *
      (↑(Nat.log (2 : ℕ) S.K + (1 : ℕ) + (1 : ℕ)) : ℝ) * ((↑Os.card : ℝ) * (↑Mp : ℝ) *
      (↑V : ℝ))))) * Γ / √(↑P : ℝ) * R))
    (cE : ℝ)
    (_ : cE ≤ ((16 : ℝ) * fourErrC κ (3 : ℕ) * ((S.Dstar ^ (100 : ℕ))⁻¹ * S.Dstar ^ (10 : ℕ))
      + K1c * ((2 : ℝ) * fourKC κ (3 : ℕ) * (12 : ℝ) ^ (4 : ℕ) * ε * U ^ (3 : ℕ) *
      S.Dstar ^ (4 : ℕ)) + (4 : ℝ) * ((81 : ℝ) * threeErrC κ (3 : ℕ) (1 : ℕ) * ((S.Dstar
      ^ (100 : ℕ))⁻¹ * S.Dstar ^ (10 : ℕ)) * U + K1c * ((8 : ℝ) * entryCU κ (3 : ℕ) (1 :
      ℕ) * (2 : ℝ) ^ ((1 : ℕ) + (4 : ℕ)) * (12 : ℝ) ^ (3 : ℕ) * ε * U ^ (3 : ℕ) *
      (S.Dstar ^ (3 : ℕ) * ((↑Iw : ℝ) + (1 : ℝ)))))) * ((↑(Mp * V) : ℝ) * R))
    (Ee : ℝ)
    (_ : (0 : ℝ) ≤ Ee)
    (_ : Ee ≤ ((8 : ℝ) * (↑dB : ℝ) * δ + (2 : ℝ) * δ ^ (2 : ℕ)) * ((4 : ℝ) * Nl * cb ^ (2 :
      ℕ) * (1 : ℝ)) * (↑((4 : ℕ) * (Mp * V)) : ℝ) * R)
    (fc : ℝ)
    (_ : fc = ((2 : ℝ) * (↑famFuel : ℝ) + (2 : ℝ)) * (((↑P : ℝ) + (1 : ℝ)) ^ (2 : ℕ) * ((16 :
      ℝ) * τ₃ * (2 : ℝ) ^ (2 : ℕ))))
    (_ : cT = (10 : ℝ) ^ (22 : ℕ) * ((1 : ℝ) + localFormUniformConstant κ) ^ (2 : ℕ))
    (_ : cK = ((1 : ℝ) + (7 : ℝ) * (10 : ℝ) ^ (9 : ℕ) + cT) * (cL + (2 : ℝ)))
    (_ : cMc = (C4c κ + (4 : ℝ) * C3c κ) * cL ^ (4 : ℕ) * cK ^ (2 : ℕ))
    (_ : cm = (196608 : ℝ) * cT + (83 : ℝ) * ((1 : ℝ) + (81 : ℝ) * localFormUniformConstant κ
      * ((30000 : ℝ) + √cT)) * ((1 : ℝ) + cT) ^ (3 : ℕ) + cMc)
    (_ : ce = (6642 : ℝ) * localFormUniformConstant κ * ((60000 : ℝ) + √cT) ^ (3 : ℕ) * (288
      : ℝ) + (9 : ℝ) * ((16 : ℝ) * fourErrC κ (3 : ℕ) + (648 : ℝ) * threeErrC κ (3 : ℕ)
      (1 : ℕ) + (324 : ℝ) * threeErrC κ (3 : ℕ) (1 : ℕ) * √cT))
    (_ : ce2 = K1c * ((2 : ℝ) * fourKC κ (3 : ℕ) * (12 : ℝ) ^ (4 : ℕ)) + (4 : ℝ) * (K1c * ((8
      : ℝ) * entryCU κ (3 : ℕ) (1 : ℕ) * (2 : ℝ) ^ ((1 : ℕ) + (4 : ℕ)) * (12 : ℝ) ^ (3 :
      ℕ))) * (501 : ℝ))
    (_ : cQ = (65536 : ℝ) * ((8 : ℝ) + (80 : ℝ) * (9 : ℝ) ^ cc * (↑cc : ℝ)) * ((80 : ℝ) * (9
      : ℝ) ^ cc * (↑cc : ℝ)) * ((4 : ℝ) * (↑cc : ℝ) ^ (2 : ℕ)) * ((17 : ℝ) * (10 : ℝ) ^
      (7 : ℕ)))
    (_ : (1 : ℝ) ≤ (↑k : ℝ))
    (_ : (0 : ℝ) ≤ R)
    (_ : (20 : ℕ) ≤ Cb)
    (_ : (⌈Msch⌉₊ + (1 : ℕ)) * CΛ ^ (16 : ℕ) + (1 : ℕ) ≤ Cb)
    (_ : (↑g : ℝ) = (8192 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) * ((1024 : ℝ) * ((↑cc : ℝ) + (1 : ℝ))
      + (↑cc : ℝ) + (7 : ℝ)) + (↑cc : ℝ) ^ (2 : ℕ) + (8 : ℝ))
    (_ : ⌈cm * (↑Cb : ℝ) ^ (59 : ℕ) + ce * (↑Cb : ℝ) ^ (18 : ℕ) + ce2 + (3 : ℝ) * (10 : ℝ) ^
      (11 : ℕ) * cQ⌉₊ + (59 : ℕ) * Cb + (4 : ℕ) * g + (8 : ℕ) * cc + (8 : ℕ) ≤ Cl)
    (u : ℝ)
    (_ : u = kD * (↑P : ℝ))
    (_ : (1 : ℝ) ≤ u)
    (B : ℝ)
    (_ : B = (↑Cb : ℝ) * u ^ Cb)
    (_ : (2 : ℝ) ≤ B)
    (_ : (1 : ℝ) ≤ B)
    (X : ℝ)
    (_ : X = ((1 : ℝ) + Real.log ((2 : ℝ) * (↑k : ℝ))) ^ (2 : ℕ))
    (_ : (0 : ℝ) ≤ X)
    (G : ℝ)
    (_ : G = Real.exp ((↑g : ℝ) * X))
    (_ : (1 : ℝ) ≤ G)
    (_ : ∀ c ≤ (↑g : ℝ), Real.exp (c * X) ≤ G)
    (_ : Real.exp (((4096 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) * ((1024 : ℝ) * ((↑cc : ℝ) + (1 : ℝ))
      + (↑cc : ℝ) + (7 : ℝ)) + (↑cc : ℝ) ^ (2 : ℕ) + (3 : ℝ)) * ((1 : ℝ) + Real.log ((2
      : ℝ) * (↑k : ℝ))) ^ (2 : ℕ)) ≤ G)
    (_ : Real.exp (((6144 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) * ((1024 : ℝ) * ((↑cc : ℝ) + (1 : ℝ))
      + (↑cc : ℝ) + (7 : ℝ)) + (4 : ℝ)) * ((1 : ℝ) + Real.log ((2 : ℝ) * (↑k : ℝ))) ^ (2
      : ℕ)) ≤ G)
    (_ : (0 : ℝ) ≤ Nl)
    (_ : (2 : ℝ) * cb ≤ Real.exp ((↑k : ℝ) ^ cc))
    (_ : Nl ≤ Real.exp ((↑k : ℝ) ^ cc))
    (_ : (↑Mp : ℝ) ≤ Real.exp ((↑k : ℝ) ^ cc))
    (_ : (↑V : ℝ) ≤ (5 : ℝ) * Real.exp ((↑k : ℝ) ^ cc))
    (_ : (1 : ℝ) ≤ (↑k : ℝ) ^ cc)
    (_ : (0 : ℝ) < S.Dstar)
    (_ : (1 : ℝ) ≤ S.Dstar)
    (_ : Real.log (max (2 : ℝ) Nl) ≤ (↑k : ℝ) ^ cc)
    (_ : (2 : ℝ) ≤ S.Dm)
    (_ : (↑S.K : ℝ) ≤ B)
    (_ : (↑S.Jstar : ℝ) + (1 : ℝ) ≤ B)
    (_ : Real.log S.H ≤ B)
    (_ : Real.log S.Dstar ≤ B)
    (_ : (↑S.dmax : ℝ) + (5 : ℝ) ≤ B)
    (_ : (↑Iw : ℝ) + (1 : ℝ) ≤ B)
    (_ : (↑((2 : ℕ) ^ famFuel) : ℝ) ≤ B)
    (_ : (↑((2 : ℕ) * famFuel + (2 : ℕ)) : ℝ) + (1 : ℝ) ≤ B)
    (_ : (0 : ℝ) ≤ Vl0)
    (_ : Vl0 ≤ (14000000 : ℝ) * B ^ (2 : ℕ) * G)
    (_ : TT ≤ cT * B ^ (11 : ℕ) * G)
    (_ : (1 : ℝ) / ρ ≤ B)
    (_ : cB ≤ (30000 : ℝ) * B ^ (2 : ℕ) * G)
    (_ : (0 : ℝ) ≤ cB)
    (_ : eB ≤ (30000 : ℝ) * B ^ (2 : ℕ) * G)
    (_ : (0 : ℝ) ≤ eB)
    (_ : (16 : ℝ) ≤ U)
    (_ : (0 : ℝ) < U)
    (_ : (0 : ℝ) ≤ MV)
    (_ : (0 : ℝ) < ε)
    (_ : (↑(dyThr ε U S.Dstar).card : ℝ) ≤ Real.logb (2 : ℝ) U - Real.logb (2 : ℝ) ε + (3 :
      ℝ))
    (_ : (1 : ℝ) ≤ cT)
    (_ : (0 : ℝ) ≤ Real.logb (2 : ℝ) (U / ε) + (1 : ℝ))
    (_ : Real.logb (2 : ℝ) (U / ε) + (1 : ℝ) ≤ cL * B)
    (_ : (0 : ℝ) ≤ cL),
  (6 : ℝ) * (256 : ℝ) * ((2 : ℝ) ^ famFuel) ^ (2 : ℕ) * ((2 : ℝ) * η₀ + fc) * TT * R +
    (6 : ℝ) * nearS + η ^ ((1 : ℝ) - ((1 : ℝ) - (1 / 1200 : ℝ))) * (TT ^ (((1 : ℝ) -
    (1 / 1200 : ℝ)) / (2 : ℝ)) * TT ^ (((1 : ℝ) - (1 / 1200 : ℝ)) / (2 : ℝ)) * TT ^
    (((1 : ℝ) - (1 / 1200 : ℝ)) / (2 : ℝ)) * R) + (82 : ℝ) * ((81 : ℝ) *
    (localFormUniformConstant κ * (cB + eB + √TT) ^ (3 : ℕ)) * (√((4 : ℝ) * ((↑(Mp *
    V) : ℝ) * R)) * √Ee)) + (82 : ℝ) * (η ^ ((1 : ℝ) - ((1 : ℝ) - (1 / 1200 : ℝ))) *
    ((81 : ℝ) * localFormUniformConstant κ * max cB √TT) ^ ((1 : ℝ) - (1 / 1200 : ℝ))
    * (TT ^ (((1 : ℝ) - (1 / 1200 : ℝ)) / (2 : ℝ)) * TT ^ (((1 : ℝ) - (1 / 1200 : ℝ))
    / (2 : ℝ)) * TT ^ (((1 : ℝ) - (1 / 1200 : ℝ)) / (2 : ℝ)) * R)) + (η ^ (1 / 1200 :
    ℝ) * (R * (cM4 + cM3)) + cE) ≤ leafBnd Cl kD P k cc η η₀ τ₃ δ (finiteDepthConstant
    κ q Nd) (nbCM κ hq2 hq3 + nbCUM κ hq2 hq3) q R


open scoped Classical in
private def LeafFinalStage1Statement : Prop :=
  ∀ (κ : LocalKernelClass)
    (q : ℝ)
    (hq2 : (2 : ℝ) < q)
    (hq3 : q < (3 : ℝ))
    (Nd : ℕ)
    (Cg : ℕ)
    (Msch : ℝ)
    (g : ℕ)
    (cT : ℝ)
    (cL : ℝ)
    (cK : ℝ)
    (cMc : ℝ)
    (cm : ℝ)
    (ce : ℝ)
    (ce2 : ℝ)
    (cQ : ℝ)
    (CΛ : ℕ)
    (_ : ℕ)
    (_ : ℕ)
    (Cb : ℕ)
    (Cl : ℕ)
    (k : ℕ)
    (cc : ℕ)
    (_ : (1 : ℕ) ≤ cc)
    (_ : (2 : ℝ) ≤ (↑k : ℝ))
    (kD : ℝ)
    (P : ℕ)
    (_ : (1 : ℕ) ≤ P)
    (cb : ℝ)
    (Nl : ℝ)
    (Mp : ℕ)
    (V : ℕ)
    (_ : (2 : ℝ) ≤ cb)
    (_ : (4 : ℝ) ≤ Nl)
    (_ : Real.log ((2 : ℝ) * cb) ≤ (↑k : ℝ) ^ cc)
    (famFuel : ℕ)
    (_ : (↑((2 : ℕ) * famFuel + (2 : ℕ)) : ℝ) ≤ (↑cc : ℝ) * (Real.log (↑k : ℝ) + (1 : ℝ)))
    (dB : ℕ)
    (_ : (1 : ℕ) ≤ dB)
    (_ : (↑dB : ℝ) ≤ (↑k : ℝ) ^ cc)
    (E : ℝ)
    (ρ : ℝ)
    (δ : ℝ)
    (η : ℝ)
    (η₀ : ℝ)
    (τ₃ : ℝ)
    (R : ℝ)
    (_ : (0 : ℝ) ≤ E)
    (_ : E ≤ (↑k : ℝ) ^ cc)
    (_ : (0 : ℝ) < ρ)
    (_ : ρ < (1 : ℝ))
    (_ : ρ⁻¹ ≤ (↑k : ℝ) ^ cc)
    (_ : (0 : ℝ) < δ)
    (_ : δ ≤ (1 / 8 : ℝ))
    (_ : (0 : ℝ) ≤ η)
    (_ : (0 : ℝ) < η₀)
    (_ : (0 : ℝ) < τ₃)
    (_ : (0 : ℝ) < R)
    (S : ModeSchedule)
    (_ : (2 : ℝ) ≤ S.Dstar)
    (_ : (2 : ℝ) ≤ S.H)
    (_ : (1 : ℕ) ≤ S.K)
    (_ : S.dmax = (2 : ℕ) * dB + (2 : ℕ))
    (_ : S.Dm = max (2 : ℝ) Nl)
    (_ : Real.exp kD ≤ S.Dstar)
    (Iw : ℕ)
    (_ : Iw = ⌊Real.logb (2 : ℝ) (S.Dstar ^ (250 : ℕ))⌋₊)
    (Vl0 : ℝ)
    (_ : Vl0 = (24 : ℝ) * ((↑⌊(180 : ℝ) * (↑S.dmax : ℝ) * Real.log ((2 : ℝ) * S.Dm) / (1 /
      1024 : ℝ)⌋₊ : ℝ) + (1 : ℝ)) * (Real.exp (((6144 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) *
      ((1024 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) + (↑cc : ℝ) + (7 : ℝ)) + (4 : ℝ)) * ((1 : ℝ) +
      Real.log ((2 : ℝ) * (↑k : ℝ))) ^ (2 : ℕ)) + (2 : ℝ) * (1 : ℝ) / S.Dstar ^ (394 :
      ℕ)))
    (TT : ℝ)
    (_ : (0 : ℝ) ≤ TT)
    (_ : TT ≤ (10 : ℝ) ^ (14 : ℕ) * ((1 : ℝ) + localFormUniformConstant κ) ^ (2 : ℕ) * (↑((2
      : ℕ) ^ famFuel) : ℝ) ^ (4 : ℕ) * ((1 : ℝ) + (↑((2 : ℕ) * famFuel + (2 : ℕ)) : ℝ))
      ^ (2 : ℕ) * ((1 : ℝ) + (↑S.K : ℝ)) ^ (2 : ℕ) * (Real.exp (((4096 : ℝ) * ((↑cc : ℝ)
      + (1 : ℝ)) * ((1024 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) + (↑cc : ℝ) + (7 : ℝ)) + (↑cc :
      ℝ) ^ (2 : ℕ) + (3 : ℝ)) * ((1 : ℝ) + Real.log ((2 : ℝ) * (↑k : ℝ))) ^ (2 : ℕ)) + E
      + Vl0 + (1 : ℝ)) / ρ)
    (U : ℝ)
    (_ : U = max ((2 : ℝ) * (cb + (2 : ℝ)) * S.Dstar ^ (2 : ℕ)) √TT)
    (MV : ℝ)
    (_ : MV = (↑Mp : ℝ) * (↑V : ℝ))
    (ε : ℝ)
    (_ : ε = (U ^ (3 : ℕ) * S.Dstar ^ (5 : ℕ) * Real.exp (↑k : ℝ) * ((1 : ℝ) + MV))⁻¹)
    (Mt : ℝ)
    (_ : Mt = (24 : ℝ) * ((2 : ℝ) * Real.exp (((6144 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) * ((1024 :
      ℝ) * ((↑cc : ℝ) + (1 : ℝ)) + (↑cc : ℝ) + (7 : ℝ)) + (4 : ℝ)) * ((1 : ℝ) + Real.log
      ((2 : ℝ) * (↑k : ℝ))) ^ (2 : ℕ)) + (2 : ℝ) * (↑S.K : ℝ) * Vl0) * (↑(Finset.range
      (S.Jstar + (1 : ℕ)) ×ˢ (Finset.range (Nat.log (2 : ℕ) ⌊S.Dstar⌋₊ + (1 : ℕ)) ×ˢ
      Finset.range (Nat.log (2 : ℕ) ⌊S.Dstar⌋₊ + (1 : ℕ))) ×ˢ dyThr ε U S.Dstar).card :
      ℝ) / ρ)
    (T2v : ℝ)
    (_ : T2v ≤ (4 : ℝ) * ((↑S.K : ℝ) * ((20 : ℝ) * Real.exp (((4096 : ℝ) * ((↑cc : ℝ) + (1 :
      ℝ)) * ((1024 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) + (↑cc : ℝ) + (7 : ℝ)) + (↑cc : ℝ) ^ (2
      : ℕ) + (3 : ℝ)) * ((1 : ℝ) + Real.log ((2 : ℝ) * (↑k : ℝ))) ^ (2 : ℕ)) + (32 : ℝ))
      + (↑S.K : ℝ) * Vl0) / ρ)
    (B0 : ℝ)
    (cB : ℝ)
    (eB : ℝ)
    (_ : B0 = (2 : ℝ))
    (_ : cB = coreBd B0 T2v)
    (_ : eB = errBd B0 T2v)
    (cM4 : ℝ)
    (cM3 : ℝ)
    (_ : cM4 = coreM4F κ S (1 / 1024 : ℝ) (3 : ℕ) U ε (max (max (1 : ℝ) Mt) TT))
    (_ : cM3 = ∑ l : Fin (4 : ℕ), coreM3F κ S (1 / 1024 : ℝ) (3 : ℕ) (1 : ℕ) Iw U ε (max (max
      (1 : ℝ) Mt) TT) l)
    (nearS : ℝ)
    (Γ : ℝ)
    (Os : Finset (Fin (4 : ℕ) × Fin (4 : ℕ) × ℕ × ℕ × ℕ × ℕ))
    (_ : Os = ActiveSetup.BasicFamilies.FamParams.SideLeafM.nOs ((2 : ℕ) ^ famFuel) ((2 : ℕ)
      * famFuel + (2 : ℕ)))
    (_ : Γ ≤ (2000 : ℝ) * (↑Os.card : ℝ) * ((↑(Nat.log (2 : ℕ) S.K + (1 : ℕ)) : ℝ) ^ (3 : ℕ)
      * (((↑((2 : ℕ) * famFuel + (2 : ℕ)) : ℝ) + (1 : ℝ)) ^ (2 : ℕ) * Real.exp ((2 : ℝ)
      * ((1024 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) * ((1024 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) + (↑cc
      : ℝ) + (7 : ℝ)) * ((1 : ℝ) + Real.log ((2 : ℝ) * (↑k : ℝ))) ^ (2 : ℕ))))) *
      (Real.exp (((4096 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) * ((1024 : ℝ) * ((↑cc : ℝ) + (1 :
      ℝ)) + (↑cc : ℝ) + (7 : ℝ)) + (↑cc : ℝ) ^ (2 : ℕ) + (3 : ℝ)) * ((1 : ℝ) + Real.log
      ((2 : ℝ) * (↑k : ℝ))) ^ (2 : ℕ)) + Vl0 + E + (1 : ℝ)))
    (_ : nearS ≤ (64 : ℝ) * ((4 : ℝ) * ((nbCM κ hq2 hq3 + nbCUM κ hq2 hq3) * ((1 : ℝ) +
      finiteDepthConstant κ q Nd) * ((1 : ℝ) + Real.log ((↑S.K : ℝ) + (2 : ℝ))) * ((↑S.K
      : ℝ) + (2 : ℝ)) ^ ((2 : ℝ) * (q - (2 : ℝ)) / (q - (1 : ℝ))) * ((64 : ℝ) * ((2 : ℝ)
      * ((2 : ℝ) * √(1 : ℝ))) * ((2 : ℝ) * ((2 : ℝ) * √(1 : ℝ))))) * (hullCutConstant (ρ
      / (64 : ℝ) / (2 : ℝ)) * (↑(Nat.log (2 : ℕ) S.K + (1 : ℕ) + (1 : ℕ)) : ℝ) * ((1 :
      ℝ) + Real.log ((2 : ℝ) + (↑(Nat.log (2 : ℕ) S.K + (1 : ℕ) + (1 : ℕ)) : ℝ) *
      (↑(Nat.log (2 : ℕ) S.K + (1 : ℕ) + (1 : ℕ)) : ℝ) * ((↑Os.card : ℝ) * (↑Mp : ℝ) *
      (↑V : ℝ))))) * Γ / √(↑P : ℝ) * R))
    (cE : ℝ)
    (_ : cE ≤ ((16 : ℝ) * fourErrC κ (3 : ℕ) * ((S.Dstar ^ (100 : ℕ))⁻¹ * S.Dstar ^ (10 : ℕ))
      + K1c * ((2 : ℝ) * fourKC κ (3 : ℕ) * (12 : ℝ) ^ (4 : ℕ) * ε * U ^ (3 : ℕ) *
      S.Dstar ^ (4 : ℕ)) + (4 : ℝ) * ((81 : ℝ) * threeErrC κ (3 : ℕ) (1 : ℕ) * ((S.Dstar
      ^ (100 : ℕ))⁻¹ * S.Dstar ^ (10 : ℕ)) * U + K1c * ((8 : ℝ) * entryCU κ (3 : ℕ) (1 :
      ℕ) * (2 : ℝ) ^ ((1 : ℕ) + (4 : ℕ)) * (12 : ℝ) ^ (3 : ℕ) * ε * U ^ (3 : ℕ) *
      (S.Dstar ^ (3 : ℕ) * ((↑Iw : ℝ) + (1 : ℝ)))))) * ((↑(Mp * V) : ℝ) * R))
    (Ee : ℝ)
    (_ : (0 : ℝ) ≤ Ee)
    (_ : Ee ≤ ((8 : ℝ) * (↑dB : ℝ) * δ + (2 : ℝ) * δ ^ (2 : ℕ)) * ((4 : ℝ) * Nl * cb ^ (2 :
      ℕ) * (1 : ℝ)) * (↑((4 : ℕ) * (Mp * V)) : ℝ) * R)
    (fc : ℝ)
    (_ : fc = ((2 : ℝ) * (↑famFuel : ℝ) + (2 : ℝ)) * (((↑P : ℝ) + (1 : ℝ)) ^ (2 : ℕ) * ((16 :
      ℝ) * τ₃ * (2 : ℝ) ^ (2 : ℕ))))
    (_ : cT = (10 : ℝ) ^ (22 : ℕ) * ((1 : ℝ) + localFormUniformConstant κ) ^ (2 : ℕ))
    (_ : cL = (159 : ℝ) + (32 : ℝ) * (↑g : ℝ) + (8 : ℝ) * Real.log cT)
    (_ : cK = ((1 : ℝ) + (7 : ℝ) * (10 : ℝ) ^ (9 : ℕ) + cT) * (cL + (2 : ℝ)))
    (_ : cMc = (C4c κ + (4 : ℝ) * C3c κ) * cL ^ (4 : ℕ) * cK ^ (2 : ℕ))
    (_ : cm = (196608 : ℝ) * cT + (83 : ℝ) * ((1 : ℝ) + (81 : ℝ) * localFormUniformConstant κ
      * ((30000 : ℝ) + √cT)) * ((1 : ℝ) + cT) ^ (3 : ℕ) + cMc)
    (_ : ce = (6642 : ℝ) * localFormUniformConstant κ * ((60000 : ℝ) + √cT) ^ (3 : ℕ) * (288
      : ℝ) + (9 : ℝ) * ((16 : ℝ) * fourErrC κ (3 : ℕ) + (648 : ℝ) * threeErrC κ (3 : ℕ)
      (1 : ℕ) + (324 : ℝ) * threeErrC κ (3 : ℕ) (1 : ℕ) * √cT))
    (_ : ce2 = K1c * ((2 : ℝ) * fourKC κ (3 : ℕ) * (12 : ℝ) ^ (4 : ℕ)) + (4 : ℝ) * (K1c * ((8
      : ℝ) * entryCU κ (3 : ℕ) (1 : ℕ) * (2 : ℝ) ^ ((1 : ℕ) + (4 : ℕ)) * (12 : ℝ) ^ (3 :
      ℕ))) * (501 : ℝ))
    (_ : cQ = (65536 : ℝ) * ((8 : ℝ) + (80 : ℝ) * (9 : ℝ) ^ cc * (↑cc : ℝ)) * ((80 : ℝ) * (9
      : ℝ) ^ cc * (↑cc : ℝ)) * ((4 : ℝ) * (↑cc : ℝ) ^ (2 : ℕ)) * ((17 : ℝ) * (10 : ℝ) ^
      (7 : ℕ)))
    (_ : (1 : ℝ) ≤ (↑k : ℝ))
    (_ : (0 : ℝ) ≤ R)
    (_ : (20 : ℕ) ≤ Cb)
    (_ : cc + (1 : ℕ) ≤ Cb)
    (_ : (500 : ℕ) * Cg + (1 : ℕ) ≤ Cb)
    (_ : (⌈Msch⌉₊ + (1 : ℕ)) * CΛ ^ (16 : ℕ) + (1 : ℕ) ≤ Cb)
    (_ : (3 : ℕ) ^ cc ≤ Cb)
    (_ : (↑g : ℝ) = (8192 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) * ((1024 : ℝ) * ((↑cc : ℝ) + (1 : ℝ))
      + (↑cc : ℝ) + (7 : ℝ)) + (↑cc : ℝ) ^ (2 : ℕ) + (8 : ℝ))
    (_ : ⌈cm * (↑Cb : ℝ) ^ (59 : ℕ) + ce * (↑Cb : ℝ) ^ (18 : ℕ) + ce2 + (3 : ℝ) * (10 : ℝ) ^
      (11 : ℕ) * cQ⌉₊ + (59 : ℕ) * Cb + (4 : ℕ) * g + (8 : ℕ) * cc + (8 : ℕ) ≤ Cl)
    (_ : (↑k : ℝ) ≤ (↑k : ℝ) ^ cc)
    (u : ℝ)
    (_ : Real.log S.Dstar ≤ (↑Cg : ℝ) * u ^ Cg)
    (_ : u = kD * (↑P : ℝ))
    (_ : (1 : ℝ) ≤ u)
    (B : ℝ)
    (_ : B = (↑Cb : ℝ) * u ^ Cb)
    (_ : ∀ (c : ℝ) (e : ℕ), (0 : ℝ) ≤ c → c ≤ (↑Cb : ℝ) → e ≤ Cb → c * u ^ e ≤ B)
    (_ : (20 : ℝ) ≤ (↑Cb : ℝ))
    (_ : (2 : ℝ) ≤ B)
    (_ : (1 : ℝ) ≤ B)
    (_ : ∀ (c : ℝ), (0 : ℝ) ≤ c → c ≤ (↑Cb : ℝ) → c * (↑k : ℝ) ^ cc ≤ B)
    (X : ℝ)
    (_ : X = ((1 : ℝ) + Real.log ((2 : ℝ) * (↑k : ℝ))) ^ (2 : ℕ))
    (_ : (0 : ℝ) ≤ X)
    (_ : X ≤ (4 : ℝ) * (↑k : ℝ))
    (G : ℝ)
    (_ : G = Real.exp ((↑g : ℝ) * X))
    (_ : (1 : ℝ) ≤ G)
    (_ : ∀ c ≤ (↑g : ℝ), Real.exp (c * X) ≤ G)
    (_ : Real.exp (((4096 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) * ((1024 : ℝ) * ((↑cc : ℝ) + (1 : ℝ))
      + (↑cc : ℝ) + (7 : ℝ)) + (↑cc : ℝ) ^ (2 : ℕ) + (3 : ℝ)) * ((1 : ℝ) + Real.log ((2
      : ℝ) * (↑k : ℝ))) ^ (2 : ℕ)) ≤ G)
    (_ : Real.exp (((6144 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) * ((1024 : ℝ) * ((↑cc : ℝ) + (1 : ℝ))
      + (↑cc : ℝ) + (7 : ℝ)) + (4 : ℝ)) * ((1 : ℝ) + Real.log ((2 : ℝ) * (↑k : ℝ))) ^ (2
      : ℕ)) ≤ G)
    (_ : (0 : ℝ) ≤ Nl)
    (_ : (2 : ℝ) * cb ≤ Real.exp ((↑k : ℝ) ^ cc))
    (_ : Nl ≤ Real.exp ((↑k : ℝ) ^ cc))
    (_ : (↑Mp : ℝ) ≤ Real.exp ((↑k : ℝ) ^ cc))
    (_ : (↑V : ℝ) ≤ (5 : ℝ) * Real.exp ((↑k : ℝ) ^ cc))
    (_ : (1 : ℝ) ≤ (↑k : ℝ) ^ cc)
    (_ : (0 : ℝ) < S.Dstar)
    (_ : (1 : ℝ) ≤ S.Dstar)
    (_ : (0 : ℝ) ≤ Real.log S.Dstar)
    (_ : Real.log (max (2 : ℝ) Nl) ≤ (↑k : ℝ) ^ cc)
    (_ : (2 : ℝ) ≤ S.Dm)
    (_ : (↑S.K : ℝ) ≤ B)
    (_ : (↑S.Jstar : ℝ) + (1 : ℝ) ≤ B)
    (_ : Real.log S.H ≤ B)
    (_ : Real.log S.Dstar ≤ B),
  (6 : ℝ) * (256 : ℝ) * ((2 : ℝ) ^ famFuel) ^ (2 : ℕ) * ((2 : ℝ) * η₀ + fc) * TT * R +
    (6 : ℝ) * nearS + η ^ ((1 : ℝ) - ((1 : ℝ) - (1 / 1200 : ℝ))) * (TT ^ (((1 : ℝ) -
    (1 / 1200 : ℝ)) / (2 : ℝ)) * TT ^ (((1 : ℝ) - (1 / 1200 : ℝ)) / (2 : ℝ)) * TT ^
    (((1 : ℝ) - (1 / 1200 : ℝ)) / (2 : ℝ)) * R) + (82 : ℝ) * ((81 : ℝ) *
    (localFormUniformConstant κ * (cB + eB + √TT) ^ (3 : ℕ)) * (√((4 : ℝ) * ((↑(Mp *
    V) : ℝ) * R)) * √Ee)) + (82 : ℝ) * (η ^ ((1 : ℝ) - ((1 : ℝ) - (1 / 1200 : ℝ))) *
    ((81 : ℝ) * localFormUniformConstant κ * max cB √TT) ^ ((1 : ℝ) - (1 / 1200 : ℝ))
    * (TT ^ (((1 : ℝ) - (1 / 1200 : ℝ)) / (2 : ℝ)) * TT ^ (((1 : ℝ) - (1 / 1200 : ℝ))
    / (2 : ℝ)) * TT ^ (((1 : ℝ) - (1 / 1200 : ℝ)) / (2 : ℝ)) * R)) + (η ^ (1 / 1200 :
    ℝ) * (R * (cM4 + cM3)) + cE) ≤ leafBnd Cl kD P k cc η η₀ τ₃ δ (finiteDepthConstant
    κ q Nd) (nbCM κ hq2 hq3 + nbCUM κ hq2 hq3) q R




private theorem leaf_final_stage_4 : LeafFinalStage4Statement := by
  classical
  intro κ q hq2 hq3 Nd Msch g cT cMc cm ce ce2 cQ CΛ t3 Cb Cl k cc hcc kD P hP Mp V famFuel E ρ δ
    η η₀ τ₃ R hρ hρ1 hη0 hη₀ hτ₃ S hK1 Iw Vl0 TT hT0 U MV ε cB eB cM4 cM3 nearS Γ Os cE Ee fc hfc
    hcm hce hR0 hCb20n hMCb2 hClb u hu hu1 B hBdef hBB1 X hX hX0 G hGdef hG1 hkcc1 hLpB hJmB hT
    hcBd hcBd0 heBd heBd0 hcT1 hcMtot hME ι Qe hcEsum hMVc hQeMV hL00 hcT0 hcMcn hcmn hcen hce2n
    Nb hNb n Cjg hCjg1 G0e W hΓle hW1 Yn hYn0 Qk hQkdef hcQ0 hQk eq' hnearS heq' Kb hKb hK0' hKp
    hlamb
  have! hKp0 : 0 ≤ ((S.K : ℝ) + 2) ^ eq' := by positivity
  have! hlam := near_lambda_le S.K hK1 hYn0
  rw [← hNb] at hlam
  have! hCN0 : 0 ≤ 1 + finiteDepthConstant κ q Nd := by
    have! this := (finiteDepthConstant_bounds κ hq2.le Nd).1; linarith only [this]
  have! hnbc : 0 ≤ nbCM κ hq2 hq3 + nbCUM κ hq2 hq3 := by
    have! h1 := nbCM_nonneg κ hq2 hq3
    have! h2 := (Classical.choose_spec (near_band_critical_UM κ hq2 hq3)).1
    change 0 ≤ nbCUM κ hq2 hq3 at h2
    linarith only [h1, h2]
  have! hP0 : 0 ≤ Real.sqrt P := Real.sqrt_nonneg _
  have! hh0 : 0 ≤ hullCutConstant (ρ / 64 / 2) :=
    (hullCutConstant_pos (by positivity) (by linarith only [hρ1, hρ])).le
  have! hL10 : 0 ≤ 1 + Real.log ((S.K : ℝ) + 2) := by
    have! this := Real.log_nonneg (show (1 : ℝ) ≤ (S.K : ℝ) + 2 by linarith only [hK0'])
    linarith only [this]
  have! hN10 : (0 : ℝ) ≤ ((Nb + 1 : ℕ) : ℝ) := Nat.cast_nonneg _
  have! hLY0 : 0 ≤ 1 + Real.log (2 + ((Nb + 1 : ℕ) : ℝ) * ((Nb + 1 : ℕ) : ℝ) * Yn) := by
    have! this := Real.log_nonneg (show (1 : ℝ) ≤
        2 + ((Nb + 1 : ℕ) : ℝ) * ((Nb + 1 : ℕ) : ℝ) * Yn by
      have! this : 0 ≤ ((Nb + 1 : ℕ) : ℝ) * ((Nb + 1 : ℕ) : ℝ) * Yn :=
        mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hYn0
      linarith only [this])
    linarith only [this]
  have! hcore : (1 + Real.log ((S.K : ℝ) + 2)) * ((Nb + 1 : ℕ) : ℝ) *
      (1 + Real.log (2 + ((Nb + 1 : ℕ) : ℝ) * ((Nb + 1 : ℕ) : ℝ) * Yn)) * Γ *
        hullCutConstant (ρ / 64 / 2) ≤ 160000 * (2 + Real.log ((S.K : ℝ) + 2)) ^ 6 * Qk :=
    leaf_final_hcore k cc Mp V famFuel E ρ S Vl0 Γ Os hCjg1 hΓle hW1 hQkdef hlam hh0 hL10 hN10 hLY0
  have! hNEAR : 6 * nearS ≤
      (Cl : ℝ) * (1 + finiteDepthConstant κ q Nd) * (nbCM κ hq2 hq3 + nbCUM κ hq2 hq3) *
        (Kb + 2) ^ eq' * (2 + Real.log (Kb + 2)) ^ 6 * Real.exp X ^ Cl / Real.sqrt P *
        R :=
    leaf_final_hNEAR κ q hq2 hq3 Nd Msch g cm ce ce2 cQ CΛ Cb Cl k cc hcc P Mp V famFuel E ρ R S
      Vl0 nearS Γ Os hR0 hCb20n hMCb2 hClb u hu1 X hX0 hcmn hcen hce2n hCjg1 hW1 hYn0 hQkdef hcQ0
      hQk hnearS hKp hlamb hKp0 hCN0 hnbc hP0 hh0 hcore
  -- the main and error collapses
  have! hX1 : 1 ≤ Real.exp X := Real.one_le_exp hX0
  have! hGX : G = Real.exp X ^ g := by rw [hGdef, ← Real.exp_nat_mul]
  have! hBn0 : 0 ≤ B := by linarith only [hBB1]
  have! hGn0 : 0 ≤ G := by linarith only [hG1]
  have! hceil : cm * Cb ^ 59 + ce * Cb ^ 18 + ce2 + 3 * 10 ^ 11 * cQ ≤ Cl :=
    leaf_final_hceil Msch g cm ce ce2 cQ CΛ Cb Cl cc hcc hMCb2 hClb
  have! hCbp59 : (0 : ℝ) ≤ (Cb : ℝ) ^ 59 := pow_nonneg (Nat.cast_nonneg _) _
  have! hCbp18 : (0 : ℝ) ≤ (Cb : ℝ) ^ 18 := pow_nonneg (Nat.cast_nonneg _) _
  have! hcm59 : 0 ≤ cm * (Cb : ℝ) ^ 59 := mul_nonneg hcmn hCbp59
  have! hce18 : 0 ≤ ce * (Cb : ℝ) ^ 18 := mul_nonneg hcen hCbp18
  have! hsT' : Real.sqrt (cT * B ^ 11 * G) ≤ Real.sqrt cT * B ^ 6 * G := by
    have! hc := Real.sq_sqrt hcT0
    have! h11 : B ^ 11 * G ≤ B ^ 12 * G ^ 2 := by
      have! this := pow_le_pow_right₀ hBB1 (show 11 ≤ 12 by norm_num)
      have! hG2 : G ≤ G ^ 2 := le_self_pow₀ hG1 (by norm_num)
      exact mul_le_mul this hG2 hGn0 (pow_nonneg hBn0 _)
    have! h1 : cT * B ^ 11 * G ≤ (Real.sqrt cT * B ^ 6 * G) ^ 2 := by
      calc cT * B ^ 11 * G = cT * (B ^ 11 * G) := by ring
        _ ≤ cT * (B ^ 12 * G ^ 2) := mul_le_mul_of_nonneg_left h11 hcT0
        _ = (Real.sqrt cT * B ^ 6 * G) ^ 2 := by rw [mul_pow, mul_pow, hc]; ring
    calc Real.sqrt (cT * B ^ 11 * G) ≤ Real.sqrt ((Real.sqrt cT * B ^ 6 * G) ^ 2) :=
          Real.sqrt_le_sqrt h1
      _ = Real.sqrt cT * B ^ 6 * G :=
          Real.sqrt_sq (mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (pow_nonneg hBn0 _)) hGn0)
  have! hB6G : 1 ≤ B ^ 6 * G := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hBB1) hG1
  have! hB2G6 : B ^ 2 * G ≤ B ^ 6 * G :=
    mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hBB1 (by norm_num)) hGn0
  have! hB59 : (0 : ℝ) ≤ B ^ 59 * G ^ 4 := mul_nonneg (pow_nonneg hBn0 _) (pow_nonneg hGn0 _)
  have! hCm : 196608 * B ^ 3 * (cT * B ^ 11 * G) + 83 * (1 + 81 * localFormUniformConstant κ *
      (30000 * B ^ 2 * G + Real.sqrt (cT * B ^ 11 * G))) * (1 + cT * B ^ 11 * G) ^ 3 +
      cMc * B ^ 59 * G ^ 2 ≤ cm * B ^ 59 * G ^ 4 :=
    leaf_final_hCm κ cT cMc cm t3 hcm B hBB1 G hG1 hL00 hcT0 hcMcn hBn0 hGn0 hsT' hB6G hB2G6
  have! hClm : cm * B ^ 59 * G ^ 4 ≤ Cl * u ^ Cl * Real.exp X ^ Cl :=
    leaf_final_hClm Msch g cm ce ce2 cQ CΛ Cb Cl cc hcc hMCb2 hClb u hu1 B hBdef X G hce2n hcQ0
      hX1 hGX hGn0 hceil hce18
  have! hErr : 6642 * localFormUniformConstant κ * (2 * (30000 * B ^ 2 * G) +
      Real.sqrt (cT * B ^ 11 * G)) ^ 3 * (288 * Real.exp (4 * (k : ℝ) ^ cc) * Real.sqrt δ * R) +
      cE ≤
      Cl * u ^ Cl * Real.exp X ^ Cl * (Real.exp (Cl * (k : ℝ) ^ cc) * (Real.sqrt δ +
        Real.exp (-kD))) * R + Cl * Real.exp (-(k : ℝ)) * R :=
    leaf_final_hErr κ Msch g cT cm ce ce2 cQ CΛ Cb Cl k cc hcc kD Mp V δ R S Iw U MV ε cE hce hR0
      hMCb2 hClb u hu1 B hBdef hBB1 X G hG1 hkcc1 hcT1 ι hcEsum hMVc hQeMV hL00 hce2n hcQ0 hX1 hGX
      hBn0 hGn0 hceil hcm59 hce18 hsT' hB6G hB2G6
  -- the explicit leaf bound
  have! hNp0 : (0 : ℝ) ≤ ((2 : ℝ) ^ famFuel) ^ 2 := by positivity
  have! hNpB : ((2 : ℝ) ^ famFuel) ^ 2 ≤ B ^ 2 := by
    have! this : (2 : ℝ) ^ famFuel ≤ B := by exact_mod_cast hLpB
    exact pow_le_pow_left₀ (by positivity) this 2
  have! hP0' : (0 : ℝ) ≤ ((P : ℝ) + 1) ^ 2 := by positivity
  have! hfc0 : 0 ≤ fc :=
    leaf_final_hfc0 P famFuel τ₃ hτ₃ fc hfc hP0'
  have! hfcB : fc ≤ 64 * B * ((P : ℝ) + 1) ^ 2 * τ₃ := by
    rw [hfc]
    have! h1 : 2 * (famFuel : ℝ) + 2 ≤ B := by
      have := hJmB; push_cast at this; linarith only [this]
    have! h0 : 0 ≤ ((P : ℝ) + 1) ^ 2 * (16 * τ₃ * 2 ^ 2) :=
      mul_nonneg hP0' (by linarith only [hτ₃])
    calc (2 * (famFuel : ℝ) + 2) * (((P : ℝ) + 1) ^ 2 * (16 * τ₃ * 2 ^ 2))
        ≤ B * (((P : ℝ) + 1) ^ 2 * (16 * τ₃ * 2 ^ 2)) := mul_le_mul_of_nonneg_right h1 h0
      _ = 64 * B * ((P : ℝ) + 1) ^ 2 * τ₃ := by ring
  have! htM0 : 0 ≤ cMc * B ^ 59 * G ^ 2 :=
    mul_nonneg (mul_nonneg hcMcn (pow_nonneg hBn0 _)) (pow_nonneg hGn0 _)
  refine (leaf_raw_le (tT := cT * B ^ 11 * G) (tC := 30000 * B ^ 2 * G)
    (tM := cMc * B ^ 59 * G ^ 2) (XE := 288 * Real.exp (4 * (k : ℝ) ^ cc) * Real.sqrt δ * R)
    (B := B) (P := (P : ℝ)) (η₀ := η₀) (τ₃ := τ₃) (nearS := nearS) (cE := cE)
    hT0 hT hcBd0 hcBd heBd0 heBd hNpB (by linarith only [hη₀]) le_rfl hfc0 hfcB hη0 hR0
    hL00 hBB1 hη₀.le hτ₃.le hME htM0 hcMtot).trans ?_
  have! hQ0 : 0 ≤ η ^ (1 / 1200 : ℝ) + η₀ + ((P : ℝ) + 1) ^ 2 * τ₃ := by
    have! h1 : 0 ≤ η ^ (1 / 1200 : ℝ) := Real.rpow_nonneg hη0 _
    have! h2 : 0 ≤ ((P : ℝ) + 1) ^ 2 * τ₃ := mul_nonneg hP0' hτ₃.le
    linarith only [h1, h2, hη₀]
  have! hM := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hCm.trans hClm) hQ0) hR0
  rw [hKb, heq'] at hNEAR
  unfold leafBnd
  rw [← hu, ← hX, add_assoc]
  refine le_trans (add_le_add (add_le_add hM hNEAR) hErr) (le_of_eq ?_)
  ring



private theorem leaf_final_stage_3 : LeafFinalStage3Statement := by
  classical
  intro κ q hq2 hq3 Nd Cg Msch g cT cL cK cMc cm ce ce2 cQ CΛ eΛ t3 Cb Cl k cc hcc hk2 kD P hP Nl
    Mp V famFuel hkF dB hdBk E ρ δ η η₀ τ₃ R hE0 hEk hρ hρ1 hρk hη0 hη₀ hτ₃ S hK1 hSd hSDm Iw Vl0
    TT hT0 hTTle U MV ε T2v hT2le cB eB cM4 cM3 nearS Γ Os hOs hΓle hnearS cE Ee fc hfc hcT hcMc
    hcm hce hce2 hcQ hk1 hR0 hCb20n hMCb2 hgr hClb u hu hu1 B hBdef hBB1 X hX hX0 G hGdef hG1
    hexpG hG0G hkcc1 hD1 hmaxNl hDm2 hKB hLpB hJmB hVl00 hT hcBd hcBd0 heBd heBd0 hcT1 Gq hGqG
    hVl0 hGq hcMtot E1 hE1 hE11 hMpE hVE1 hME ι Qe hcEsum hMVc hQeMV
  have! hL00 := localFormUniformConstant_nonneg κ
  have! hcT0 : 0 ≤ cT := by rw [hcT]; positivity
  have! hcMcn : 0 ≤ cMc :=
    leaf_final_hcMcn κ cL cK cMc hcMc
  have! hcmn : 0 ≤ cm := by
    rw [hcm]
    have! h1 : 0 ≤ 81 * localFormUniformConstant κ * (30000 + Real.sqrt cT) :=
      mul_nonneg (mul_nonneg (by norm_num) hL00) (by positivity)
    have! h2 : 0 ≤ (1 + cT) ^ 3 := by positivity
    have! h3 : 0 ≤ (1 + 81 * localFormUniformConstant κ * (30000 + Real.sqrt cT)) * (1 + cT) ^ 3 :=
      mul_nonneg (by linarith only [h1]) h2
    linarith only [hcT0, h3, hcMcn]
  have! hcen : 0 ≤ ce := by
    rw [hce]
    have! h1 := fourErrC_nonneg κ 3
    have! h2 := threeErrC_nonneg κ 3 1
    have! h3 : 0 ≤ 6642 * localFormUniformConstant κ * (60000 + Real.sqrt cT) ^ 3 * 288 :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hL00) (by positivity)) (by norm_num)
    have! h4 : 0 ≤ 324 * threeErrC κ 3 1 * Real.sqrt cT :=
      mul_nonneg (mul_nonneg (by norm_num) h2) (Real.sqrt_nonneg _)
    linarith only [h1, h2, h3, h4]
  have! hce2n : 0 ≤ ce2 := by
    rw [hce2]
    have! h1 := fourKC_nonneg κ 3
    have! h2 := entryCU_nonneg' κ 3 1
    have h3 := K1c_pos
    have! h4 : 0 ≤ K1c * (2 * fourKC κ 3 * 12 ^ 4) :=
      mul_nonneg h3.le (mul_nonneg (mul_nonneg (by norm_num) h1) (by norm_num))
    have! h5 : 0 ≤ K1c * (8 * entryCU κ 3 1 * 2 ^ (1 + 4) * 12 ^ 3) :=
      mul_nonneg h3.le (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) h2) (by norm_num))
        (by norm_num))
    linarith only [h4, h5]
  -- the near bands: the `k`-polynomial factors
  set! Nb : ℕ := Nat.log 2 S.K + 1 with hNb
  rewrite [← hNb] at hΓle hnearS
  set! n : ℝ := (Nb : ℝ) with hn
  rewrite [← hn] at hΓle
  have! hn1 : 1 ≤ n := by
    rw [hn, hNb]; push_cast
    have! this := Nat.cast_nonneg (α := ℝ) (Nat.log 2 S.K)
    linarith only [this]
  set! Cjg : ℝ := (((2 * famFuel + 2 : ℕ) : ℝ) + 1) ^ 2 * Real.exp (2 * (1024 * (cc + 1) *
    (1024 * (cc + 1) + cc + 7) * (1 + Real.log (2 * (k : ℝ))) ^ 2)) with hCjg
  rewrite [← hCjg] at hΓle
  have! hCjg1 : 1 ≤ Cjg :=
    leaf_final_hCjg1 k cc famFuel hCjg
  set! G0e := Real.exp ((4096 * (cc + 1) * (1024 * (cc + 1) + cc + 7) + cc ^ 2 + 3) *
    (1 + Real.log (2 * (k : ℝ))) ^ 2) with hG0e
  rewrite [← hG0e] at hTTle hT2le hG0G hΓle
  have! hG0e1 : 1 ≤ G0e := Real.one_le_exp (by positivity)
  set! W := G0e + Vl0 + E + 1 with hWdef
  rewrite [← hWdef] at hΓle
  have! hW1 : 1 ≤ W := by linarith only [hG0e1, hVl00, hE0]
  -- the `k`-polynomial factors of the near bands: `Q_k ≤ c_Q k^{8c+4} G²`
  have! hkcc' : (k : ℝ) ^ cc ≤ (k : ℝ) ^ (2 * cc + 1) := pow_le_pow_right₀ hk1 (by omega)
  have! hk2cc : (1 : ℝ) ≤ (k : ℝ) ^ (2 * cc + 1) := one_le_pow₀ hk1
  have! hJmk : ((2 * famFuel + 2 : ℕ) : ℝ) ≤ cc * k := by
    have! hlk : Real.log k + 1 ≤ k := by
      have! this := Real.log_le_sub_one_of_pos (show (0 : ℝ) < k by linarith only [hk1])
      linarith only [this]
    have! this := mul_le_mul_of_nonneg_left hlk (Nat.cast_nonneg (α := ℝ) cc)
    linarith only [hkF, this]
  have! hcc1 : (1 : ℝ) ≤ cc := by exact_mod_cast hcc
  have! hLpk : (2 : ℝ) ^ famFuel ≤ 3 ^ cc * (k : ℝ) ^ cc := by
    have! this := two_pow_le_of_fuel hk1 hkF; rwa [mul_pow] at this
  have! hOsk : (Os.card : ℝ) ≤ 80 * 9 ^ cc * cc * (k : ℝ) ^ (2 * cc + 1) :=
    leaf_final_hOsk k cc famFuel Os hOs hJmk hLpk
  have! hOs0' : (0 : ℝ) ≤ Os.card := Nat.cast_nonneg _
  have! hhull : hullCutConstant (ρ / 64 / 2) ≤ 65536 * (k : ℝ) ^ (2 * cc) :=
    leaf_final_hhull k cc hk2 ρ hρ hρk
  set! Yn : ℝ := (Os.card : ℝ) * (Mp : ℝ) * V with hYn
  rewrite [← hYn] at hnearS
  have! hYn0 : 0 ≤ Yn := by
    rw [hYn]; exact mul_nonneg (mul_nonneg hOs0' (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  have! hlogY : 1 + Real.log (2 + Yn) ≤ (8 + 80 * 9 ^ cc * cc) * (k : ℝ) ^ (2 * cc + 1) :=
    leaf_final_hlogY k cc Mp V Os E1 hE1 hE11 hMpE hVE1 hkcc' hk2cc hOsk hOs0' hYn hYn0
  have! hCjgk : Cjg ≤ 4 * cc ^ 2 * (k : ℝ) ^ 2 * G :=
    leaf_final_hCjgk g k cc famFuel hk1 hgr X hX G hexpG hCjg hJmk hcc1
  have! hWk : W ≤ 170000000 * (k : ℝ) ^ (2 * cc) * G :=
    leaf_final_hWk k cc Nl dB hdBk E hEk S hSd hSDm Vl0 hk1 G hG1 hkcc1 hD1 hmaxNl hDm2 hGqG hVl0
      hGq hG0G hWdef
  -- the bound `Q_k ≤ c_Q e^{(8c + 4 + 2g) X}`
  set! Qk := hullCutConstant (ρ / 64 / 2) * (1 + Real.log (2 + Yn)) * Os.card * Cjg * W with hQkdef
  have! hcQ0 : 0 ≤ cQ := by rw [hcQ]; positivity
  have! hQk : Qk ≤ cQ * Real.exp X ^ (8 * cc + 4 + 2 * g) :=
    leaf_final_hQk g cQ k cc hcc hk2 Mp V famFuel E ρ hρ hρ1 Vl0 Os hcQ hk1 X hX G hGdef hG1 hCjg1
      hW1 hOsk hhull hYn0 hlogY hCjgk hWk hQkdef hcQ0
  -- the near bands in the final form
  set! eq' := 2 * (q - 2) / (q - 1) with heq'
  rewrite [← heq'] at hnearS
  have! he0 : 0 ≤ eq' := by rw [heq']; apply div_nonneg <;> linarith only [hq2]
  set! Kb : ℝ := Cl * u ^ Cl with hKb
  have! hClCb : (Cb : ℝ) ≤ Cl := by
    have! this : Cb ≤ Cl := by omega
    exact_mod_cast this
  have! hBKb : B ≤ Kb := by
    rw [hBdef, hKb]
    exact mul_le_mul hClCb (pow_le_pow_right₀ hu1 (by omega)) (by positivity)
      (Nat.cast_nonneg _)
  have! hKKb : (S.K : ℝ) ≤ Kb := hKB.trans hBKb
  have! hK0' : (0 : ℝ) ≤ S.K := Nat.cast_nonneg _
  have! hKp : ((S.K : ℝ) + 2) ^ eq' ≤ (Kb + 2) ^ eq' :=
    Real.rpow_le_rpow (by positivity) (by linarith only [hKKb]) he0
  have! hlamb : (2 + Real.log ((S.K : ℝ) + 2)) ^ 6 ≤ (2 + Real.log (Kb + 2)) ^ 6 := by
    have! h1 := Real.log_le_log (by positivity) (show (S.K : ℝ) + 2 ≤ Kb + 2 by
      linarith only [hKKb])
    have! h0 : 0 ≤ 2 + Real.log ((S.K : ℝ) + 2) := by
      have! this := Real.log_nonneg (show (1 : ℝ) ≤ (S.K : ℝ) + 2 by linarith only [hK0'])
      linarith only [this]
    exact pow_le_pow_left₀ h0 (by linarith only [h1]) 6
  expose_names
  exact @leaf_final_stage_4 κ q hq2 hq3 Nd Msch g cT cMc cm ce ce2 cQ CΛ t3 Cb Cl k cc hcc kD P hP
    Mp V famFuel E ρ δ η η₀ τ₃ R hρ hρ1 hη0 hη₀ hτ₃ S hK1 Iw Vl0 TT hT0 U MV ε cB eB cM4 cM3 nearS
    Γ Os cE Ee fc hfc hcm hce hR0 hCb20n hMCb2 hClb u hu hu1 B hBdef hBB1 X hX hX0 G hGdef hG1
    hkcc1 hLpB hJmB hT hcBd hcBd0 heBd heBd0 hcT1 hcMtot hME ι hcEsum hMVc hQeMV hL00 hcT0 hcMcn
    hcmn hcen hce2n hNb hCjg1 hΓle hW1 hYn0 hQkdef hcQ0 hQk hnearS heq' hKb hK0' hKp hlamb



private theorem leaf_final_stage_2 : LeafFinalStage2Statement := by
  classical
  intro κ q hq2 hq3 Nd Cg Msch g cT cL cK cMc cm ce ce2 cQ CΛ eΛ t3 Cb Cl k cc hcc hk2 kD P hP cb
    Nl Mp V hcb hNl4 famFuel hkF dB hdB1 hdBk E ρ δ η η₀ τ₃ R hE0 hEk hρ hρ1 hρk hδ hδ8 hη0 hη₀
    hτ₃ hRl0 S hD2 hH2 hK1 hSd hSDm hexpD Iw hIw Vl0 hVl0 TT hT0 hTTle U hUdef MV hMV ε hεdef Mt
    hMt T2v hT2le cB eB cM4 cM3 hcM4 hcM3 nearS Γ Os hOs hΓle hnearS cE hcEsum Ee hEe0 hEeb fc hfc
    hcT hcK hcMc hcm hce hce2 hcQ hk1 hR0 hCb20n hMCb2 hgr hClb u hu hu1 B hBdef hBB2 hBB1 X hX
    hX0 G hGdef hG1 hexpG hG0G hGqG hNl0 hcbexp hNlexp hMpexp hVexp hkcc1 hD0 hD1 hmaxNl hDm2 hKB
    hJB hlHB hlDB hdmB hIwB hLpB hJmB hVl00 hVl0B hT hρ1' hcBd hcBd0 heBd heBd0 hU16 hU0 hMV0 hε0
    hThrC hcT1 hL0' hLB hcL0
  set! Gq := Real.exp ((6144 * (cc + 1) * (1024 * (cc + 1) + cc + 7) + 4) *
    (1 + Real.log (2 * (k : ℝ))) ^ 2) with hGq
  rewrite [← hGq] at hVl0 hMt hGqG
  set! Ts := Finset.range (Nat.log 2 ⌊S.Dstar⌋₊ + 1) ×ˢ Finset.range (Nat.log 2 ⌊S.Dstar⌋₊ + 1)
    with hTsdef
  rewrite [← hTsdef] at hMt
  have! hcardTs : (Ts.card : ℝ) ≤ (3 * B) ^ 2 := by
    rw [hTsdef, Finset.card_product, Finset.card_range]
    push_cast
    have! h := natLog_floor_le hD1
    have! h1 : (Nat.log 2 ⌊S.Dstar⌋₊ : ℝ) + 1 ≤ 3 * B := by linarith only [h, hlDB, hBB1]
    have! h0 : (0 : ℝ) ≤ (Nat.log 2 ⌊S.Dstar⌋₊ : ℝ) + 1 := by positivity
    calc ((Nat.log 2 ⌊S.Dstar⌋₊ : ℝ) + 1) * ((Nat.log 2 ⌊S.Dstar⌋₊ : ℝ) + 1)
        ≤ (3 * B) * (3 * B) := mul_le_mul h1 h1 h0 (by linarith only [hBB1])
      _ = (3 * B) ^ 2 := by ring
  have! hcardThr : ((dyThr ε U S.Dstar).card : ℝ) ≤ cL * B + 2 := by
    have h := hThrC
    rw [← Real.logb_div hU0.ne' hε0.ne'] at h
    linarith only [h, hLB]
  have! hMtB : Mt ≤ 7000000000 * B ^ 7 * G * (cL * B + 2) :=
    leaf_final_hMtB cL k cc ρ hρ S Vl0 U ε Mt B hBB1 G hG1 hKB hJB hVl00 hVl0B hρ1' hcL0 hGqG hMt
      hcardTs hcardThr
  have! hMt0 : 0 ≤ Mt := by
    rw [hMt]; have : 0 ≤ Gq := by rw [hGq]; positivity
    exact div_nonneg (mul_nonneg (by positivity) (Nat.cast_nonneg _)) hρ.le
  set! Kc := max (max 1 Mt) TT with hKcdef
  rewrite [← hKcdef] at hcM4 hcM3
  have! hKc1 : 1 ≤ Kc := le_trans (le_max_left _ _) (le_max_left _ _)
  have! hKcB : Kc ≤ cK * B ^ 12 * G :=
    leaf_final_hKcB cT cL cK TT hT0 Mt hcK B hBB1 G hG1 hT hcT1 hcL0 hMtB hMt0
  -- the core bounds
  have! hH1' : (1 : ℝ) ≤ S.H := by linarith only [hH2]
  have! hcM4' : cM4 ≤ C4c κ * B ^ 30 * (cL * B) ^ 4 * Kc ^ 2 := by
    rw [hcM4]
    exact coreM4F_le κ S hBB2 hdmB hD1 hH1' hlDB hlHB hJB hL0' hLB hKc1
  have! hcM3' : cM3 ≤ 4 * (C3c κ * B ^ 30 * B * (cL * B) ^ 4 * Kc ^ 2) := by
    rw [hcM3]
    calc ∑ l, coreM3F κ S (1 / 1024) 3 1 Iw U ε Kc l
        ≤ ∑ _l : Fin 4, C3c κ * B ^ 30 * B * (cL * B) ^ 4 * Kc ^ 2 :=
          Finset.sum_le_sum fun l _ =>
            coreM3F_le κ S Iw l hBB2 hdmB hD1 hH1' hlDB hlHB hJB hL0' hLB hKc1 hIwB
      _ = _ := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast; ring
  have! hcMtot : cM4 + cM3 ≤ cMc * B ^ 59 * G ^ 2 :=
    leaf_final_hcMtot κ cL cK cMc TT Mt cM4 cM3 hcMc B hBB1 G hKc1 hKcB hcM4' hcM3'
  -- the physical errors: `√(4M) √E_e ≤ 288 e^{4 k^c} √δ |R|`
  obtain ⟨E1, hE1⟩ : ∃ x : ℝ, x = Real.exp ((k : ℝ) ^ cc) := ⟨_, rfl⟩
  have! hE11 : 1 ≤ E1 := by rw [hE1]; exact Real.one_le_exp (by positivity)
  have! hMpE : (Mp : ℝ) ≤ E1 := by rw [hE1]; exact hMpexp
  have! hVE1 : (V : ℝ) ≤ 5 * E1 := by rw [hE1]; exact hVexp
  have! hcbE : cb ≤ E1 := by rw [hE1]; linarith only [hcbexp, hcb]
  have! hNlE : Nl ≤ E1 := by rw [hE1]; exact hNlexp
  have! hdBE : (dB : ℝ) ≤ E1 := by
    rw [hE1]; exact hdBk.trans ((Real.add_one_le_exp _).trans' (by linarith only []))
  have! hME : Real.sqrt (4 * (((Mp * V : ℕ) : ℝ) * R)) *
      Real.sqrt Ee ≤ 288 * Real.exp (4 * (k : ℝ) ^ cc) * Real.sqrt δ * R :=
    leaf_final_hME κ k cc cb Nl Mp V hcb hNl4 dB hdB1 δ R hδ hδ8 hRl0 S Iw U ε cE hcEsum Ee hEe0
      hEeb hNl0 E1 hE1 hE11 hMpE hVE1 hcbE hNlE hdBE
  have! hDinv : S.Dstar⁻¹ ≤ Real.exp (-kD) := by
    rw [Real.exp_neg]; exact inv_anti₀ (Real.exp_pos _) hexpD
  obtain ⟨ι, hι⟩ : ∃ x : ℝ, x = (S.Dstar ^ 100)⁻¹ * S.Dstar ^ 10 := ⟨_, rfl⟩
  rw [← hι] at hcEsum
  have! hι0 : 0 ≤ ι := by rw [hι]; positivity
  have! hιD : ι ≤ S.Dstar⁻¹ := by
    rw [hι, show S.Dstar ^ 100 = S.Dstar ^ 90 * S.Dstar ^ 10 by ring, mul_inv, mul_assoc,
      inv_mul_cancel₀ (pow_ne_zero _ hD0.ne'), mul_one]
    exact inv_anti₀ hD0 (le_self_pow₀ hD1 (by norm_num))
  have! hιD2 : ι * S.Dstar ^ 2 ≤ S.Dstar⁻¹ := by
    rw [hι, show S.Dstar ^ 100 = S.Dstar ^ 88 * S.Dstar ^ 12 by ring, mul_inv, mul_assoc,
      mul_assoc, ← pow_add, inv_mul_cancel₀ (pow_ne_zero _ hD0.ne'), mul_one]
    exact inv_anti₀ hD0 (le_self_pow₀ hD1 (by norm_num))
  set! Qe : ℝ := 16 * fourErrC κ 3 * ι + K1c * (2 * fourKC κ 3 * 12 ^ 4 * ε * U ^ 3 *
      S.Dstar ^ 4) + 4 * (81 * threeErrC κ 3 1 * ι * U + K1c * (8 * entryCU κ 3 1 *
        2 ^ (1 + 4) * 12 ^ 3 * ε * U ^ 3 * (S.Dstar ^ 3 * (Iw + 1)))) with hQe
  rewrite [← hQe] at hcEsum
  have! hQe0 : 0 ≤ Qe :=
    leaf_final_hQe0 κ S hD2 Iw U ε hU16 hε0 ι hι0 hQe
  -- the error constant `Q_e M V`
  have! hMVc : (((Mp * V : ℕ) : ℝ)) = MV := by rw [hMV]; push_cast; ring
  have! hMVE : MV ≤ 5 * E1 ^ 2 := by
    rw [hMV]
    have! this := mul_le_mul hMpE hVE1 (Nat.cast_nonneg _) (by linarith only [hE11])
    nlinarith only [this]
  have! hε4 : ε * U ^ 3 * S.Dstar ^ 4 * MV ≤ Real.exp (-(k : ℝ)) :=
    leaf_final_hε4 k S hD2 U MV ε hεdef hD1 hU16 hMV0
  have! hIwD : (Iw : ℝ) + 1 ≤ 501 * S.Dstar ^ 2 := by
    have! h1 : (Iw : ℝ) ≤ Real.logb 2 (S.Dstar ^ 250) := by
      rw [hIw]; exact Nat.floor_le (Real.logb_nonneg (by norm_num) (one_le_pow₀ hD1))
    have! h2 : Real.logb 2 (S.Dstar ^ 250) ≤ 500 * Real.log S.Dstar := by
      have! this := logb_two_le_two_log (one_le_pow₀ hD1 : (1 : ℝ) ≤ S.Dstar ^ 250)
      rw [Real.log_pow] at this; push_cast at this; linarith only [this]
    have! h3 : Real.log S.Dstar ≤ S.Dstar := by
      have! this := Real.log_le_sub_one_of_pos hD0; linarith only [this]
    have! h4 : S.Dstar ≤ S.Dstar ^ 2 := le_self_pow₀ hD1 (by norm_num)
    have! h5 : (1 : ℝ) ≤ S.Dstar ^ 2 := one_le_pow₀ hD1
    linarith only [h1, h2, h3, h4, h5]
  have! hε3 : ε * U ^ 3 * (S.Dstar ^ 3 * (Iw + 1)) * MV ≤ 501 * Real.exp (-(k : ℝ)) :=
    leaf_final_hε3 k S hD2 Iw U MV ε hεdef hU16 hMV0 hIwD
  have! hE14 : 4 ≤ E1 :=
    leaf_final_hE14 k cc hcc hk2 hk1 E1 hE1
  have! hιU : ι * U ≤ S.Dstar⁻¹ * (2 * (cb + 2) + Real.sqrt TT) :=
    leaf_final_hιU cb hcb S TT U hUdef ι hι0 hιD hιD2
  have! hsTT : Real.sqrt TT ≤ Real.sqrt cT * B ^ 6 * G :=
    leaf_final_hsTT cT TT B hBB1 G hG1 hT hcT1
  have! hQeMV : Qe * MV ≤ 5 * (16 * fourErrC κ 3 + 648 * threeErrC κ 3 1 +
      324 * threeErrC κ 3 1 * Real.sqrt cT) * Real.exp (3 * (k : ℝ) ^ cc) * B ^ 6 * G *
        Real.exp (-kD) + ce2 * Real.exp (-(k : ℝ)) :=
    leaf_final_hQeMV κ cT ce2 k cc kD cb hcb S Iw TT U MV ε hce2 B hBB2 hBB1 G hG1 hcbexp hMV0 E1
      hE1 hE11 hcbE hDinv ι hιD hQe hMVE hε4 hε3 hE14 hιU hsTT
  -- nonnegativity of the constants
  expose_names
  exact @leaf_final_stage_3 κ q hq2 hq3 Nd Cg Msch g cT cL cK cMc cm ce ce2 cQ CΛ eΛ t3 Cb Cl k cc
    hcc hk2 kD P hP Nl Mp V famFuel hkF dB hdBk E ρ δ η η₀ τ₃ R hE0 hEk hρ hρ1 hρk hη0 hη₀ hτ₃ S
    hK1 hSd hSDm Iw Vl0 TT hT0 hTTle U MV ε T2v hT2le cB eB cM4 cM3 nearS Γ Os hOs hΓle hnearS cE
    Ee fc hfc hcT hcMc hcm hce hce2 hcQ hk1 hR0 hCb20n hMCb2 hgr hClb u hu hu1 B hBdef hBB1 X hX
    hX0 G hGdef hG1 hexpG hG0G hkcc1 hD1 hmaxNl hDm2 hKB hLpB hJmB hVl00 hT hcBd hcBd0 heBd heBd0
    hcT1 hGqG hVl0 hGq hcMtot E1 hE1 hE11 hMpE hVE1 hME ι hcEsum hMVc hQeMV



private theorem leaf_final_stage_1 : LeafFinalStage1Statement := by
  classical
  intro κ q hq2 hq3 Nd Cg Msch g cT cL cK cMc cm ce ce2 cQ CΛ eΛ t3 Cb Cl k cc hcc hk2 kD P hP cb
    Nl Mp V hcb hNl4 hkb famFuel hkF dB hdB1 hdBk E ρ δ η η₀ τ₃ R hE0 hEk hρ hρ1 hρk hδ hδ8 hη0
    hη₀ hτ₃ hRl0 S hD2 hH2 hK1 hSd hSDm hexpD Iw hIw Vl0 hVl0 TT hT0 hTTle U hUdef MV hMV ε hεdef
    Mt hMt T2v hT2le B0 cB eB hB0 hcBdef heBdef cM4 cM3 hcM4 hcM3 nearS Γ Os hOs hΓle hnearS cE
    hcEsum Ee hEe0 hEeb fc hfc hcT hcL hcK hcMc hcm hce hce2 hcQ hk1 hR0 hCb20n hccCb hCgCb hMCb2
    h3Cb hgr hClb hkcc0 u hlD hu hu1 B hBdef hpowB hCb20 hBB2 hBB1 hkcc X hX hX0 hX4 G hGdef hG1
    hexpG hG0G hGqG hNl0 hcbexp hNlexp hMpexp hVexp hkcc1 hD0 hD1 hlD0 hmaxNl hDm2 hKB hJB hlHB
    hlDB
  have! hdmB : (S.dmax : ℝ) + 5 ≤ B := by
    rw [hSd]; push_cast
    have! this := hkcc 9 (by norm_num) (by linarith only [hCb20])
    linarith only [this, hdBk, hkcc1]
  have! hDmB : Real.log (2 * S.Dm) ≤ B := by
    rw [hSDm, Real.log_mul (by norm_num) (by positivity)]
    have! this := hkcc 2 (by norm_num) (by linarith only [hCb20])
    have! hl2 : Real.log 2 ≤ 1 := by linarith only [Real.log_two_lt_d9]
    linarith only [this, hl2, hmaxNl, hkcc1]
  have! hIwB : (Iw : ℝ) + 1 ≤ B :=
    leaf_final_hIwB Cg Cb S Iw hIw hCgCb u hlD hu1 B hpowB hD1 hlD0
  have! hkB' : (k : ℝ) ≤ B := by
    have! h1 := hkcc 1 (by norm_num) (by linarith only [hCb20])
    linarith only [h1, hkcc0]
  have! hEB : E ≤ B := by
    have! this := hkcc 1 (by norm_num) (by linarith only [hCb20]); linarith only [this, hEk]
  have! hρB : ρ⁻¹ ≤ B := by
    have! this := hkcc 1 (by norm_num) (by linarith only [hCb20]); linarith only [this, hρk]
  have! hLpB : ((2 ^ famFuel : ℕ) : ℝ) ≤ B := by
    push_cast
    have! h1 := two_pow_le_of_fuel hk1 hkF
    rw [mul_pow] at h1
    refine h1.trans (hkcc _ (by positivity) ?_)
    have! this : (3 : ℝ) ^ cc = ((3 ^ cc : ℕ) : ℝ) := by push_cast; ring
    rw [this]
    exact_mod_cast h3Cb
  have! hJmB : ((2 * famFuel + 2 : ℕ) : ℝ) + 1 ≤ B :=
    leaf_final_hJmB Cb k cc hcc famFuel hkF hk1 hccCb hkcc0 B hkcc hkcc1
  -- the linear sides and the side cap
  have! hVl00 : 0 ≤ Vl0 := by rw [hVl0]; positivity
  have! hVl0B : Vl0 ≤ 14000000 * B ^ 2 * G :=
    leaf_final_hVl0B k cc S Vl0 hVl0 B hBB1 G hG1 hGqG hD1 hDm2 hdmB hDmB
  have! hT : TT ≤ cT * B ^ 11 * G :=
    leaf_final_hT κ cT k cc famFuel E ρ hE0 hρ S hK1 Vl0 TT hTTle hcT B hBB2 hBB1 G hG1 hG0G hKB
      hEB hρB hLpB hJmB hVl00 hVl0B
  -- the two-side cap and the core and error sizes
  have! hρ1' : 1 / ρ ≤ B := by rw [one_div]; exact hρB
  have! hT2 : T2v ≤ 60000000 * B ^ 4 * G :=
    leaf_final_hT2 k cc ρ hρ S Vl0 T2v hT2le B hBB2 hBB1 G hG1 hG0G hKB hVl00 hVl0B hρ1'
  have! hsT2 : Real.sqrt T2v ≤ 7746 * B ^ 2 * G :=
    leaf_final_hsT2 T2v B G hG1 hT2
  have! hs5 : Real.sqrt 5 ≤ 9 / 4 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have! hBG1 : (1 : ℝ) ≤ B ^ 2 * G := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hBB1) hG1
  have! hcBd : cB ≤ 30000 * B ^ 2 * G := by
    rw [hcBdef, hB0]; unfold coreBd
    have! h0 := Real.sqrt_nonneg T2v
    have! h5 : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
    nlinarith only [hs5, hsT2, h0, h5, hBG1]
  have! hcBd0 : 0 ≤ cB := by rw [hcBdef, hB0]; unfold coreBd; positivity
  have! heBd : eB ≤ 30000 * B ^ 2 * G := by
    rw [heBdef, hB0]; unfold errBd
    have! h0 := Real.sqrt_nonneg T2v
    have! h5 : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
    nlinarith only [hs5, hsT2, h0, h5, hBG1]
  have! heBd0 : 0 ≤ eB := by rw [heBdef, hB0]; unfold errBd; positivity
  -- the cap `U` and the accuracy `ε`
  have! hU4 : 2 * (cb + 2) * S.Dstar ^ 2 ≤ U := hUdef ▸ le_max_left _ _
  have! hU16 : 16 ≤ U := by
    refine le_trans ?_ hU4
    have! h2 : (2 : ℝ) ^ 2 ≤ S.Dstar ^ 2 := pow_le_pow_left₀ (by norm_num) hD2 2
    nlinarith only [h2, hcb]
  have! hU0 : 0 < U := by linarith only [hU16]
  have! hMV0 : 0 ≤ MV := by rw [hMV]; positivity
  have! hε0 : 0 < ε := by rw [hεdef]; exact inv_pos.mpr (by positivity)
  have! hε1 : ε ≤ 1 := by
    rw [hεdef]
    refine inv_le_one_of_one_le₀ ?_
    have! h1 : (1 : ℝ) ≤ U ^ 3 := one_le_pow₀ (le_trans (by norm_num) hU16)
    have! h2 : (1 : ℝ) ≤ S.Dstar ^ 5 := one_le_pow₀ hD1
    have! h3 : (1 : ℝ) ≤ Real.exp k := Real.one_le_exp (Nat.cast_nonneg _)
    have! h4 : (1 : ℝ) ≤ 1 + MV := by linarith only [hMV0]
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le h1 h2) h3) h4
  have! hεU : ε ≤ U := le_trans hε1 (le_trans (by norm_num) hU16)
  have! hUD : S.Dstar⁻¹ ≤ U := le_trans (inv_le_one_of_one_le₀ hD1) (le_trans (by norm_num) hU16)
  obtain ⟨hThr0, hThrD, hThrM, hThrC⟩ := dyThr_spec hε0 hεU hUD
  -- the dyadic thresholds: `log₂ (U/ε) + 1 ≤ c_L B`
  have hTT1 : TT ≤ cT * B ^ 11 * G := hT
  have! hcT1 : 1 ≤ cT := by
    rw [hcT]
    have! this := localFormUniformConstant_nonneg κ
    have! this : (1 : ℝ) ≤ (1 + localFormUniformConstant κ) ^ 2 :=
      one_le_pow₀ (by linarith only [this])
    nlinarith only [this]
  have! hBGT : 1 ≤ cT * B ^ 11 * G :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hcT1 (one_le_pow₀ hBB1)) hG1
  have! hUε : U / ε = U ^ 4 * S.Dstar ^ 5 * Real.exp k * (1 + MV) := by
    rw [hεdef, div_inv_eq_mul]; ring
  have! hUε1 : 1 ≤ U / ε := by
    rw [hUε]
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by linarith only [hU16])) (one_le_pow₀ hD1))
      (Real.one_le_exp (Nat.cast_nonneg _))) (by linarith only [hMV0])
  have! hlogU : Real.log U ≤ (17 + 4 * g + Real.log cT) * B :=
    leaf_final_hlogU g cT Cb k cc cb hcb hkb S hD2 TT hT0 U hUdef B hCb20 hBB2 hBB1 hkcc X hX0 hX4
      G hGdef hG1 hD1 hlDB hkB' hU0 hTT1 hcT1 hBGT
  have! hlogMV : Real.log (1 + MV) ≤ 4 * B :=
    leaf_final_hlogMV Cb k cc Mp V MV hMV B hCb20 hBB1 hkcc hMpexp hVexp hMV0
  have! hlogUε : Real.log (U / ε) ≤ (78 + 16 * g + 4 * Real.log cT) * B :=
    leaf_final_hlogUε g cT k S hD2 U MV ε B hBB2 hBB1 hlDB hkB' hU16 hMV0 hcT1 hUε hlogU hlogMV
  have! hL0' : 0 ≤ Real.logb 2 (U / ε) + 1 := by
    have! this := Real.logb_nonneg (b := 2) (by norm_num) hUε1; linarith only [this]
  have! hLB : Real.logb 2 (U / ε) + 1 ≤ cL * B := by
    have! h1 := logb_two_le_two_log hUε1
    have! hlc : 0 ≤ Real.log cT := Real.log_nonneg hcT1
    rw [hcL]
    nlinarith only [h1, hlogUε, hBB1, hlc]
  -- the top-count cap `M_t` and the path cap `K_c`
  have! hcL0 : 0 ≤ cL :=
    leaf_final_hcL0 g cT cL hcL hcT1
  expose_names
  exact @leaf_final_stage_2 κ q hq2 hq3 Nd Cg Msch g cT cL cK cMc cm ce ce2 cQ CΛ eΛ t3 Cb Cl k cc
    hcc hk2 kD P hP cb Nl Mp V hcb hNl4 famFuel hkF dB hdB1 hdBk E ρ δ η η₀ τ₃ R hE0 hEk hρ hρ1
    hρk hδ hδ8 hη0 hη₀ hτ₃ hRl0 S hD2 hH2 hK1 hSd hSDm hexpD Iw hIw Vl0 hVl0 TT hT0 hTTle U hUdef
    MV hMV ε hεdef Mt hMt T2v hT2le cB eB cM4 cM3 hcM4 hcM3 nearS Γ Os hOs hΓle hnearS cE hcEsum
    Ee hEe0 hEeb fc hfc hcT hcK hcMc hcm hce hce2 hcQ hk1 hR0 hCb20n hMCb2 hgr hClb u hu hu1 B
    hBdef hBB2 hBB1 X hX hX0 G hGdef hG1 hexpG hG0G hGqG hNl0 hcbexp hNlexp hMpexp hVexp hkcc1 hD0
    hD1 hmaxNl hDm2 hKB hJB hlHB hlDB hdmB hIwB hLpB hJmB hVl00 hVl0B hT hρ1' hcBd hcBd0 heBd
    heBd0 hU16 hU0 hMV0 hε0 hThrC hcT1 hL0' hLB hcL0


/-- The arithmetic of the explicit leaf bound (`eq:before-absorption` on one leaf): the right side
of `leaf_bound` (in the shape of `leaf_raw_le`), with the side caps, core bounds, near bands, core
errors and physical errors of a leaf given by their explicit forms or bounds, is at most
`leafBnd`. All sizes are reduced to the size parameter `B = C_b (k_D P)^{C_b}` and the unit
`G = e^{g (1 + log 2k)²}`. -/
theorem leaf_final (κ : LocalKernelClass) {q : ℝ} (hq2 : 2 < q) (hq3 : q < 3) (Nd : ℕ)
    {Cg : ℕ} {Msch : ℝ} (hMsch : 0 < Msch) {g : ℕ} {cT cL cK cMc cm ce ce2 cQ : ℝ}
    {CΛ eΛ CM1 t3 Cb Cl : ℕ} {k cc : ℕ}
    (hconst : g = 8192 * (cc + 1) * (1024 * (cc + 1) + cc + 7) + cc ^ 2 + 8 ∧
      cT = 10 ^ 22 * (1 + localFormUniformConstant κ) ^ 2 ∧
      cL = 159 + 32 * g + 8 * Real.log cT ∧
      cK = (1 + 7 * 10 ^ 9 + cT) * (cL + 2) ∧
      cMc = (C4c κ + 4 * C3c κ) * cL ^ 4 * cK ^ 2 ∧
      cm = 196608 * cT + 83 * (1 + 81 * localFormUniformConstant κ *
        (30000 + Real.sqrt cT)) * (1 + cT) ^ 3 + cMc ∧
      ce = 6642 * localFormUniformConstant κ * (60000 + Real.sqrt cT) ^ 3 * 288 +
        9 * (16 * fourErrC κ 3 + 648 * threeErrC κ 3 1 + 324 * threeErrC κ 3 1 * Real.sqrt cT) ∧
      ce2 = K1c * (2 * fourKC κ 3 * 12 ^ 4) +
        4 * (K1c * (8 * entryCU κ 3 1 * 2 ^ (1 + 4) * 12 ^ 3)) * 501 ∧
      cQ = 65536 * (8 + 80 * 9 ^ cc * cc) * (80 * 9 ^ cc * cc) * (4 * cc ^ 2) * (17 * 10 ^ 7) ∧
      CΛ = 2 * Cg + 12 ∧ eΛ = Cg + 3 * cc ∧ CM1 = (⌈Msch⌉₊ + 1) * CΛ ^ 16 ∧ t3 = 3 ^ cc ∧
      Cb = CM1 + 501 * Cg + t3 + 2 * cc + 20 + 16 * eΛ ∧
      Cl = ⌈cm * Cb ^ 59 + ce * Cb ^ 18 + ce2 + 3 * 10 ^ 11 * cQ⌉₊ + 59 * Cb + 4 * g + 8 * cc + 8)
    (hcc : 1 ≤ cc) (hk2 : (2 : ℝ) ≤ k) {kD : ℝ} (hkD : (k : ℝ) ^ cc ≤ kD) {P : ℕ} (hP : 1 ≤ P)
    -- the budget and the counts
    {cb Nl : ℝ} {Mp V : ℕ} (hcb : 2 ≤ cb) (hNl4 : 4 ≤ Nl)
    (hkB : Real.log (2 * (8 * cb + (1 + Mp) * Nl)) ≤ (k : ℝ) ^ cc)
    (hkb : Real.log (2 * cb) ≤ (k : ℝ) ^ cc) (hVle : (V : ℝ) ≤ 8 * cb + 1)
    {famFuel : ℕ} (hkF : ((2 * famFuel + 2 : ℕ) : ℝ) ≤ cc * (Real.log k + 1))
    {dB : ℕ} (hdB1 : 1 ≤ dB) (hdBk : (dB : ℝ) ≤ (k : ℝ) ^ cc)
    {E ρ δ η η₀ τ₃ R : ℝ} (hE0 : 0 ≤ E) (hEk : E ≤ (k : ℝ) ^ cc) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (hρk : ρ⁻¹ ≤ (k : ℝ) ^ cc) (hδ : 0 < δ) (hδ8 : δ ≤ 1 / 8) (hη0 : 0 ≤ η) (hη₀ : 0 < η₀)
    (hτ₃ : 0 < τ₃) (hRl0 : 0 < R)
    -- the schedule
    (S : ModeSchedule) (hD2 : 2 ≤ S.Dstar) (hH2 : 2 ≤ S.H) (hK1 : 1 ≤ S.K)
    (hSd : S.dmax = 2 * dB + 2) (hSDm : S.Dm = max 2 Nl) (hJH : (S.Jstar : ℝ) ≤ Real.log S.H)
    {Λ : ℝ} (hΛ0 : 0 ≤ Λ) (hΛ : Λ ≤ CΛ * (kD * P) ^ eΛ) (hK : (S.K : ℝ) ≤ Msch * Λ ^ 16)
    (hlogH : Real.log S.H ≤ Msch * Λ ^ 12) (hlD : Real.log S.Dstar ≤ Cg * (kD * P) ^ Cg)
    (hexpD : Real.exp kD ≤ S.Dstar)
    -- the leaf quantities
    {Iw : ℕ} (hIw : Iw = ⌊Real.logb 2 (S.Dstar ^ 250)⌋₊)
    {Vl0 : ℝ} (hVl0 : Vl0 = 24 * (⌊180 * S.dmax * Real.log (2 * S.Dm) / (1 / 1024 : ℝ)⌋₊ + 1) *
      (Real.exp ((6144 * (cc + 1) * (1024 * (cc + 1) + cc + 7) + 4) *
        (1 + Real.log (2 * (k : ℝ))) ^ 2) + 2 * 1 / S.Dstar ^ 394))
    {TT : ℝ} (hT0 : 0 ≤ TT)
    (hTTle : TT ≤ 10 ^ 14 * (1 + localFormUniformConstant κ) ^ 2 *
      (((2 ^ famFuel : ℕ) : ℝ)) ^ 4 * (1 + ((2 * famFuel + 2 : ℕ) : ℝ)) ^ 2 * (1 + (S.K : ℝ)) ^ 2 *
      (Real.exp ((4096 * (cc + 1) * (1024 * (cc + 1) + cc + 7) + cc ^ 2 + 3) *
        (1 + Real.log (2 * (k : ℝ))) ^ 2) + E + Vl0 + 1) / ρ)
    {U : ℝ} (hUdef : U = max (2 * (cb + 2) * S.Dstar ^ 2) (Real.sqrt TT))
    {MV : ℝ} (hMV : MV = (Mp : ℝ) * V)
    {ε : ℝ} (hεdef : ε = (U ^ 3 * S.Dstar ^ 5 * Real.exp k * (1 + MV))⁻¹)
    {Mt : ℝ} (hMt : Mt = 24 * (2 * Real.exp ((6144 * (cc + 1) * (1024 * (cc + 1) + cc + 7) + 4) *
      (1 + Real.log (2 * (k : ℝ))) ^ 2) + 2 * S.K * Vl0) *
        (Finset.range (S.Jstar + 1) ×ˢ (Finset.range (Nat.log 2 ⌊S.Dstar⌋₊ + 1) ×ˢ
          Finset.range (Nat.log 2 ⌊S.Dstar⌋₊ + 1)) ×ˢ dyThr ε U S.Dstar).card / ρ)
    {T2v : ℝ}
    (hT2le : T2v ≤ 4 * ((S.K : ℝ) * (20 * Real.exp ((4096 * (cc + 1) *
      (1024 * (cc + 1) + cc + 7) + cc ^ 2 + 3) * (1 + Real.log (2 * (k : ℝ))) ^ 2) + 32) +
        S.K * Vl0) / ρ)
    {B0 cB eB : ℝ} (hB0 : B0 = 2) (hcBdef : cB = coreBd B0 T2v) (heBdef : eB = errBd B0 T2v)
    {cM4 cM3 : ℝ}
    (hcM4 : cM4 = coreM4F κ S (1 / 1024) 3 U ε (max (max 1 Mt) TT))
    (hcM3 : cM3 = ∑ l, coreM3F κ S (1 / 1024) 3 1 Iw U ε (max (max 1 Mt) TT) l)
    -- the near bands
    {nearS Γ : ℝ} {Os : Finset (Fin 4 × Fin 4 × ℕ × ℕ × ℕ × ℕ)}
    (hOs : Os = ActiveSetup.BasicFamilies.FamParams.SideLeafM.nOs (2 ^ famFuel) (2 * famFuel + 2))
    (hΓle : Γ ≤ 2000 * Os.card * (((Nat.log 2 S.K + 1 : ℕ) : ℝ) ^ 3 *
      ((((2 * famFuel + 2 : ℕ) : ℝ) + 1) ^ 2 * Real.exp (2 * (1024 * (cc + 1) *
        (1024 * (cc + 1) + cc + 7) * (1 + Real.log (2 * (k : ℝ))) ^ 2)))) *
      (Real.exp ((4096 * (cc + 1) * (1024 * (cc + 1) + cc + 7) + cc ^ 2 + 3) *
        (1 + Real.log (2 * (k : ℝ))) ^ 2) + Vl0 + E + 1))
    (hnearS : nearS ≤ 64 * (4 * ((nbCM κ hq2 hq3 + nbCUM κ hq2 hq3) *
        (1 + finiteDepthConstant κ q Nd) * (1 + Real.log ((S.K : ℝ) + 2)) *
        ((S.K : ℝ) + 2) ^ (2 * (q - 2) / (q - 1)) * (64 * (2 * (2 * Real.sqrt 1)) *
          (2 * (2 * Real.sqrt 1)))) *
      (hullCutConstant (ρ / 64 / 2) * ((Nat.log 2 S.K + 1 + 1 : ℕ) : ℝ) *
        (1 + Real.log (2 + ((Nat.log 2 S.K + 1 + 1 : ℕ) : ℝ) * ((Nat.log 2 S.K + 1 + 1 : ℕ) : ℝ) *
          (Os.card * (Mp : ℝ) * V)))) * Γ / Real.sqrt P * R))
    -- the core errors and the physical errors
    {cE : ℝ} (hcEsum : cE ≤ (16 * fourErrC κ 3 * ((S.Dstar ^ 100)⁻¹ * S.Dstar ^ 10) +
      K1c * (2 * fourKC κ 3 * 12 ^ 4 * ε * U ^ 3 * S.Dstar ^ 4) +
      4 * (81 * threeErrC κ 3 1 * ((S.Dstar ^ 100)⁻¹ * S.Dstar ^ 10) * U + K1c *
        (8 * entryCU κ 3 1 * 2 ^ (1 + 4) * 12 ^ 3 * ε * U ^ 3 * (S.Dstar ^ 3 * (Iw + 1))))) *
      (((Mp * V : ℕ) : ℝ) * R))
    {Ee : ℝ} (hEe0 : 0 ≤ Ee)
    (hEeb : Ee ≤ (8 * dB * δ + 2 * δ ^ 2) * (4 * Nl * cb ^ 2 * 1) * ((4 * (Mp * V) : ℕ) : ℝ) * R)
    {fc : ℝ} (hfc : fc = (2 * (famFuel : ℝ) + 2) * (((P : ℝ) + 1) ^ 2 * (16 * τ₃ * 2 ^ 2))) :
    6 * 256 * ((2 : ℝ) ^ famFuel) ^ 2 * (2 * η₀ + fc) * TT * R + 6 * nearS +
        η ^ (1 - (1 - 1 / 1200 : ℝ)) * (TT ^ ((1 - 1 / 1200 : ℝ) / 2) *
          TT ^ ((1 - 1 / 1200 : ℝ) / 2) * TT ^ ((1 - 1 / 1200 : ℝ) / 2) * R) +
      82 * (81 * (localFormUniformConstant κ * (cB + eB + Real.sqrt TT) ^ 3) *
        (Real.sqrt (4 * (((Mp * V : ℕ) : ℝ) * R)) * Real.sqrt Ee)) +
      82 * (η ^ (1 - (1 - 1 / 1200 : ℝ)) * (81 * localFormUniformConstant κ *
          max cB (Real.sqrt TT)) ^ (1 - 1 / 1200 : ℝ) *
        (TT ^ ((1 - 1 / 1200 : ℝ) / 2) * TT ^ ((1 - 1 / 1200 : ℝ) / 2) *
          TT ^ ((1 - 1 / 1200 : ℝ) / 2) * R)) +
      (η ^ (1 / 1200 : ℝ) * (R * (cM4 + cM3)) + cE) ≤
    leafBnd Cl kD P k cc η η₀ τ₃ δ (finiteDepthConstant κ q Nd)
      (nbCM κ hq2 hq3 + nbCUM κ hq2 hq3) q R := by
  obtain ⟨hg, hcT, hcL, hcK, hcMc, hcm, hce, hce2, hcQ, hCΛ, heΛ, hCM1, ht3, hCb, hCl⟩ := hconst
  have! hk1 : (1 : ℝ) ≤ k := by linarith only [hk2]
  have hR0 := hRl0.le
  -- the natural-number facts of the constants; their defining equations are then cleared
  have! hCb20n : 20 ≤ Cb := by omega
  have! hccCb : cc + 1 ≤ Cb := by omega
  have! hCgCb : 500 * Cg + 1 ≤ Cb := by omega
  have! heΛCb : 16 * eΛ ≤ Cb := by omega
  have! hMCb1 : (⌈Msch⌉₊ + 1) * CΛ ^ 16 ≤ Cb := by rw [hCb, ← hCM1]; omega
  have! hMCb2 : (⌈Msch⌉₊ + 1) * CΛ ^ 16 + 1 ≤ Cb := by rw [hCb, ← hCM1]; omega
  have! h3Cb : 3 ^ cc ≤ Cb := by rw [hCb, ← ht3]; omega
  have! hcceΛ : 3 * cc ≤ eΛ := by rw [heΛ]; omega
  have! hCgeΛ : Cg ≤ eΛ := by rw [heΛ]; omega
  have! hCΛr : (CΛ : ℝ) = 2 * Cg + 12 := by rw [hCΛ]; push_cast; ring
  have! hgr : (g : ℝ) = 8192 * (cc + 1) * (1024 * (cc + 1) + cc + 7) + cc ^ 2 + 8 := by
    rw [hg]; push_cast; ring
  have hClb : ⌈cm * Cb ^ 59 + ce * Cb ^ 18 + ce2 + 3 * 10 ^ 11 * cQ⌉₊ + 59 * Cb + 4 * g + 8 * cc + 8
      ≤ Cl := hCl.ge
  clear hg hCΛ heΛ hCM1 ht3 hCb hCl
  -- the size parameter `B = C_b u^{C_b}`, `u = k_D P`, and the unit `G = exp(g (1 + log 2k)²)`
  have! hP1 : (1 : ℝ) ≤ P := by exact_mod_cast hP
  have! hkcc0 : (k : ℝ) ≤ (k : ℝ) ^ cc := le_self_pow₀ hk1 (by omega)
  have! hkD1 : (1 : ℝ) ≤ kD := hk1.trans (hkcc0.trans hkD)
  obtain ⟨u, hu⟩ : ∃ x : ℝ, x = kD * P := ⟨_, rfl⟩
  have! hu1 : 1 ≤ u := by rw [hu]; exact one_le_mul_of_one_le_of_one_le hkD1 hP1
  have! hku : (k : ℝ) ≤ u := by
    rw [hu]; exact (hkcc0.trans hkD).trans (le_mul_of_one_le_right (by linarith only [hkD1]) hP1)
  rw [← hu] at hΛ hlD
  obtain ⟨B, hBdef⟩ : ∃ x : ℝ, x = (Cb : ℝ) * u ^ Cb := ⟨_, rfl⟩
  have! hpowB : ∀ (c : ℝ) (e : ℕ), 0 ≤ c → c ≤ Cb → e ≤ Cb → c * u ^ e ≤ B := by
    intro c e hc0 hc he
    have! h1 : u ^ e ≤ u ^ Cb := pow_le_pow_right₀ hu1 he
    have! h0 : (0 : ℝ) ≤ u ^ e := by positivity
    rw [hBdef]
    calc c * u ^ e ≤ Cb * u ^ e := mul_le_mul_of_nonneg_right hc h0
      _ ≤ Cb * u ^ Cb := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _)
  have! hCb20 : (20 : ℝ) ≤ Cb := by
    exact_mod_cast hCb20n
  have! hBB2 : 2 ≤ B := by
    have! this := hpowB 2 0 (by norm_num) (by linarith only [hCb20]) (Nat.zero_le _)
    rwa [pow_zero, mul_one] at this
  have! hBB1 : 1 ≤ B := by linarith only [hBB2]
  have! hkcc : ∀ c : ℝ, 0 ≤ c → c ≤ Cb → c * (k : ℝ) ^ cc ≤ B := by
    intro c hc0 hc
    refine le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith only [hk1]) hku cc)
      hc0) (hpowB c cc hc0 hc ?_)
    omega
  obtain ⟨X, hX⟩ : ∃ x : ℝ, x = (1 + Real.log (2 * (k : ℝ))) ^ 2 := ⟨_, rfl⟩
  have! hX0 : 0 ≤ X := by rw [hX]; positivity
  have! hX4 : X ≤ 4 * k := by rw [hX]; exact one_add_log_two_mul_sq_le hk1
  obtain ⟨G, hGdef⟩ : ∃ x : ℝ, x = Real.exp (g * X) := ⟨_, rfl⟩
  have! hG1 : 1 ≤ G := by rw [hGdef]; exact Real.one_le_exp (by positivity)
  have! hexpG : ∀ c : ℝ, c ≤ g → Real.exp (c * X) ≤ G := fun c hc => by
    rw [hGdef]; exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right hc hX0)
  have! hG0G : Real.exp ((4096 * (cc + 1) * (1024 * (cc + 1) + cc + 7) + cc ^ 2 + 3) *
      (1 + Real.log (2 * (k : ℝ))) ^ 2) ≤ G := by
    rw [← hX]
    refine hexpG _ ?_
    rw [hgr]
    nlinarith only [sq_nonneg (cc : ℝ), Nat.cast_nonneg (α := ℝ) cc]
  have! hGqG : Real.exp ((6144 * (cc + 1) * (1024 * (cc + 1) + cc + 7) + 4) *
      (1 + Real.log (2 * (k : ℝ))) ^ 2) ≤ G := by
    rw [← hX]
    refine hexpG _ ?_
    rw [hgr]
    nlinarith only [sq_nonneg (cc : ℝ), Nat.cast_nonneg (α := ℝ) cc]
  -- the standing bounds at the accuracy `k`
  have! hMp0 : (0 : ℝ) ≤ Mp := Nat.cast_nonneg _
  have! hNl0 : 0 ≤ Nl := by linarith only [hNl4]
  have! hNl1 : 1 ≤ Nl := by linarith only [hNl4]
  have! hcbexp : 2 * cb ≤ Real.exp ((k : ℝ) ^ cc) := by
    rw [← Real.exp_log (show 0 < 2 * cb by linarith only [hcb])]
    exact Real.exp_le_exp.mpr hkb
  have! hbig : 2 * (8 * cb + (1 + Mp) * Nl) ≤ Real.exp ((k : ℝ) ^ cc) := by
    rw [← Real.exp_log (show (0 : ℝ) < 2 * (8 * cb + (1 + Mp) * Nl) by
      have! this : 0 ≤ (1 + (Mp : ℝ)) * Nl := by positivity
      linarith only [this, hcb])]
    exact Real.exp_le_exp.mpr hkB
  have! hNlexp : Nl ≤ Real.exp ((k : ℝ) ^ cc) := by
    have! this : Nl ≤ (1 + (Mp : ℝ)) * Nl := le_mul_of_one_le_left hNl0 (by linarith only [hMp0])
    linarith only [this, hbig, hcb, Real.exp_pos ((k : ℝ) ^ cc)]
  have! hMpexp : (Mp : ℝ) ≤ Real.exp ((k : ℝ) ^ cc) := by
    have! h1 : (Mp : ℝ) ≤ (1 + (Mp : ℝ)) * Nl := by nlinarith only [hNl1, hMp0]
    linarith only [h1, hbig, hcb, Real.exp_pos ((k : ℝ) ^ cc)]
  have! hVexp : (V : ℝ) ≤ 5 * Real.exp ((k : ℝ) ^ cc) := by
    linarith only [hVle, hcbexp, hcb]
  have! hkcc1 : (1 : ℝ) ≤ (k : ℝ) ^ cc := one_le_pow₀ hk1
  have! hD0 : (0 : ℝ) < S.Dstar := by linarith only [hD2]
  have! hD1 : (1 : ℝ) ≤ S.Dstar := by linarith only [hD2]
  have! hlD0 : 0 ≤ Real.log S.Dstar := Real.log_nonneg hD1
  have! hmaxNl : Real.log (max 2 Nl) ≤ (k : ℝ) ^ cc := by
    rw [max_eq_right (by linarith only [hNl4])]
    calc Real.log Nl ≤ Real.log (Real.exp ((k : ℝ) ^ cc)) :=
          Real.log_le_log (by linarith only [hNl4]) hNlexp
      _ = _ := Real.log_exp _
  have! hDm2 : 2 ≤ S.Dm := by rw [hSDm]; exact le_max_left _ _
  -- the schedule parameters are at most `B`
  have! hMc : Msch ≤ ((⌈Msch⌉₊ + 1 : ℕ) : ℝ) := by
    push_cast; linarith only [Nat.le_ceil Msch]
  have! hCΛ1 : (1 : ℝ) ≤ CΛ := by
    rw [hCΛr]; linarith only [Nat.cast_nonneg (α := ℝ) Cg]
  have! hKB : (S.K : ℝ) ≤ B :=
    leaf_final_hKB Msch hMsch CΛ eΛ Cb S Λ hΛ0 hK heΛCb hMCb1 u hΛ hu1 B hpowB hMc hCΛ1
  have! hHB : Real.log S.H + 1 ≤ B :=
    leaf_final_hHB Msch hMsch CΛ eΛ Cb S Λ hΛ0 hlogH heΛCb hMCb2 u hΛ hu1 B hpowB hCΛ1
  have! hJB : (S.Jstar : ℝ) + 1 ≤ B := le_trans (by linarith only [hJH]) hHB
  have! hlHB : Real.log S.H ≤ B := by linarith only [hHB]
  have! hlDB : Real.log S.Dstar ≤ B :=
    hlD.trans (hpowB _ _ (Nat.cast_nonneg _)
      (by exact_mod_cast (show Cg ≤ Cb by omega)) (by omega))
  expose_names
  exact @leaf_final_stage_1 κ q hq2 hq3 Nd Cg Msch g cT cL cK cMc cm ce ce2 cQ CΛ eΛ t3 Cb Cl k cc
    hcc hk2 kD P hP cb Nl Mp V hcb hNl4 hkb famFuel hkF dB hdB1 hdBk E ρ δ η η₀ τ₃ R hE0 hEk hρ
    hρ1 hρk hδ hδ8 hη0 hη₀ hτ₃ hRl0 S hD2 hH2 hK1 hSd hSDm hexpD Iw hIw Vl0 hVl0 TT hT0 hTTle U
    hUdef MV hMV ε hεdef Mt hMt T2v hT2le B0 cB eB hB0 hcBdef heBdef cM4 cM3 hcM4 hcM3 nearS Γ Os
    hOs hΓle hnearS cE hcEsum Ee hEe0 hEeb fc hfc hcT hcL hcK hcMc hcm hce hce2 hcQ hk1 hR0 hCb20n
    hccCb hCgCb hMCb2 h3Cb hgr hClb hkcc0 u hlD hu hu1 B hBdef hpowB hCb20 hBB2 hBB1 hkcc X hX hX0
    hX4 G hGdef hG1 hexpG hG0G hGqG hNl0 hcbexp hNlexp hMpexp hVexp hkcc1 hD0 hD1 hlD0 hmaxNl hDm2
    hKB hJB hlHB hlDB

namespace ActiveSetup.BasicFamilies
variable {κ : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ c₀} (bf : A.BasicFamilies)

/-! Steps of `leaf_estimate`. Each lemma below is one step of that proof, stated over the
hypotheses and local definitions (as `let`s) of the proof that it uses, so that it is
elaborated in a small local context instead of the long context of the whole proof. -/

open Classical in
/-- Step `hn_mono` of `leaf_estimate`, over the part of its context that it uses. -/
theorem leaf_estimate_hn_mono :
    ∀ (κ : LocalKernelClass) (c₀ : ℕ) (A : ActiveSetup κ c₀) (bf : A.BasicFamilies)
      (p : Fin (3 : ℕ)) (AD : bf.AttemptData p), (2 : ℝ) ≤ A.colBudget →
    Monotone AD.n := by
  intro κ c₀ A bf p AD hcb
  let fp : bf.FamParams := AD.fp
  refine monotone_nat_of_le_succ fun r => ?_
  have! h := AD.hgrow r
  have! hR0 := closureRatio_nonneg A.famVtxBound AD.Kt fp.mH AD.Tmax
    (Real.exp (AD.Dst * (1 + Real.log A.Hsrc) ^ AD.Dst)) AD.τ₃
  have! hpos : ∀ r, 0 ≤ AD.n r := by
    intro r
    induction r with
    | zero => linarith only [AD.hn0, hcb]
    | succ r ih =>
      have! h1 := AD.hgrow r
      have! this : (0 : ℝ) ≤ (1 + (fp.Lc + 6) * AD.Mp * closureRatio A.famVtxBound AD.Kt fp.mH
        AD.Tmax (Real.exp (AD.Dst * (1 + Real.log A.Hsrc) ^ AD.Dst)) AD.τ₃) * AD.n r := by
        positivity
      linarith only [h1, this]
  have! hfac : (1 : ℝ) ≤ 1 + (fp.Lc + 6) * AD.Mp * closureRatio A.famVtxBound AD.Kt fp.mH
      AD.Tmax (Real.exp (AD.Dst * (1 + Real.log A.Hsrc) ^ AD.Dst)) AD.τ₃ := by
    have! this : (0 : ℝ) ≤ (fp.Lc + 6) * AD.Mp * closureRatio A.famVtxBound AD.Kt fp.mH
      AD.Tmax (Real.exp (AD.Dst * (1 + Real.log A.Hsrc) ^ AD.Dst)) AD.τ₃ := by positivity
    linarith only [this]
  exact (le_mul_of_one_le_left (hpos r) hfac).trans h

open Classical in
/-- Step `hpathU` of `leaf_estimate`, over the part of its context that it uses. -/
theorem leaf_estimate_hpathU :
    ∀ (κ : LocalKernelClass) (c₀ : ℕ) (A : ActiveSetup κ c₀) (bf : A.BasicFamilies)
      (p : Fin (3 : ℕ)) (AD : bf.AttemptData p) (s : ℕ),
    let fp : bf.FamParams := AD.fp;
    let Lf : SearchLeaf := leafAt A.famFuel fp.Lc (A.basicSlot p) s;
    let ks : ℕ := Lf.k;
    let S0 : Finset (ℤ × ℤ) := {I ∈ AD.Tc | ¬∃ c ∈ fp.failRoots, dyadicGridCell A.G I.1 I.2 ⊆
        dyadicGridCell A.G c.1 c.2};
    S0 ⊆ AD.Tc →
    let gs : ℤ × ℤ → Finset bf.Grp := fun (I : ℤ × ℤ) ↦ fp.groupsAt I ks;
    let gset : Finset bf.Grp := S0.biUnion gs;
    let U : Fin (4 : ℕ) → bf.Grp → Finset (ℤ × ℤ) := fun (_ : Fin (4 : ℕ)) (G : bf.Grp) ↦ {I ∈
        S0 | G ∈ gs I};
    (U = fun (_ : Fin (4 : ℕ)) (G : bf.Grp) ↦ {I ∈ S0 | G ∈ gs I}) →
    ∀ y, ∑ l, ∑ G ∈ gset, ((U l G).filter fun I : ℤ × ℤ =>
    y ∈ dyadicGridCell A.G I.1 I.2).card ≤ 4 * (AD.Mp * A.famVtxBound) := by
  intro κ c₀ A bf p AD s fp Lf ks S0 hS0T gs gset U hU y
  simp only [hU]
  calc ∑ _l : Fin 4, ∑ G ∈ gset, ((S0.filter fun I => G ∈ gs I).filter fun I : ℤ × ℤ =>
        y ∈ dyadicGridCell A.G I.1 I.2).card
      ≤ ∑ _l : Fin 4, AD.Mp * A.famVtxBound :=
        Finset.sum_le_sum fun l _ => by
          have! h := sum_card_uses_le A.G S0 gs gset y
            (le_trans (Finset.card_le_card (Finset.filter_subset_filter _ hS0T))
              (card_cells_mem_le A.G AD.Tc AD.hmult y))
            (fun I _ => fp.card_groupsAt_le I ks)
          convert h
    _ = 4 * (AD.Mp * A.famVtxBound) := by simp

open Classical in
/-- Step `hU16` of `leaf_estimate`, over the part of its context that it uses. -/
theorem leaf_estimate_hU16 :
    ∀ (κ : LocalKernelClass) (c₀ : ℕ) (A : ActiveSetup κ c₀), (2 : ℝ) ≤ A.colBudget →
      ∀ (S : ModeSchedule), (2 : ℝ) ≤ S.Dstar → ∀ (U : ℝ),
      (2 : ℝ) * (A.colBudget + (2 : ℝ)) * S.Dstar ^ (2 : ℕ) ≤ U →
    16 ≤ U := by
  intro κ c₀ A hcb S hD2 U hU4
  refine le_trans ?_ hU4
  have! h1 : (2 : ℝ) + 2 ≤ A.colBudget + 2 := by linarith only [hcb]
  have! h2 : (2 : ℝ) ^ 2 ≤ S.Dstar ^ 2 := pow_le_pow_left₀ (by norm_num) hD2 2
  calc (16 : ℝ) ≤ 2 * (2 + 2) * 2 ^ 2 := by norm_num
    _ ≤ 2 * (A.colBudget + 2) * 2 ^ 2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (by norm_num)) (by norm_num)
    _ ≤ 2 * (A.colBudget + 2) * S.Dstar ^ 2 :=
        mul_le_mul_of_nonneg_left h2 (by linarith only [hcb])

open Classical in
/-- Step `hMV0` of `leaf_estimate`, over the part of its context that it uses. -/
theorem leaf_estimate_hMV0 :
    ∀ (κ : LocalKernelClass) (c₀ : ℕ) (A : ActiveSetup κ c₀) (bf : A.BasicFamilies)
      (p : Fin (3 : ℕ)) (AD : bf.AttemptData p) (MV : ℝ), MV = (↑AD.Mp : ℝ) * (↑A.famVtxBound : ℝ) →
    0 ≤ MV := by
  intro κ c₀ A bf p AD MV hMV
  rw [hMV]; positivity

open Classical in
/-- Step `hε0` of `leaf_estimate`, over the part of its context that it uses. -/
theorem leaf_estimate_hε0 :
    ∀ (k : ℕ) (S : ModeSchedule), (2 : ℝ) ≤ S.Dstar → ∀ (U : ℝ), (16 : ℝ) ≤ U → ∀ (MV : ℝ),
      (0 : ℝ) ≤ MV → ∀ (ε : ℝ),
      ε = (U ^ (3 : ℕ) * S.Dstar ^ (5 : ℕ) * Real.exp (↑k : ℝ) * ((1 : ℝ) + MV))⁻¹ →
    0 < ε := by
  intro k S hD2 U hU16 MV hMV0 ε hεdef
  rw [hεdef]
  exact inv_pos.mpr (by positivity)

open Classical in
/-- Step `hτb` of `leaf_estimate`, over the part of its context that it uses. -/
theorem leaf_estimate_hτb :
    ∀ (κ : LocalKernelClass) (c₀ : ℕ) (A : ActiveSetup κ c₀) (bf : A.BasicFamilies)
      (p : Fin (3 : ℕ)) (AD : bf.AttemptData p),
    let fp : bf.FamParams := AD.fp;
    let Nl : ℝ := AD.n (fp.Lc + (5 : ℕ));
    let BN : ℕ := ⌈(8 : ℝ) * A.colBudget + Nl⌉₊;
    let τb : ℝ := (1 : ℝ) / ((1 : ℝ) + (↑BN : ℝ) * A.colBudget ^ (2 : ℕ));
    0 < τb := by
  intro κ c₀ A bf p AD fp Nl BN τb
  positivity

open Classical in
/-- Step `hτb1` of `leaf_estimate`, over the part of its context that it uses. -/
theorem leaf_estimate_hτb1 :
    ∀ (κ : LocalKernelClass) (c₀ : ℕ) (A : ActiveSetup κ c₀) (bf : A.BasicFamilies)
      (p : Fin (3 : ℕ)) (AD : bf.AttemptData p),
    let fp : bf.FamParams := AD.fp;
    let Nl : ℝ := AD.n (fp.Lc + (5 : ℕ));
    let BN : ℕ := ⌈(8 : ℝ) * A.colBudget + Nl⌉₊;
    let τb : ℝ := (1 : ℝ) / ((1 : ℝ) + (↑BN : ℝ) * A.colBudget ^ (2 : ℕ));
    τb = (1 : ℝ) / ((1 : ℝ) + (↑BN : ℝ) * A.colBudget ^ (2 : ℕ)) →
    τb ≤ 1 := by
  intro κ c₀ A bf p AD fp Nl BN τb hτbdef
  rw [hτbdef, div_le_one (by positivity)]
  have! this : (0 : ℝ) ≤ BN * A.colBudget ^ 2 := by positivity
  linarith only [this]

open Classical in
/-- Step `hτbN` of `leaf_estimate`, over the part of its context that it uses. -/
theorem leaf_estimate_hτbN :
    ∀ (κ : LocalKernelClass) (c₀ : ℕ) (A : ActiveSetup κ c₀) (bf : A.BasicFamilies)
      (p : Fin (3 : ℕ)) (AD : bf.AttemptData p),
    let fp : bf.FamParams := AD.fp;
    let Nl : ℝ := AD.n (fp.Lc + (5 : ℕ));
    let BN : ℕ := ⌈(8 : ℝ) * A.colBudget + Nl⌉₊;
    let τb : ℝ := (1 : ℝ) / ((1 : ℝ) + (↑BN : ℝ) * A.colBudget ^ (2 : ℕ));
    τb = (1 : ℝ) / ((1 : ℝ) + (↑BN : ℝ) * A.colBudget ^ (2 : ℕ)) →
    τb * BN * A.colBudget ^ 2 ≤ 1 := by
  intro κ c₀ A bf p AD fp Nl BN τb hτbdef
  rw [hτbdef, div_mul_eq_mul_div, div_mul_eq_mul_div, one_mul, div_le_one (by positivity)]
  linarith only

open Classical in
/-- Step `hNq` of `leaf_estimate`, over the part of its context that it uses. -/
theorem leaf_estimate_hNq :
    ∀ (κ : LocalKernelClass) (c₀ : ℕ) (A : ActiveSetup κ c₀) (bf : A.BasicFamilies), ℝ →
      ∀ (p : Fin (3 : ℕ)) (AD : bf.AttemptData p) (d : bf.Vtx) (s : ℕ),
    let fp : bf.FamParams := AD.fp;
    let Nl : ℝ := AD.n (fp.Lc + (5 : ℕ));
    (0 : ℝ) ≤ Nl →
    let Lf : SearchLeaf := leafAt A.famFuel fp.Lc (A.basicSlot p) s;
    let ks : ℕ := Lf.k;
    let S0 : Finset (ℤ × ℤ) := {I ∈ AD.Tc | ¬∃ c ∈ fp.failRoots, dyadicGridCell A.G I.1 I.2 ⊆
        dyadicGridCell A.G c.1 c.2};
    let gs : ℤ × ℤ → Finset bf.Grp := fun (I : ℤ × ℤ) ↦ fp.groupsAt I ks;
    let gset : Finset bf.Grp := S0.biUnion gs;
    (∀ (l : Fin (4 : ℕ)), (AD.cat l).length ≤ fp.Mc) →
    let BN : ℕ := ⌈(8 : ℝ) * A.colBudget + Nl⌉₊;
    (∀ (G : ↥gset), (↑G : bf.Grp).1 = ks) →
      (∀ (l : Fin (4 : ℕ)), fp.bbase (Lf.role l) + fp.P ≤ fp.Hmax) →
    ∀ l y, ((Finset.univ : Finset ({G // G ∈ gset} × (bf.Lab ⊕ Fin fp.Mc))).filter
    fun q => ∃ I ∈ A.cells, (∃ k', fp.Cert k' q.1.1 I) ∧ ∃ p : Fin fp.P,
    y ∈ dyadicGridCell A.G I.1 I.2 ∧
    q.2 ∈ mainLabelsM A.G fp.Mc (bf.origCols l) (AD.cat l) I (fp.brank (Lf.role l))
    (fp.bmask I q.1.1 (Lf.role l) (p + 1)) d).card ≤ BN := by
  intro κ c₀ A bf q p AD d s fp Nl hNl0 Lf ks S0 gs gset hlenMc BN hcolG hPH l y
  have! h1 := fp.card_ballPairs_le l (AD.cat l) d (ι := {G // G ∈ gset}) Subtype.val
    Subtype.val_injective ks hcolG (Lf.role l) (hPH l) y
  have! h2 := bf.card_pathLabels_le l (Mc := fp.Mc) (AD.cat l) (fp.brank (Lf.role l)) y
  have! h3 := bf.tmplPath_le fp.Mc (AD.cat l) (hlenMc l) l (fun e he => AD.hTc (AD.hT l e he).1)
    (r := fp.Lc + 5) (fun e he => (AD.hT l e he).2.1) hNl0 (fun I _ => AD.hlab l I _ le_rfl) y
  have! h4 : (((Finset.univ : Finset ({G // G ∈ gset} × (bf.Lab ⊕ Fin fp.Mc))).filter
    fun q => ∃ I ∈ A.cells, (∃ k', fp.Cert k' q.1.1 I) ∧ ∃ p : Fin fp.P,
      y ∈ dyadicGridCell A.G I.1 I.2 ∧
      q.2 ∈ mainLabelsM A.G fp.Mc (bf.origCols l) (AD.cat l) I (fp.brank (Lf.role l))
        (fp.bmask I q.1.1 (Lf.role l) (p + 1)) d).card : ℝ) ≤ 8 * A.colBudget + Nl :=
    le_trans (Nat.cast_le.mpr h1) (le_trans h2 (by linarith only [h3]))
  exact Nat.cast_le.mp (h4.trans (Nat.le_ceil _))

open Classical in
/-- Step `hden` of `leaf_estimate`, over the part of its context that it uses. -/
theorem leaf_estimate_hden :
    ∀ (κ : LocalKernelClass) (c₀ : ℕ) (A : ActiveSetup κ c₀) (bf : A.BasicFamilies)
      (p : Fin (3 : ℕ)) (AD : bf.AttemptData p),
    let fp : bf.FamParams := AD.fp;
    let Nl : ℝ := AD.n (fp.Lc + (5 : ℕ));
    (2 : ℝ) ≤ A.colBudget → (4 : ℝ) ≤ Nl →
    let NH : ℝ := (2 : ℝ) * A.colBudget + ((1 : ℝ) + (↑AD.Mp : ℝ)) * Nl;
    0 < 1 + A.colBudget * Real.sqrt (AD.n (fp.Lc + 4)) *
    (A.colBudget * Real.sqrt NH) := by
  intro κ c₀ A bf p AD fp Nl hcb hNl4 NH
  positivity

open Classical in
/-- Step `hτ₂1` of `leaf_estimate`, over the part of its context that it uses. -/
theorem leaf_estimate_hτ₂1 :
    ∀ (κ : LocalKernelClass) (c₀ : ℕ) (A : ActiveSetup κ c₀) (bf : A.BasicFamilies)
      (p : Fin (3 : ℕ)) (AD : bf.AttemptData p),
    let fp : bf.FamParams := AD.fp;
    let Nl : ℝ := AD.n (fp.Lc + (5 : ℕ));
    (2 : ℝ) ≤ A.colBudget → (4 : ℝ) ≤ Nl →
    let NH : ℝ := (2 : ℝ) * A.colBudget + ((1 : ℝ) + (↑AD.Mp : ℝ)) * Nl;
    let τ₂ : ℝ := AD.τ₃ / ((1 : ℝ) + A.colBudget * √(AD.n (fp.Lc + (4 : ℕ))) * (A.colBudget * √NH));
    τ₂ = AD.τ₃ / ((1 : ℝ) + A.colBudget * √(AD.n (fp.Lc + (4 : ℕ))) * (A.colBudget * √NH)) →
      (0 : ℝ) < (1 : ℝ) + A.colBudget * √(AD.n (fp.Lc + (4 : ℕ))) * (A.colBudget * √NH) →
    τ₂ ≤ 1 := by
  intro κ c₀ A bf p AD fp Nl hcb hNl4 NH τ₂ hτ₂def hden
  rw [hτ₂def, div_le_one hden]
  have! this : 0 ≤ A.colBudget * Real.sqrt (AD.n (fp.Lc + 4)) *
      (A.colBudget * Real.sqrt NH) := by
    positivity
  linarith only [this, AD.hτ₃1]

open Classical in
/-- Step `hτ₂'` of `leaf_estimate`, over the part of its context that it uses. -/
theorem leaf_estimate_hτ₂' :
    ∀ (κ : LocalKernelClass) (c₀ : ℕ) (A : ActiveSetup κ c₀) (bf : A.BasicFamilies)
      (p : Fin (3 : ℕ)) (AD : bf.AttemptData p),
    let fp : bf.FamParams := AD.fp;
    let Nl : ℝ := AD.n (fp.Lc + (5 : ℕ));
    (2 : ℝ) ≤ A.colBudget → (4 : ℝ) ≤ Nl →
    let NH : ℝ := (2 : ℝ) * A.colBudget + ((1 : ℝ) + (↑AD.Mp : ℝ)) * Nl;
    let τ₂ : ℝ := AD.τ₃ / ((1 : ℝ) + A.colBudget * √(AD.n (fp.Lc + (4 : ℕ))) * (A.colBudget * √NH));
    τ₂ = AD.τ₃ / ((1 : ℝ) + A.colBudget * √(AD.n (fp.Lc + (4 : ℕ))) * (A.colBudget * √NH)) →
      (0 : ℝ) < (1 : ℝ) + A.colBudget * √(AD.n (fp.Lc + (4 : ℕ))) * (A.colBudget * √NH) →
    τ₂ * (A.colBudget * Real.sqrt (AD.n (fp.Lc + 4)) * (A.colBudget * Real.sqrt NH)) ≤
    AD.τ₃ := by
  intro κ c₀ A bf p AD fp Nl hcb hNl4 NH τ₂ hτ₂def hden
  rw [hτ₂def, div_mul_eq_mul_div, div_le_iff₀ hden]
  have! this : 0 ≤ A.colBudget * Real.sqrt (AD.n (fp.Lc + 4)) *
      (A.colBudget * Real.sqrt NH) := by
    positivity
  nlinarith only [this, AD.hτ₃]

open Classical in
/-- Step `hcapV0` of `leaf_estimate`, over the part of its context that it uses. -/
theorem leaf_estimate_hcapV0 :
    ∀ (κ : LocalKernelClass) (c₀ : ℕ) (cc : ℕ) (A : ActiveSetup κ c₀) (k : ℕ),
      (0 : ℝ) < dyadicGridLength A.G A.R.1 →
    0 ≤ FamParams.capV A cc k := by
  intro κ c₀ cc A k hRl0
  unfold FamParams.capV; positivity

open Classical in
/-- Step `hVl00` of `leaf_estimate`, over the part of its context that it uses. -/
theorem leaf_estimate_hVl00 :
    ∀ (cc : ℕ) (k : ℕ) (S : ModeSchedule) (Vl0 : ℝ),
      Vl0 = (24 : ℝ) * ((↑⌊(180 : ℝ) * (↑S.dmax : ℝ) * Real.log ((2 : ℝ) * S.Dm) / (1 /
        1024 : ℝ)⌋₊ : ℝ) + (1 : ℝ)) * (Real.exp (((6144 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) *
        ((1024 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) + (↑cc : ℝ) + (7 : ℝ)) + (4 : ℝ)) * ((1 : ℝ) +
        Real.log ((2 : ℝ) * (↑k : ℝ))) ^ (2 : ℕ)) + (2 : ℝ) * (1 : ℝ) / S.Dstar ^ (394 : ℕ)) →
    0 ≤ Vl0 := by
  intro cc k S Vl0 hVl0
  rw [hVl0]; positivity

open Classical in
/-- Step `hB00` of `leaf_estimate`, over the part of its context that it uses. -/
theorem leaf_estimate_hB00 :
    ∀ (κ : LocalKernelClass) (c₀ : ℕ) (cc : ℕ) (A : ActiveSetup κ c₀) (k : ℕ) (Vl0 : ℝ),
      (0 : ℝ) < dyadicGridLength A.G A.R.1 → (0 : ℝ) ≤ Vl0 →
    0 ≤ FamParams.SideInput.sideB0 A cc k Vl0 := by
  intro κ c₀ cc A k Vl0 hRl0 hVl00
  unfold FamParams.SideInput.sideB0; positivity

open Classical in
/-- Step `hbig` of `leaf_estimate`, over the part of its context that it uses. -/
theorem leaf_estimate_hbig :
    ∀ (κ : LocalKernelClass) (c₀ : ℕ) (cc : ℕ) (A : ActiveSetup κ c₀) (bf : A.BasicFamilies) (k : ℕ)
      (p : Fin (3 : ℕ)) (AD : bf.AttemptData p),
    let fp : bf.FamParams := AD.fp;
    let Nl : ℝ := AD.n (fp.Lc + (5 : ℕ));
    Real.log ((2 : ℝ) * ((8 : ℝ) * A.colBudget + ((1 : ℝ) + (↑AD.Mp : ℝ)) * Nl)) ≤ (↑k : ℝ) ^ cc →
      (2 : ℝ) ≤ A.colBudget → (4 : ℝ) ≤ Nl →
    2 * (8 * A.colBudget + (1 + AD.Mp) * Nl) ≤ Real.exp ((k : ℝ) ^ cc) := by
  intro κ c₀ cc A bf k p AD fp Nl hkB hcb hNl4
  rw [← Real.exp_log (show (0 : ℝ) < 2 * (8 * A.colBudget + (1 + AD.Mp) * Nl) by
    have! this : 0 ≤ (1 + (AD.Mp : ℝ)) * Nl := by positivity
    linarith only [this, hcb])]
  exact Real.exp_le_exp.mpr hkB

open Classical in
/-- Step `h64D` of `leaf_estimate`, over the part of its context that it uses. -/
theorem leaf_estimate_h64D :
    ∀ (cc : ℕ), (1 : ℕ) ≤ cc → ∀ (kD : ℝ), (1 : ℝ) ≤ kD → (2 : ℝ) ≤ kD →
    64 * kD ≤ kD ^ (cc + 6) := by
  intro cc hcc kD hkD1 hkD2
  have! h1 : (2 : ℝ) ^ (cc + 5) ≤ kD ^ (cc + 5) := pow_le_pow_left₀ (by norm_num) hkD2 _
  have! h2 : (64 : ℝ) ≤ 2 ^ (cc + 5) := by
    calc (64 : ℝ) = 2 ^ 6 := by norm_num
      _ ≤ 2 ^ (cc + 5) := pow_le_pow_right₀ (by norm_num) (by omega)
  rw [show cc + 6 = (cc + 5) + 1 by omega, pow_succ]
  nlinarith only [h1, h2, hkD1]

open Classical in
/-- Step `hlogHm` of `leaf_estimate`, over the part of its context that it uses. -/
theorem leaf_estimate_hlogHm :
    ∀ (κ : LocalKernelClass) (c₀ : ℕ) (cc : ℕ) (A : ActiveSetup κ c₀) (k : ℕ) (δ : ℝ) (kD : ℝ),
      (0 : ℝ) < δ →
    let dB : ℕ := A.dBnd;
    let Hm : ℝ := max (max A.Hsrc (Real.exp (↑dB : ℝ))) (max ((5832 : ℝ) * max A.H padW ^ (4 : ℕ))
        ((↑dB : ℝ) * (bumpConst * (8 : ℝ) ^ (32 : ℕ) * ((2 : ℝ) / δ))));
    (1 : ℝ) ≤ Hm → (↑dB : ℝ) ≤ (↑k : ℝ) ^ cc → Real.log A.Hsrc ≤ (↑k : ℝ) ^ cc →
      Real.log (max A.H padW) ≤ (↑k : ℝ) ^ cc → δ⁻¹ ≤ Real.exp kD → (↑k : ℝ) ^ cc ≤ kD →
      (1 : ℝ) ≤ kD → (1 : ℝ) ≤ (↑k : ℝ) ^ cc → kD ≤ kD ^ (cc + (6 : ℕ)) →
      (↑k : ℝ) ^ cc ≤ kD ^ (cc + (6 : ℕ)) → (64 : ℝ) * kD ≤ kD ^ (cc + (6 : ℕ)) →
      (64 : ℝ) * (↑k : ℝ) ^ cc ≤ kD ^ (cc + (6 : ℕ)) →
      Real.log bumpConst + (68 : ℝ) ≤ (↑k : ℝ) ^ cc →
    Real.log Hm ≤ kD ^ (cc + 6) := by
  intro κ c₀ cc A k δ kD hδ dB Hm hHm1 hdBk hHsk hHWk hδk hkD hkD1 hkcc1 hkDle hkk h64D h64 hkK0
  set! Y := kD ^ (cc + 6) with hY
  rewrite [← hY] at hkDle hkk h64D h64 ⊢
  have! hHs0 : 0 < A.Hsrc := lt_of_lt_of_le (Real.exp_pos 2) A.exp_two_le_Hsrc
  have! hW0 : 0 < max A.H ActiveSetup.padW :=
    lt_of_lt_of_le (Real.exp_pos 2) (le_trans (le_max_left _ _) (le_max_right _ _))
  have! ha : A.Hsrc ≤ Real.exp Y := by
    rw [← Real.exp_log hHs0]; exact Real.exp_le_exp.mpr (hHsk.trans hkk)
  have! hb : Real.exp dB ≤ Real.exp Y := Real.exp_le_exp.mpr (hdBk.trans hkk)
  have! he9 : (5832 : ℝ) ≤ Real.exp 9 := by
    have! h1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith only [Real.exp_one_gt_d9]
    have! h2 := pow_le_pow_left₀ (by norm_num) h1 9
    rw [← Real.exp_nat_mul] at h2
    norm_num at h2 ⊢
    linarith only [h2]
  have! hc : 5832 * max A.H ActiveSetup.padW ^ 4 ≤ Real.exp Y := by
    have! h1 : max A.H ActiveSetup.padW ^ 4 ≤ Real.exp (4 * (k : ℝ) ^ cc) := by
      rw [← Real.exp_log hW0, ← Real.exp_nat_mul]
      push_cast
      exact Real.exp_le_exp.mpr (by linarith only [hHWk])
    calc 5832 * max A.H ActiveSetup.padW ^ 4 ≤ Real.exp 9 * Real.exp (4 * (k : ℝ) ^ cc) :=
          mul_le_mul he9 h1 (by positivity) (Real.exp_pos _).le
      _ = Real.exp (9 + 4 * (k : ℝ) ^ cc) := (Real.exp_add _ _).symm
      _ ≤ Real.exp Y := Real.exp_le_exp.mpr (by linarith only [h64, hkcc1])
  have! hd : (dB : ℝ) * (bumpConst * 8 ^ 32 * (2 / δ)) ≤ Real.exp Y := by
    have! hdB0 : (dB : ℝ) ≤ Real.exp ((k : ℝ) ^ cc) :=
      hdBk.trans ((Real.add_one_le_exp _).trans' (by linarith only []))
    have! h8 : (8 : ℝ) ^ 32 * 2 ≤ Real.exp 68 := by
      have! h1 : (2.7 : ℝ) ≤ Real.exp 1 := by linarith only [Real.exp_one_gt_d9]
      have! h2 := pow_le_pow_left₀ (by norm_num) h1 68
      rw [← Real.exp_nat_mul] at h2
      norm_num at h2 ⊢
      linarith only [h2]
    have! hδi : 2 / δ = (8 : ℝ) ^ 0 * 2 * δ⁻¹ := by rw [pow_zero, one_mul, div_eq_mul_inv]
    have! hb0 : bumpConst = Real.exp (Real.log bumpConst) :=
      (Real.exp_log (lt_of_lt_of_le one_pos one_le_bumpConst)).symm
    calc (dB : ℝ) * (bumpConst * 8 ^ 32 * (2 / δ))
        = (dB : ℝ) * bumpConst * ((8 : ℝ) ^ 32 * 2) * δ⁻¹ := by
          rw [div_eq_mul_inv]; ring
      _ ≤ Real.exp ((k : ℝ) ^ cc) * Real.exp (Real.log bumpConst) * Real.exp 68 *
          Real.exp kD := by
          rw [← hb0]
          have hb1 := one_le_bumpConst
          gcongr
      _ = Real.exp ((k : ℝ) ^ cc + Real.log bumpConst + 68 + kD) := by
          rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
      _ ≤ Real.exp Y := Real.exp_le_exp.mpr (by linarith only [h64D, hkK0, hkD, hkD1])
  have! hHmY : Hm ≤ Real.exp Y := max_le (max_le ha hb) (max_le hc hd)
  rw [← Real.exp_log (lt_of_lt_of_le one_pos hHm1)] at hHmY
  exact Real.exp_le_exp.mp hHmY

open Classical in
/-- Step `hQ0l` of `leaf_estimate`, over the part of its context that it uses. -/
theorem leaf_estimate_hQ0l :
    ∀ (κ : LocalKernelClass) (c₀ : ℕ) (cc : ℕ) (A : ActiveSetup κ c₀) (bf : A.BasicFamilies) (k : ℕ)
      (p : Fin (3 : ℕ)) (AD : bf.AttemptData p), (1 : ℝ) ≤ (↑k : ℝ) →
    let fp : bf.FamParams := AD.fp;
    let dB : ℕ := A.dBnd;
    (1 : ℕ) ≤ dB → (↑dB : ℝ) ≤ (↑k : ℝ) ^ cc → Real.log fp.Hed ≤ (↑k : ℝ) ^ cc →
    Real.log (fp.Q0bd dB) ≤ (k : ℝ) ^ (3 * cc) + 1 := by
  intro κ c₀ cc A bf k p AD hk1 fp dB hdB1 hdBk hHedk
  have! hq := fp.Q0bd_le dB AD.hHed2
  have! hH1 : (1 : ℝ) ≤ fp.Hed ^ (dB * dB) := one_le_pow₀ (by linarith only [AD.hHed2])
  have! hq1 : (1 : ℝ) ≤ fp.Q0bd dB := by exact_mod_cast fp.one_le_Q0bd dB AD.hHed2
  have! h2 : (fp.Q0bd dB : ℝ) ≤ 2 * fp.Hed ^ (dB * dB) := by linarith only [hq, hH1]
  have! h3 : Real.log (fp.Q0bd dB) ≤ Real.log 2 + ((dB * dB : ℕ) : ℝ) * Real.log fp.Hed := by
    rw [← Real.log_pow, ← Real.log_mul (by norm_num) (by positivity)]
    exact Real.log_le_log (by linarith only [hq1]) h2
  have! hl2 : Real.log 2 ≤ 1 := by linarith only [Real.log_two_lt_d9]
  have! hHl0 : 0 ≤ Real.log fp.Hed := Real.log_nonneg (by linarith only [AD.hHed2])
  have! hdB0 : (0 : ℝ) ≤ dB := Nat.cast_nonneg _
  have! hdd : ((dB * dB : ℕ) : ℝ) * Real.log fp.Hed ≤ (k : ℝ) ^ (3 * cc) := by
    push_cast
    calc (dB : ℝ) * dB * Real.log fp.Hed ≤ (k : ℝ) ^ cc * (k : ℝ) ^ cc * (k : ℝ) ^ cc := by
          gcongr
      _ = (k : ℝ) ^ (3 * cc) := by ring
  linarith only [h3, hl2, hdd]

open Classical in
/-- Step `hΛ0` of `leaf_estimate`, over the part of its context that it uses. -/
theorem leaf_estimate_hΛ0 :
    ∀ (κ : LocalKernelClass) (c₀ : ℕ) (Dm0 : ℕ) (A : ActiveSetup κ c₀) (bf : A.BasicFamilies)
      (p : Fin (3 : ℕ)) (AD : bf.AttemptData p) (δ : ℝ) (kD : ℝ),
    let fp : bf.FamParams := AD.fp;
    let dB : ℕ := A.dBnd;
    let Nl : ℝ := AD.n (fp.Lc + (5 : ℕ));
    let Hm : ℝ := max (max A.Hsrc (Real.exp (↑dB : ℝ))) (max ((5832 : ℝ) * max A.H padW ^ (4 : ℕ))
        ((↑dB : ℝ) * (bumpConst * (8 : ℝ) ^ (32 : ℕ) * ((2 : ℝ) / δ))));
    (1 : ℕ) ≤ dB → (0 : ℝ) ≤ Real.log (max (2 : ℝ) Nl) →
      Real.log (fp.Bst Dm0 dB Hm δ Nl kD δ) = Real.log (↑(fp.Q0bd dB) : ℝ) + Real.log ((2 : ℝ) ^
        (fp.Kstar Dm0 dB Hm δ Nl kD δ + (1 : ℕ))) →
      (0 : ℝ) ≤ Real.log ((2 : ℝ) ^ (fp.Kstar Dm0 dB Hm δ Nl kD δ + (1 : ℕ))) →
      (0 : ℝ) ≤ Real.log (fp.modeStarG Dm0 dB Hm δ Nl kD δ) →
    let Λ : ℝ := (↑((2 : ℕ) * dB + (2 : ℕ)) : ℝ) + Real.log (fp.modeStarG Dm0 dB Hm δ Nl kD δ) +
        Real.log (fp.Bst Dm0 dB Hm δ Nl kD δ) + Real.log (max (2 : ℝ) Nl) + Real.log (↑(fp.Q0bd
        dB) : ℝ) + (1 : ℝ);
    Λ = (↑((2 : ℕ) * dB + (2 : ℕ)) : ℝ) + Real.log (fp.modeStarG Dm0 dB Hm δ Nl kD δ) + Real.log
        (fp.Bst Dm0 dB Hm δ Nl kD δ) + Real.log (max (2 : ℝ) Nl) + Real.log (↑(fp.Q0bd dB) : ℝ) +
        (1 : ℝ) →
    0 ≤ Λ := by
  intro κ c₀ Dm0 A bf p AD δ kD fp dB Nl Hm hdB1 hmaxNl0 hBstl hlK0 hlDG0 Λ hΛdef
  rw [hΛdef, hBstl]; positivity

open Classical in
/-- Step `hE0` of `leaf_estimate`, over the part of its context that it uses. -/
theorem leaf_estimate_hE0 :
    ∀ (κ : LocalKernelClass) (c₀ : ℕ) (A : ActiveSetup κ c₀) (η₀ : ℝ) (E : ℝ), A.SubRootProps η₀ E →
      (0 : ℝ) < dyadicGridLength A.G A.R.1 →
    0 ≤ E := by
  intro κ c₀ A η₀ E hsub hRl0
  obtain ⟨h1, -, -⟩ := hsub A.R subset_rfl
  have! h := h1 0
  have! h0 : 0 ≤ ∑ I ∈ A.cells with dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G A.R.1 A.R.2,
      dyadicGridLength A.G I.1 * (MeasureTheory.eLpNorm (A.U 0 I) 2 (A.μ I)).toReal ^ 2 :=
    Finset.sum_nonneg fun I _ => mul_nonneg (dyadicGridLength_pos A.G I.1).le (sq_nonneg _)
  by_contra hneg
  push Not at hneg
  have! this : E * dyadicGridLength A.G A.R.1 < 0 := mul_neg_of_neg_of_pos hneg hRl0
  linarith only [h, h0, this]

open Classical in
/-- Step `hT0` of `leaf_estimate`, over the part of its context that it uses. -/
theorem leaf_estimate_hT0 :
    ∀ (κ : LocalKernelClass) (c₀ : ℕ) (cc : ℕ) (A : ActiveSetup κ c₀) (bf : A.BasicFamilies) (k : ℕ)
      (E : ℝ) (p : Fin (3 : ℕ)) (AD : bf.AttemptData p) (ρ : ℝ), (0 : ℝ) < ρ →
    let fp : bf.FamParams := AD.fp;
    ∀ (S : ModeSchedule), (1 : ℕ) ≤ S.K → ∀ (Vl0 : ℝ), (0 : ℝ) < dyadicGridLength A.G A.R.1 →
      (0 : ℝ) ≤ Vl0 → (1 : ℝ) ≤ (↑fp.P : ℝ) → (0 : ℝ) ≤ E →
    let TT : ℝ := TsideF A fp.P S.K (A.uslot p) ((2 : ℕ) ^ A.famFuel) ((2 : ℕ) * A.famFuel +
        (2 : ℕ)) (1 : ℝ) E cc (↑k : ℝ) (fun (_ : Fin (4 : ℕ)) ↦ Vl0) ρ;
    (TT = TsideF A fp.P S.K (A.uslot p) ((2 : ℕ) ^ A.famFuel) ((2 : ℕ) * A.famFuel + (2 : ℕ))
        (1 : ℝ) E cc (↑k : ℝ) (fun (_ : Fin (4 : ℕ)) ↦ Vl0) ρ) →
    0 ≤ TT := by
  intro κ c₀ cc A bf k E p AD ρ hρ fp S hK1 Vl0 hRl0 hVl00 hP1 hE0 TT hTT
  rw [hTT]; unfold TsideF; dsimp only
  have := hVl00
  have! hL0 := localFormUniformConstant_nonneg κ
  refine div_nonneg (add_nonneg (div_nonneg ?_ hRl0.le) (div_nonneg ?_ hRl0.le)) hρ.le
  · exact Finset.sum_nonneg fun l _ => by split_ifs <;> positivity
  · have! this : 0 ≤ ∑ l : Fin 4,
        (if A.uslot p = some l then 2 * (4 * E * dyadicGridLength A.G A.R.1)
        else 2 * ((S.K : ℝ) * (20 * Real.exp ((4096 * (cc + 1) * (1024 * (cc + 1) + cc + 7) +
          cc ^ 2 + 3) * (1 + Real.log (2 * (k : ℝ))) ^ 2) + 32) * dyadicGridLength A.G A.R.1) +
        2 * ((S.K : ℝ) * (Vl0 * dyadicGridLength A.G A.R.1))) :=
      Finset.sum_nonneg fun l _ => by split_ifs <;> positivity
    positivity

open Classical in
/-- Step `h3pow` of `leaf_estimate`, over the part of its context that it uses. -/
theorem leaf_estimate_h3pow :
    ∀ (S : ModeSchedule), (0 : ℝ) < S.Dstar → (1 : ℝ) ≤ S.Dstar →
      √((4 : ℝ) * S.Dstar ^ (2 : ℕ) * (1 : ℝ)) = (2 : ℝ) * S.Dstar → √S.Dstar ^ (2 : ℕ) = S.Dstar →
      (1 : ℝ) ≤ √S.Dstar →
    (S.Dstar * (Real.sqrt S.Dstar * Real.sqrt (4 * S.Dstar ^ 2 * 1) + 1)) ^ 4 ≤
    81 * S.Dstar ^ 10 := by
  intro S hD0 hD1 hsq hsD hsD1
  rw [hsq]
  have! h1 : Real.sqrt S.Dstar * (2 * S.Dstar) + 1 ≤ 3 * (Real.sqrt S.Dstar * S.Dstar) := by
    nlinarith only [hsD1, hD1]
  have! h0 : 0 ≤ S.Dstar * (Real.sqrt S.Dstar * (2 * S.Dstar) + 1) := by positivity
  calc _ ≤ (S.Dstar * (3 * (Real.sqrt S.Dstar * S.Dstar))) ^ 4 :=
        pow_le_pow_left₀ h0 (mul_le_mul_of_nonneg_left h1 hD0.le) 4
    _ = 81 * S.Dstar ^ 8 * (Real.sqrt S.Dstar ^ 2) ^ 2 := by ring
    _ = _ := by rw [hsD]; ring

open Classical in
/-- Step `hQe0` of `leaf_estimate`, over the part of its context that it uses. -/
theorem leaf_estimate_hQe0 :
    ∀ (κ : LocalKernelClass) (S : ModeSchedule), (2 : ℝ) ≤ S.Dstar → ∀ (U : ℝ), (16 : ℝ) ≤ U →
      ∀ (ε : ℝ), (0 : ℝ) < ε →
    let Iw : ℕ := ⌊Real.logb (2 : ℝ) (S.Dstar ^ (250 : ℕ))⌋₊;
    let ι : ℝ := (S.Dstar ^ (100 : ℕ))⁻¹ * S.Dstar ^ (10 : ℕ);
    let Qe : ℝ := (16 : ℝ) * fourErrC κ (3 : ℕ) * ι + K1c * ((2 : ℝ) * fourKC κ (3 : ℕ) *
        (12 : ℝ) ^ (4 : ℕ) * ε * U ^ (3 : ℕ) * S.Dstar ^ (4 : ℕ)) + (4 : ℝ) * ((81 : ℝ) *
        threeErrC κ (3 : ℕ) (1 : ℕ) * ι * U + K1c * ((8 : ℝ) * entryCU κ (3 : ℕ) (1 : ℕ) *
        (2 : ℝ) ^ ((1 : ℕ) + (4 : ℕ)) * (12 : ℝ) ^ (3 : ℕ) * ε * U ^ (3 : ℕ) * (S.Dstar ^
        (3 : ℕ) * ((↑Iw : ℝ) + (1 : ℝ)))));
    Qe = (16 : ℝ) * fourErrC κ (3 : ℕ) * ι + K1c * ((2 : ℝ) * fourKC κ (3 : ℕ) * (12 : ℝ) ^
        (4 : ℕ) * ε * U ^ (3 : ℕ) * S.Dstar ^ (4 : ℕ)) + (4 : ℝ) * ((81 : ℝ) * threeErrC κ (3 : ℕ)
        (1 : ℕ) * ι * U + K1c * ((8 : ℝ) * entryCU κ (3 : ℕ) (1 : ℕ) * (2 : ℝ) ^ ((1 : ℕ) +
        (4 : ℕ)) * (12 : ℝ) ^ (3 : ℕ) * ε * U ^ (3 : ℕ) * (S.Dstar ^ (3 : ℕ) * ((↑Iw : ℝ) +
        (1 : ℝ))))) →
    0 ≤ Qe := by
  intro κ S hD2 U hU16 ε hε0 Iw ι Qe hQe
  rw [hQe]
  have! this := fourErrC_nonneg κ 3; have := threeErrC_nonneg κ 3 1; have := fourKC_nonneg κ 3
  have! this := entryCU_nonneg' κ 3 1; have := K1c_pos
  positivity

open Classical in
/-- Step `hCjg1` of `leaf_estimate`, over the part of its context that it uses. -/
theorem leaf_estimate_hCjg1 :
    ∀ (κ : LocalKernelClass) (c₀ : ℕ) (cc : ℕ) (A : ActiveSetup κ c₀) (k : ℕ),
    let Cjg : ℝ := ((↑((2 : ℕ) * A.famFuel + (2 : ℕ)) : ℝ) + (1 : ℝ)) ^ (2 : ℕ) * Real.exp
        ((2 : ℝ) * ((1024 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) * ((1024 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) +
        (↑cc : ℝ) + (7 : ℝ)) * ((1 : ℝ) + Real.log ((2 : ℝ) * (↑k : ℝ))) ^ (2 : ℕ)));
    Cjg = ((↑((2 : ℕ) * A.famFuel + (2 : ℕ)) : ℝ) + (1 : ℝ)) ^ (2 : ℕ) * Real.exp ((2 : ℝ) *
        ((1024 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) * ((1024 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) + (↑cc : ℝ) +
        (7 : ℝ)) * ((1 : ℝ) + Real.log ((2 : ℝ) * (↑k : ℝ))) ^ (2 : ℕ))) →
    1 ≤ Cjg := by
  intro κ c₀ cc A k Cjg hCjg
  rw [hCjg]
  have! h0 := Nat.cast_nonneg (α := ℝ) (2 * A.famFuel + 2)
  exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by linarith only [h0]))
    (Real.one_le_exp (by positivity))

open Classical in
/-- Step `hΓa0` of `leaf_estimate`, over the part of its context that it uses. -/
theorem leaf_estimate_hΓa0 :
    ∀ (κ : LocalKernelClass) (c₀ : ℕ) (cc : ℕ) (A : ActiveSetup κ c₀) (k : ℕ) (E : ℝ)
      (S : ModeSchedule) (Vl0 : ℝ),
    let Nb : ℕ := Nat.log (2 : ℕ) S.K + (1 : ℕ);
    (0 : ℝ) ≤ Vl0 →
    let Os : Finset (Fin (4 : ℕ) × Fin (4 : ℕ) × ℕ × ℕ × ℕ × ℕ) := FamParams.SideLeafM.nOs
        ((2 : ℕ) ^ A.famFuel) ((2 : ℕ) * A.famFuel + (2 : ℕ));
    let Cjg : ℝ := ((↑((2 : ℕ) * A.famFuel + (2 : ℕ)) : ℝ) + (1 : ℝ)) ^ (2 : ℕ) * Real.exp
        ((2 : ℝ) * ((1024 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) * ((1024 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) +
        (↑cc : ℝ) + (7 : ℝ)) * ((1 : ℝ) + Real.log ((2 : ℝ) * (↑k : ℝ))) ^ (2 : ℕ)));
    let Γa : Fin (4 : ℕ) → ℝ := fun (_ : Fin (4 : ℕ)) ↦ (↑Os.card : ℝ) * ((↑Nb : ℝ) * ((2 : ℝ) *
        FamParams.capV A cc (↑k : ℝ) + (16 : ℝ) * (Cjg * FamParams.SideInput.sideB0 A cc (↑k : ℝ)
        Vl0) + (16 : ℝ) * ((↑Nb : ℝ) * (Cjg * ((↑Nb : ℝ) * FamParams.capV A cc (↑k : ℝ))))) +
        FamParams.SideInput.sideB0 A cc (↑k : ℝ) Vl0) / dyadicGridLength A.G A.R.1;
    let G0e : ℝ := Real.exp (((4096 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) * ((1024 : ℝ) * ((↑cc : ℝ) +
        (1 : ℝ)) + (↑cc : ℝ) + (7 : ℝ)) + (↑cc : ℝ) ^ (2 : ℕ) + (3 : ℝ)) * ((1 : ℝ) + Real.log
        ((2 : ℝ) * (↑k : ℝ))) ^ (2 : ℕ));
    (1 : ℝ) ≤ G0e →
    let W : ℝ := G0e + Vl0 + E + (1 : ℝ);
    (1 : ℝ) ≤ W →
    let n : ℝ := (↑Nb : ℝ);
    (Γa = fun (_ : Fin (4 : ℕ)) ↦ (↑Os.card : ℝ) * (n * ((2 : ℝ) * FamParams.capV A cc (↑k : ℝ) +
        (16 : ℝ) * (Cjg * FamParams.SideInput.sideB0 A cc (↑k : ℝ) Vl0) + (16 : ℝ) * (n * (Cjg *
        (n * FamParams.capV A cc (↑k : ℝ))))) + FamParams.SideInput.sideB0 A cc (↑k : ℝ) Vl0) /
        dyadicGridLength A.G A.R.1) →
    let P3 : ℝ := n ^ (3 : ℕ) * Cjg;
    P3 = n ^ (3 : ℕ) * Cjg → (1 : ℝ) ≤ P3 → n ≤ P3 → n * Cjg ≤ P3 → (0 : ℝ) ≤ (↑Os.card : ℝ) →
      FamParams.capV A cc (↑k : ℝ) = G0e * ((4 : ℝ) * dyadicGridLength A.G A.R.1) →
      FamParams.SideInput.sideB0 A cc (↑k : ℝ) Vl0 = (2 : ℝ) * (((20 : ℝ) * G0e + (32 : ℝ)) *
        dyadicGridLength A.G A.R.1) + (2 : ℝ) * (Vl0 * dyadicGridLength A.G A.R.1) →
      dyadicGridLength A.G A.R.1 ≠ (0 : ℝ) → G0e ≤ W →
      (40 : ℝ) * G0e + (64 : ℝ) + (2 : ℝ) * Vl0 ≤ (106 : ℝ) * W →
    Γa 0 ≤ 1874 * Os.card * P3 * W := by
  intro κ c₀ cc A k E S Vl0 Nb hVl00 Os Cjg Γa G0e hG0e1 W hW1 n hΓadef P3 hP3 hP31 hnP3 hnCP3
    hOs0 hcapV hsideB hR0 hG0W hsB
  have! e : Γa 0 = Os.card * (n * (8 * G0e + 16 * Cjg * (40 * G0e + 64 + 2 * Vl0) +
      64 * n ^ 2 * Cjg * G0e) + (40 * G0e + 64 + 2 * Vl0)) := by
    simp only [hΓadef, hcapV, hsideB]
    rw [div_eq_iff hR0]
    ring
  rw [e]
  have! h1 : n * (8 * G0e) ≤ 8 * (P3 * W) := by
    have! this := mul_le_mul hnP3 hG0W (by linarith only [hG0e1]) (by linarith only [hP31])
    linarith only [this]
  have! h2 : n * (16 * Cjg * (40 * G0e + 64 + 2 * Vl0)) ≤ 1696 * (P3 * W) := by
    have! h3 : n * Cjg * (40 * G0e + 64 + 2 * Vl0) ≤ P3 * (106 * W) :=
      mul_le_mul hnCP3 hsB (by positivity) (by linarith only [hP31])
    nlinarith only [h3]
  have! h4 : n * (64 * n ^ 2 * Cjg * G0e) ≤ 64 * (P3 * W) := by
    have! this : n * (64 * n ^ 2 * Cjg * G0e) = 64 * (P3 * G0e) := by rw [hP3]; ring
    rw [this]
    have! this := mul_le_mul_of_nonneg_left hG0W (show 0 ≤ P3 by linarith only [hP31])
    linarith only [this]
  have! h5 : 40 * G0e + 64 + 2 * Vl0 ≤ 106 * (P3 * W) := by
    have! this := mul_le_mul_of_nonneg_right hP31 (show 0 ≤ W by linarith only [hW1])
    linarith only [hsB, this]
  have! h6 : n * (8 * G0e + 16 * Cjg * (40 * G0e + 64 + 2 * Vl0) + 64 * n ^ 2 * Cjg * G0e) +
      (40 * G0e + 64 + 2 * Vl0) ≤ 1874 * (P3 * W) := by
    have! this : n * (8 * G0e + 16 * Cjg * (40 * G0e + 64 + 2 * Vl0) + 64 * n ^ 2 * Cjg * G0e) =
        n * (8 * G0e) + n * (16 * Cjg * (40 * G0e + 64 + 2 * Vl0)) +
          n * (64 * n ^ 2 * Cjg * G0e) := by ring
    rw [this]; linarith only [h1, h2, h4, h5]
  calc _ ≤ (Os.card : ℝ) * (1874 * (P3 * W)) := mul_le_mul_of_nonneg_left h6 hOs0
    _ = _ := by ring

open Classical in
/-- Step `hΓb0` of `leaf_estimate`, over the part of its context that it uses. -/
theorem leaf_estimate_hΓb0 :
    ∀ (κ : LocalKernelClass) (c₀ : ℕ) (cc : ℕ) (A : ActiveSetup κ c₀) (k : ℕ) (E : ℝ)
      (S : ModeSchedule) (Vl0 : ℝ),
    let Nb : ℕ := Nat.log (2 : ℕ) S.K + (1 : ℕ);
    let Os : Finset (Fin (4 : ℕ) × Fin (4 : ℕ) × ℕ × ℕ × ℕ × ℕ) := FamParams.SideLeafM.nOs
        ((2 : ℕ) ^ A.famFuel) ((2 : ℕ) * A.famFuel + (2 : ℕ));
    let Cjg : ℝ := ((↑((2 : ℕ) * A.famFuel + (2 : ℕ)) : ℝ) + (1 : ℝ)) ^ (2 : ℕ) * Real.exp
        ((2 : ℝ) * ((1024 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) * ((1024 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) +
        (↑cc : ℝ) + (7 : ℝ)) * ((1 : ℝ) + Real.log ((2 : ℝ) * (↑k : ℝ))) ^ (2 : ℕ)));
    let Γb : Fin (4 : ℕ) → ℝ := fun (_ : Fin (4 : ℕ)) ↦ (↑Os.card : ℝ) * ((↑Nb : ℝ) *
        FamParams.capV A cc (↑k : ℝ) + FamParams.SideInput.sideB0 A cc (↑k : ℝ) Vl0) /
        dyadicGridLength A.G A.R.1;
    let G0e : ℝ := Real.exp (((4096 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) * ((1024 : ℝ) * ((↑cc : ℝ) +
        (1 : ℝ)) + (↑cc : ℝ) + (7 : ℝ)) + (↑cc : ℝ) ^ (2 : ℕ) + (3 : ℝ)) * ((1 : ℝ) + Real.log
        ((2 : ℝ) * (↑k : ℝ))) ^ (2 : ℕ));
    (1 : ℝ) ≤ G0e →
    let W : ℝ := G0e + Vl0 + E + (1 : ℝ);
    (1 : ℝ) ≤ W →
    let n : ℝ := (↑Nb : ℝ);
    (Γb = fun (_ : Fin (4 : ℕ)) ↦ (↑Os.card : ℝ) * (n * FamParams.capV A cc (↑k : ℝ) +
        FamParams.SideInput.sideB0 A cc (↑k : ℝ) Vl0) / dyadicGridLength A.G A.R.1) →
    let P3 : ℝ := n ^ (3 : ℕ) * Cjg;
    (1 : ℝ) ≤ P3 → n ≤ P3 → (0 : ℝ) ≤ (↑Os.card : ℝ) →
      FamParams.capV A cc (↑k : ℝ) = G0e * ((4 : ℝ) * dyadicGridLength A.G A.R.1) →
      FamParams.SideInput.sideB0 A cc (↑k : ℝ) Vl0 = (2 : ℝ) * (((20 : ℝ) * G0e + (32 : ℝ)) *
        dyadicGridLength A.G A.R.1) + (2 : ℝ) * (Vl0 * dyadicGridLength A.G A.R.1) →
      dyadicGridLength A.G A.R.1 ≠ (0 : ℝ) → G0e ≤ W →
      (40 : ℝ) * G0e + (64 : ℝ) + (2 : ℝ) * Vl0 ≤ (106 : ℝ) * W →
    Γb 0 ≤ 110 * Os.card * P3 * W := by
  intro κ c₀ cc A k E S Vl0 Nb Os Cjg Γb G0e hG0e1 W hW1 n hΓbdef P3 hP31 hnP3 hOs0 hcapV hsideB
    hR0 hG0W hsB
  have! e : Γb 0 = Os.card * (n * (4 * G0e) + (40 * G0e + 64 + 2 * Vl0)) := by
    simp only [hΓbdef, hcapV, hsideB]
    rw [div_eq_iff hR0]
    ring
  rw [e]
  have! h1 : n * (4 * G0e) ≤ 4 * (P3 * W) := by
    have! this := mul_le_mul hnP3 hG0W (by linarith only [hG0e1]) (by linarith only [hP31])
    linarith only [this]
  have! h5 : 40 * G0e + 64 + 2 * Vl0 ≤ 106 * (P3 * W) := by
    have! this := mul_le_mul_of_nonneg_right hP31 (show 0 ≤ W by linarith only [hW1])
    linarith only [hsB, this]
  calc _ ≤ (Os.card : ℝ) * (110 * (P3 * W)) :=
        mul_le_mul_of_nonneg_left (by linarith only [h1, h5]) hOs0
    _ = _ := by ring

open Classical in
/-- Step `hΓa00` of `leaf_estimate`, over the part of its context that it uses. -/
theorem leaf_estimate_hΓa00 :
    ∀ (κ : LocalKernelClass) (c₀ : ℕ) (cc : ℕ) (A : ActiveSetup κ c₀) (k : ℕ) (S : ModeSchedule)
      (Vl0 : ℝ),
    let Nb : ℕ := Nat.log (2 : ℕ) S.K + (1 : ℕ);
    (0 : ℝ) < dyadicGridLength A.G A.R.1 → (0 : ℝ) ≤ Vl0 →
    let Os : Finset (Fin (4 : ℕ) × Fin (4 : ℕ) × ℕ × ℕ × ℕ × ℕ) := FamParams.SideLeafM.nOs
        ((2 : ℕ) ^ A.famFuel) ((2 : ℕ) * A.famFuel + (2 : ℕ));
    let Cjg : ℝ := ((↑((2 : ℕ) * A.famFuel + (2 : ℕ)) : ℝ) + (1 : ℝ)) ^ (2 : ℕ) * Real.exp
        ((2 : ℝ) * ((1024 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) * ((1024 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) +
        (↑cc : ℝ) + (7 : ℝ)) * ((1 : ℝ) + Real.log ((2 : ℝ) * (↑k : ℝ))) ^ (2 : ℕ)));
    let Γa : Fin (4 : ℕ) → ℝ := fun (_ : Fin (4 : ℕ)) ↦ (↑Os.card : ℝ) * ((↑Nb : ℝ) * ((2 : ℝ) *
        FamParams.capV A cc (↑k : ℝ) + (16 : ℝ) * (Cjg * FamParams.SideInput.sideB0 A cc (↑k : ℝ)
        Vl0) + (16 : ℝ) * ((↑Nb : ℝ) * (Cjg * ((↑Nb : ℝ) * FamParams.capV A cc (↑k : ℝ))))) +
        FamParams.SideInput.sideB0 A cc (↑k : ℝ) Vl0) / dyadicGridLength A.G A.R.1;
    let G0e : ℝ := Real.exp (((4096 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) * ((1024 : ℝ) * ((↑cc : ℝ) +
        (1 : ℝ)) + (↑cc : ℝ) + (7 : ℝ)) + (↑cc : ℝ) ^ (2 : ℕ) + (3 : ℝ)) * ((1 : ℝ) + Real.log
        ((2 : ℝ) * (↑k : ℝ))) ^ (2 : ℕ));
    let n : ℝ := (↑Nb : ℝ);
    (Γa = fun (_ : Fin (4 : ℕ)) ↦ (↑Os.card : ℝ) * (n * ((2 : ℝ) * FamParams.capV A cc (↑k : ℝ) +
        (16 : ℝ) * (Cjg * FamParams.SideInput.sideB0 A cc (↑k : ℝ) Vl0) + (16 : ℝ) * (n * (Cjg *
        (n * FamParams.capV A cc (↑k : ℝ))))) + FamParams.SideInput.sideB0 A cc (↑k : ℝ) Vl0) /
        dyadicGridLength A.G A.R.1) → (0 : ℝ) ≤ (↑Os.card : ℝ) →
      FamParams.capV A cc (↑k : ℝ) = G0e * ((4 : ℝ) * dyadicGridLength A.G A.R.1) →
      FamParams.SideInput.sideB0 A cc (↑k : ℝ) Vl0 = (2 : ℝ) * (((20 : ℝ) * G0e + (32 : ℝ)) *
        dyadicGridLength A.G A.R.1) + (2 : ℝ) * (Vl0 * dyadicGridLength A.G A.R.1) →
    0 ≤ Γa 0 := by
  intro κ c₀ cc A k S Vl0 Nb hRl0 hVl00 Os Cjg Γa G0e n hΓadef hOs0 hcapV hsideB
  simp only [hΓadef, hcapV, hsideB]
  exact div_nonneg (mul_nonneg hOs0 (by positivity)) hRl0.le

open Classical in
/-- Step `hΓb00` of `leaf_estimate`, over the part of its context that it uses. -/
theorem leaf_estimate_hΓb00 :
    ∀ (κ : LocalKernelClass) (c₀ : ℕ) (cc : ℕ) (A : ActiveSetup κ c₀) (k : ℕ) (S : ModeSchedule)
      (Vl0 : ℝ),
    let Nb : ℕ := Nat.log (2 : ℕ) S.K + (1 : ℕ);
    (0 : ℝ) < dyadicGridLength A.G A.R.1 → (0 : ℝ) ≤ Vl0 →
    let Os : Finset (Fin (4 : ℕ) × Fin (4 : ℕ) × ℕ × ℕ × ℕ × ℕ) := FamParams.SideLeafM.nOs
        ((2 : ℕ) ^ A.famFuel) ((2 : ℕ) * A.famFuel + (2 : ℕ));
    let Γb : Fin (4 : ℕ) → ℝ := fun (_ : Fin (4 : ℕ)) ↦ (↑Os.card : ℝ) * ((↑Nb : ℝ) *
        FamParams.capV A cc (↑k : ℝ) + FamParams.SideInput.sideB0 A cc (↑k : ℝ) Vl0) /
        dyadicGridLength A.G A.R.1;
    let G0e : ℝ := Real.exp (((4096 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) * ((1024 : ℝ) * ((↑cc : ℝ) +
        (1 : ℝ)) + (↑cc : ℝ) + (7 : ℝ)) + (↑cc : ℝ) ^ (2 : ℕ) + (3 : ℝ)) * ((1 : ℝ) + Real.log
        ((2 : ℝ) * (↑k : ℝ))) ^ (2 : ℕ));
    let n : ℝ := (↑Nb : ℝ);
    (Γb = fun (_ : Fin (4 : ℕ)) ↦ (↑Os.card : ℝ) * (n * FamParams.capV A cc (↑k : ℝ) +
        FamParams.SideInput.sideB0 A cc (↑k : ℝ) Vl0) / dyadicGridLength A.G A.R.1) →
      (0 : ℝ) ≤ (↑Os.card : ℝ) →
      FamParams.capV A cc (↑k : ℝ) = G0e * ((4 : ℝ) * dyadicGridLength A.G A.R.1) →
      FamParams.SideInput.sideB0 A cc (↑k : ℝ) Vl0 = (2 : ℝ) * (((20 : ℝ) * G0e + (32 : ℝ)) *
        dyadicGridLength A.G A.R.1) + (2 : ℝ) * (Vl0 * dyadicGridLength A.G A.R.1) →
    0 ≤ Γb 0 := by
  intro κ c₀ cc A k S Vl0 Nb hRl0 hVl00 Os Γb G0e n hΓbdef hOs0 hcapV hsideB
  simp only [hΓbdef, hcapV, hsideB]
  exact div_nonneg (mul_nonneg hOs0 (by positivity)) hRl0.le

open Classical in
/-- Step `hΓU00` of `leaf_estimate`, over the part of its context that it uses. -/
theorem leaf_estimate_hΓU00 :
    ∀ (κ : LocalKernelClass) (c₀ : ℕ) (A : ActiveSetup κ c₀) (E : ℝ),
      (0 : ℝ) < dyadicGridLength A.G A.R.1 →
    let Os : Finset (Fin (4 : ℕ) × Fin (4 : ℕ) × ℕ × ℕ × ℕ × ℕ) := FamParams.SideLeafM.nOs
        ((2 : ℕ) ^ A.famFuel) ((2 : ℕ) * A.famFuel + (2 : ℕ));
    let ΓU : ℝ := (↑Os.card : ℝ) * ((2 : ℝ) * ((4 : ℝ) * E * dyadicGridLength A.G A.R.1)) /
        dyadicGridLength A.G A.R.1;
    ΓU = (↑Os.card : ℝ) * ((2 : ℝ) * ((4 : ℝ) * E * dyadicGridLength A.G A.R.1)) /
        dyadicGridLength A.G A.R.1 → (0 : ℝ) ≤ E → (0 : ℝ) ≤ (↑Os.card : ℝ) →
    0 ≤ ΓU := by
  intro κ c₀ A E hRl0 Os ΓU hΓUdef hE0 hOs0
  rw [hΓUdef]
  exact div_nonneg (mul_nonneg hOs0 (by positivity)) hRl0.le

open Classical in
/-- Step `hprin` of `leaf_estimate`, over the part of its context that it uses. -/
theorem leaf_estimate_hprin :
    ∀ (κ : LocalKernelClass) (c₀ : ℕ) (Dm0 : ℕ) (A : ActiveSetup κ c₀) (bf : A.BasicFamilies)
      (p : Fin (3 : ℕ)) (AD : bf.AttemptData p) (d : bf.Vtx) (s : ℕ) (δ : ℝ) (ρ : ℝ) (kD : ℝ),
      (0 : ℝ) < δ → δ ≤ (1 / 8 : ℝ) → (0 : ℝ) < ρ →
    let fp : bf.FamParams := AD.fp;
    let dB : ℕ := A.dBnd;
    (8 : ℝ) * (↑dB : ℝ) * δ ≤ (1 : ℝ) →
    let Nl : ℝ := AD.n (fp.Lc + (5 : ℕ));
    ∀ (hNl0 : (0 : ℝ) ≤ Nl),
    let Hm : ℝ := max (max A.Hsrc (Real.exp (↑dB : ℝ))) (max ((5832 : ℝ) * max A.H padW ^ (4 : ℕ))
        ((↑dB : ℝ) * (bumpConst * (8 : ℝ) ^ (32 : ℕ) * ((2 : ℝ) / δ))));
    (1 : ℝ) ≤ Hm → (∀ (w : bf.Vtx), (bf.vtag w).dim ≤ dB) →
      (∀ (w : bf.Vtx) (a c : Fin (bf.vtag w).dim), (↑(rationalHeight ((bf.vtag w).C a c)) : ℝ) ≤
        fp.Hed) → ∀ (S : ModeSchedule), S.dmax = (2 : ℕ) * dB + (2 : ℕ) →
      (↑S.Q0 : ℝ) * (2 : ℝ) ^ (fp.Kstar Dm0 dB Hm δ Nl kD δ + (1 : ℕ)) ≤ S.Bstar →
      ∀ (hK1 : (1 : ℕ) ≤ S.K),
    let Lf : SearchLeaf := leafAt A.famFuel fp.Lc (A.basicSlot p) s;
    let ks : ℕ := Lf.k;
    let S0 : Finset (ℤ × ℤ) := {I ∈ AD.Tc | ¬∃ c ∈ fp.failRoots, dyadicGridCell A.G I.1 I.2 ⊆
        dyadicGridCell A.G c.1 c.2};
    let gs : ℤ × ℤ → Finset bf.Grp := fun (I : ℤ × ℤ) ↦ fp.groupsAt I ks;
    let gset : Finset bf.Grp := S0.biUnion gs;
    ∀ (hlenMc : ∀ (l : Fin (4 : ℕ)), (AD.cat l).length ≤ fp.Mc),
    let mbs : (l : Fin (4 : ℕ)) → bf.MainBudget (AD.cat l) := fun (l : Fin (4 : ℕ)) ↦
        MainBudget.ofCounts bf fp.Mc (AD.cat l) (hlenMc l) l (fun (e : CatCol bf.Vtx) (he : e ∈
        AD.cat l) ↦ AD.hTc (AD.hT l e he).left) (fun (e : CatCol bf.Vtx) (he : e ∈ AD.cat l) ↦
        (AD.hT l e he).right.left) hNl0 fun (I : ℤ × ℤ) (_ : I ∈ A.cells) ↦ AD.hlab l I
        (AD.fp.Lc + (5 : ℕ)) le_rfl;
    ∀ (Ms : Fin (4 : ℕ) → bf.Grp → ModeSystem A.G (Fintype.card (bf.Lab ⊕ Fin fp.Mc))),
      S.Dstar = fp.modeStarG Dm0 dB Hm δ Nl kD δ →
      (∀ (l : Fin (4 : ℕ)), ∀ G ∈ gset, (∀ (q : (Ms l G).Key), (Ms l G).dvOf q + (Ms l G).zc.dim ≤
        (2 : ℕ) * dB + (2 : ℕ)) ∧ (Ms l G).Λ ≤ S.Dstar ∧ gaugeSqNorm (Ms l G).zc.dim (Ms l G).δc ≤
        S.Dstar ∧ (2 : ℝ) * gaugeTail (Ms l G).zc.dim (Ms l G).δc / (2 : ℝ) ^ fp.Kstar Dm0 dB Hm δ
        Nl kD δ * S.Dstar ^ (300 : ℕ) ≤ (1 : ℝ) ∧ (∀ (m : (Ms l G).Md), S.Dstar⁻¹ ≤ (Ms l G).L.εM
        m) ∧ (∀ (V : ℤ × ℤ), (↑((Ms l G).alive V).card : ℝ) ≤ S.Dstar) ∧ ∀ (V : ℤ × ℤ),
        (↑(Finset.image (Ms l G).keyOf ((Ms l G).alive V)).card : ℝ) ≤ Nl) →
      ∀ (hA6 : (6 : ℝ) ≤ S.A0),
    let qG : bf.Grp → ℕ := fun (G : bf.Grp) ↦ clearInt (bf.vtag (bf.grpCenter d G)).C;
    (∀ (G : bf.Grp), (1 : ℕ) ≤ qG G ∧ qG G ≤ S.Q0) →
      ∀ (c : (l : Fin (4 : ℕ)) → (G : ↥gset) → ℤ → ℤ × ℤ → (Ms l (↑G : bf.Grp)).Md → ℂ),
    let cf : (l : Fin (4 : ℕ)) → (G : bf.Grp) → ℤ → ℤ × ℤ → (Ms l G).Md → ℂ := fun (l : Fin
        (4 : ℕ)) (G : bf.Grp) ↦ if hG : G ∈ gset then c l ⟨G, hG⟩ else fun (_ : ℤ) (_ : ℤ × ℤ)
        (_ : (Ms l G).Md) ↦ (0 : ℂ);
    let D₀ : fp.SideInput :=
      { cat := AD.cat, mbs := mbs, Lf := Lf, u := A.uslot p, S := S, hA := hA6, SP := S.sideParams
          (1 / 1024 : ℝ), hK := hK1, n := Fintype.card (bf.Lab ⊕ Fin fp.Mc), Ms := Ms, c := cf };
    ∀ (hcat : Fin (4 : ℕ) → List (CatCol bf.Vtx))
      (hmbb : ∀ (l : Fin (4 : ℕ)), ∀ e ∈ AD.cat l ++ hcat l, e.birth ∈ A.cells)
      (hmbT : ∀ (l : Fin (4 : ℕ)) (y : ℝ), (8 : ℝ) * A.colBudget + (↑(bf.tmplPath (AD.cat l ++
        hcat l) y) : ℝ) ≤ (8 : ℝ) * A.colBudget + ((1 : ℝ) + (↑AD.Mp : ℝ)) * Nl),
    let mb' : (l : Fin (4 : ℕ)) → bf.MainBudget (AD.cat l ++ hcat l) :=
      fun (l : Fin (4 : ℕ)) ↦ { hb := hmbb l, B := (8 : ℝ) * A.colBudget + ((1 : ℝ) + (↑AD.Mp :
                                  ℝ)) * Nl, hTp := hmbT l };
    let D : fp.SideInput := D₀.appendCat hcat mb';
    (∀ (l : Fin (4 : ℕ)), ∀ G ∈ gset, (Ms l G).zc = bf.vtag (bf.grpCenter d G)) →
      (∀ (l : Fin (4 : ℕ)), ∀ G ∈ gset, (Ms l G).δc = δ ∧ (Ms l G).cl = slotCoeff l ∧ ∀ (i : Fin
        (Ms l G).zc.dim), (Ms l G).ρ i ∈ Set.Icc (0 : ℝ) (1 : ℝ)) → (1 : ℕ) ≤ dB →
    ∀ G ∈ gset, (D.withQ0 (qG G)).PrinOK G δ fp.Hed (fp.Kstar Dm0 dB Hm δ Nl kD δ)
    (fp.Kstar Dm0 dB Hm δ Nl kD δ) := by
  intro κ c₀ Dm0 A bf p AD d s δ ρ kD hδ hδ8 hρ fp dB hdδ Nl hNl0 Hm hHm1 hdim hC S hSd hbox hK1
    Lf ks S0 gs gset hlenMc mbs Ms hDS hsch' hA6 qG hqG1 c cf D₀ hcat hmbb hmbT mb' D hzc hgrpE
    hdB1 G hG
  have! hcp := fp.center_principal_bounds Dm0 dB kD hδ (le_trans hδ8 (by norm_num)) AD.hHed2
    hHm1 hδ hNl0 hdB1 hdim hC (bf.grpCenter d G)
  rw [← hDS] at hcp
  obtain ⟨hMN, hτm, hCN, hτc, hCm, hQC⟩ := hcp
  have! hz0 := hzc 0 G hG
  have hz0' : ((D.withQ0 (qG G)).Ms 0 G).zc = bf.vtag (bf.grpCenter d G) := hz0
  have hz0'' : (D.Ms 0 G).zc = bf.vtag (bf.grpCenter d G) := hz0
  have! hdimz := hdim (bf.grpCenter d G)
  have! hqS : (qG G : ℝ) ≤ S.Q0 := by exact_mod_cast (hqG1 G).2
  have! hQB : (qG G : ℝ) * 2 ^ (fp.Kstar Dm0 dB Hm δ Nl kD δ + 1) ≤ S.Bstar :=
    le_trans (mul_le_mul_of_nonneg_right hqS (by positivity)) hbox
  exact
    { hz := fun j => (hzc j G hG).trans hz0.symm
      hdim := by
        change (D.Ms 0 G).zc.dim ≤ S.dmax
        rw [hz0'', hSd]
        omega
      hδ := hδ
      hdδ := by
        rw [hz0']
        have! this : (8 : ℝ) * (bf.vtag (bf.grpCenter d G)).dim * δ ≤ 8 * dB * δ := by
          have! this : ((bf.vtag (bf.grpCenter d G)).dim : ℝ) ≤ dB := by exact_mod_cast hdimz
          gcongr
        exact this.trans hdδ
      hδ8 := hδ8
      hδc := fun j => (hgrpE j G hG).1
      hcl := fun j => (hgrpE j G hG).2.1
      hρ := fun j i => (hgrpE j G hG).2.2 i
      hQC := by rw [hz0']; exact hQC
      hCm0 := le_trans (by norm_num) AD.hHed2
      hCm := by rw [hz0']; exact hCm
      hQB := hQB
      hτc := by rw [hz0']; exact hτc
      hτm := by rw [hz0']; exact hτm
      hMN := by rw [hz0']; exact hMN
      hCN := by rw [hz0']; exact hCN
      hDg := fun j => (hsch' j G hG).2.2.1
      hKf := fun j => (hsch' j G hG).2.2.2.1
      hQBf := hQB
      hεw := fun j m => (hsch' j G hG).2.2.2.2.1 m
      hΛ := fun j => (hsch' j G hG).2.1 }

open Classical in
/-- Step `hUD` of `leaf_estimate`, over the part of its context that it uses. -/
theorem leaf_estimate_hUD :
    ∀ (κ : LocalKernelClass) (c₀ : ℕ) (cc : ℕ), (1 : ℕ) ≤ cc → ∀ (Dm0 : ℕ) (A : ActiveSetup κ c₀)
      (bf : A.BasicFamilies) (p : Fin (3 : ℕ)) (AD : bf.AttemptData p) (d : bf.Vtx) (s : ℕ) (δ : ℝ)
      (kD : ℝ),
    let fp : bf.FamParams := AD.fp;
    let dB : ℕ := A.dBnd;
    let Nl : ℝ := AD.n (fp.Lc + (5 : ℕ));
    (2 : ℝ) ≤ A.colBudget → ∀ (hNl0 : (0 : ℝ) ≤ Nl),
    let Hm : ℝ := max (max A.Hsrc (Real.exp (↑dB : ℝ))) (max ((5832 : ℝ) * max A.H padW ^ (4 : ℕ))
        ((↑dB : ℝ) * (bumpConst * (8 : ℝ) ^ (32 : ℕ) * ((2 : ℝ) / δ))));
    ∀ (S : ModeSchedule) (hK1 : (1 : ℕ) ≤ S.K),
    let Lf : SearchLeaf := leafAt A.famFuel fp.Lc (A.basicSlot p) s;
    let ks : ℕ := Lf.k;
    let S0 : Finset (ℤ × ℤ) := {I ∈ AD.Tc | ¬∃ c ∈ fp.failRoots, dyadicGridCell A.G I.1 I.2 ⊆
        dyadicGridCell A.G c.1 c.2};
    let gs : ℤ × ℤ → Finset bf.Grp := fun (I : ℤ × ℤ) ↦ fp.groupsAt I ks;
    let gset : Finset bf.Grp := S0.biUnion gs;
    ∀ (hlenMc : ∀ (l : Fin (4 : ℕ)), (AD.cat l).length ≤ fp.Mc),
    let mbs : (l : Fin (4 : ℕ)) → bf.MainBudget (AD.cat l) := fun (l : Fin (4 : ℕ)) ↦
        MainBudget.ofCounts bf fp.Mc (AD.cat l) (hlenMc l) l (fun (e : CatCol bf.Vtx) (he : e ∈
        AD.cat l) ↦ AD.hTc (AD.hT l e he).left) (fun (e : CatCol bf.Vtx) (he : e ∈ AD.cat l) ↦
        (AD.hT l e he).right.left) hNl0 fun (I : ℤ × ℤ) (_ : I ∈ A.cells) ↦ AD.hlab l I
        (AD.fp.Lc + (5 : ℕ)) le_rfl;
    ∀ (Ms : Fin (4 : ℕ) → bf.Grp → ModeSystem A.G (Fintype.card (bf.Lab ⊕ Fin fp.Mc)))
      (L : (l : Fin (4 : ℕ)) → (G : bf.Grp) → LiftData (bf.Lab ⊕ Fin fp.Mc) (Ms l G).Md),
      (∀ (l : Fin (4 : ℕ)), ∀ G ∈ gset, fp.ModeExports l (AD.cat l) G (Lf.role l) d Dm0 dB Hm δ δ
        Nl (Ms l G) (L l G)) →
      (∀ (l : Fin (4 : ℕ)), ∀ G ∈ gset, (∀ (q : (Ms l G).Key), (Ms l G).dvOf q + (Ms l G).zc.dim ≤
        (2 : ℕ) * dB + (2 : ℕ)) ∧ (Ms l G).Λ ≤ S.Dstar ∧ gaugeSqNorm (Ms l G).zc.dim (Ms l G).δc ≤
        S.Dstar ∧ (2 : ℝ) * gaugeTail (Ms l G).zc.dim (Ms l G).δc / (2 : ℝ) ^ fp.Kstar Dm0 dB Hm δ
        Nl kD δ * S.Dstar ^ (300 : ℕ) ≤ (1 : ℝ) ∧ (∀ (m : (Ms l G).Md), S.Dstar⁻¹ ≤ (Ms l G).L.εM
        m) ∧ (∀ (V : ℤ × ℤ), (↑((Ms l G).alive V).card : ℝ) ≤ S.Dstar) ∧ ∀ (V : ℤ × ℤ),
        (↑(Finset.image (Ms l G).keyOf ((Ms l G).alive V)).card : ℝ) ≤ Nl) →
      ∀ (hA6 : (6 : ℝ) ≤ S.A0),
    let qG : bf.Grp → ℕ := fun (G : bf.Grp) ↦ clearInt (bf.vtag (bf.grpCenter d G)).C;
    ∀ (U : ℝ), (2 : ℝ) * (A.colBudget + (2 : ℝ)) * S.Dstar ^ (2 : ℕ) ≤ U → (0 : ℝ) < S.Dstar →
      (1 : ℝ) ≤ S.Dstar → ∀ (gsc : Fin (4 : ℕ) → ↥gset → ℤ),
      (∀ (l : Fin (4 : ℕ)) (G : ↥gset), fp.MainLiftExports l (AD.cat l) (↑G : bf.Grp) (Lf.role l)
        d Dm0 dB Hm (gsc l G) (L l (↑G : bf.Grp)) (Ms l (↑G : bf.Grp)).wave (Ms l
        (↑G : bf.Grp)).cellOf) →
      ∀ (c : (l : Fin (4 : ℕ)) → (G : ↥gset) → ℤ → ℤ × ℤ → (Ms l (↑G : bf.Grp)).Md → ℂ),
      (∀ (l : Fin (4 : ℕ)) (G : ↥gset), ∀ b ∈ Finset.image (fun (β : ℕ) ↦ A.R.1 + (↑(S.K *
        β) : ℤ)) (Finset.range (A.treeDepth + (1 : ℕ))), ∀ J ∈ fp.retainedV (↑G : bf.Grp) b S.K, ∑
        m ∈ (Ms l (↑G : bf.Grp)).alive (ancAt A.G J (b - (4 : ℤ) * (↑S.K : ℤ))), ‖c l G b J m‖ ^
        (2 : ℕ) ≤ (4 : ℝ) * S.Dstar ^ (2 : ℕ) * (1 : ℝ)) → ∀ (Cut : Fin (4 : ℕ) → Finset (ℤ × ℤ)),
    let cf : (l : Fin (4 : ℕ)) → (G : bf.Grp) → ℤ → ℤ × ℤ → (Ms l G).Md → ℂ := fun (l : Fin
        (4 : ℕ)) (G : bf.Grp) ↦ if hG : G ∈ gset then c l ⟨G, hG⟩ else fun (_ : ℤ) (_ : ℤ × ℤ)
        (_ : (Ms l G).Md) ↦ (0 : ℂ);
    let D₀ : fp.SideInput :=
      { cat := AD.cat, mbs := mbs, Lf := Lf, u := A.uslot p, S := S, hA := hA6, SP := S.sideParams
          (1 / 1024 : ℝ), hK := hK1, n := Fintype.card (bf.Lab ⊕ Fin fp.Mc), Ms := Ms, c := cf };
    ∀ (hcat : Fin (4 : ℕ) → List (CatCol bf.Vtx))
      (hmbb : ∀ (l : Fin (4 : ℕ)), ∀ e ∈ AD.cat l ++ hcat l, e.birth ∈ A.cells)
      (hmbT : ∀ (l : Fin (4 : ℕ)) (y : ℝ), (8 : ℝ) * A.colBudget + (↑(bf.tmplPath (AD.cat l ++
        hcat l) y) : ℝ) ≤ (8 : ℝ) * A.colBudget + ((1 : ℝ) + (↑AD.Mp : ℝ)) * Nl),
    let mb' : (l : Fin (4 : ℕ)) → bf.MainBudget (AD.cat l ++ hcat l) :=
      fun (l : Fin (4 : ℕ)) ↦ { hb := hmbb l, B := (8 : ℝ) * A.colBudget + ((1 : ℝ) + (↑AD.Mp :
                                  ℝ)) * Nl, hTp := hmbT l };
    let D : fp.SideInput := D₀.appendCat hcat mb';
    let S1 : Finset (ℤ × ℤ) := {I ∈ S0 | ∀ (j : Fin (4 : ℕ)), ∀ e ∈ Cut j, ¬dyadicGridCell A.G I.1
        I.2 ⊆ dyadicGridCell A.G e.1 e.2};
    S1 ⊆ S0 → S1 ⊆ A.cells →
      (∀ I ∈ A.cells, A.blkStart S.K I.1 ∈ Finset.image (fun (β : ℕ) ↦ A.R.1 + (↑(S.K * β) : ℤ))
        (Finset.range (A.treeDepth + (1 : ℕ)))) →
      (∀ (j : Fin (4 : ℕ)) (G : ↥gset), D.c j (↑G : bf.Grp) = c j G) →
    ∀ I ∈ S1, ∀ G ∈ gs I, ∀ h ∈ ModeComponents.upperHeights D.SP.Jst D.SP.δs, ∀ j,
    ∀ F ∈ (D.withQ0 (qG G)).goodCls G I j h, (D.withQ0 (qG G)).clsSize G I j F ≤ U := by
  intro κ c₀ cc hcc Dm0 A bf p AD d s δ kD fp dB Nl hcb hNl0 Hm S hK1 Lf ks S0 gs gset hlenMc mbs
    Ms L hexp hsch' hA6 qG U hU4 hD0 hD1 gsc hMLE c hcB Cut cf D₀ hcat hmbb hmbT mb' D S1 hS1S0
    hS1c hIB hcD I hI G hG h _ j F hF
  have! hGs : G ∈ gset := Finset.mem_biUnion.mpr ⟨I, hS1S0 hI, hG⟩
  have! hret : (D.withQ0 (qG G)).preAt I ∈ fp.retainedV G (A.blkStart S.K I.1) S.K := by
    obtain ⟨K', hK', -⟩ := Finset.mem_image.mp hF
    have! hK'' := (Finset.mem_filter.mp hK').1
    unfold FamParams.SideInput.compsAt at hK''
    split_ifs at hK'' with hcond
    · exact hcond.2
    · exact absurd hK'' (Finset.notMem_empty _)
  have! hW : ∀ m, (D.Ms j G).L.εM m ≤ A.colBudget ^ 2 := by
    intro m
    obtain ⟨ρ₀', z', g', -, -, hMLE, hεM', -⟩ := hexp j G hGs
    change (Ms j G).L.εM m ≤ _
    rw [← hεM' m]
    exact (hMLE.εM_le m).trans (by rw [hMLE.εP_eq]; exact bf.mainWeight_le fp.Mc j _)
  have! hcc := hcB j ⟨G, hGs⟩ _ (hIB I (hS1c hI)) _ hret
  have! hcl := (D.withQ0 (qG G)).clsSize_le G I j F (sq_nonneg _) hW
    (Cc := 4 * S.Dstar ^ 2 * 1) (by rw [← hcD j ⟨G, hGs⟩] at hcc; exact hcc)
    ((hsch' j G hGs).2.2.2.2.2.1 _) hD1
  refine hcl.trans (le_trans ?_ hU4)
  have! hs1 : Real.sqrt (1 + A.colBudget ^ 2) ≤ A.colBudget + 1 := by
    calc Real.sqrt (1 + A.colBudget ^ 2) ≤ Real.sqrt ((A.colBudget + 1) ^ 2) :=
          Real.sqrt_le_sqrt (by nlinarith only [hcb])
      _ = A.colBudget + 1 := Real.sqrt_sq (by linarith only [hcb])
  have! hs2 : Real.sqrt (4 * S.Dstar ^ 2 * 1) = 2 * S.Dstar := by
    rw [mul_one, show (4 : ℝ) * S.Dstar ^ 2 = (2 * S.Dstar) ^ 2 by ring,
      Real.sqrt_sq (by linarith only [hD0])]
  rw [hs2]
  change (Real.sqrt (1 + A.colBudget ^ 2) + 1) * S.Dstar * (2 * S.Dstar) ≤
    2 * (A.colBudget + 2) * S.Dstar ^ 2
  have! this : (Real.sqrt (1 + A.colBudget ^ 2) + 1) * S.Dstar * (2 * S.Dstar) ≤
      (A.colBudget + 2) * S.Dstar * (2 * S.Dstar) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith only [hs1]) hD0.le)
      (by linarith only [hD0])
  calc _ ≤ (A.colBudget + 2) * S.Dstar * (2 * S.Dstar) := this
    _ = 2 * (A.colBudget + 2) * S.Dstar ^ 2 := by ring

open Classical in
/-- Step `hΞ` of `leaf_estimate`, over the part of its context that it uses. -/
theorem leaf_estimate_hΞ :
    ∀ x : ℝ, 2 ≤ x → 8 * x ≤ x ^ 1000 := by
  intro x hx
  have! h8 : (8 : ℝ) ≤ 2 ^ 999 := by
    calc (8 : ℝ) = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ 999 := pow_le_pow_right₀ (by norm_num) (by norm_num)
  have! h1 : (8 : ℝ) ≤ x ^ 999 := le_trans h8 (pow_le_pow_left₀ (by norm_num) hx 999)
  calc 8 * x ≤ x ^ 999 * x := mul_le_mul_of_nonneg_right h1 (by linarith only [hx])
    _ = x ^ 1000 := by ring

open Classical in
/-- Step `hcoreE` of `leaf_estimate`, over the part of its context that it uses. -/
theorem leaf_estimate_hcoreE :
    ∀ (κ : LocalKernelClass) (c₀ : ℕ) (cc : ℕ), (1 : ℕ) ≤ cc → ∀ (Dm0 : ℕ) (A : ActiveSetup κ c₀)
      (bf : A.BasicFamilies), A.cells.Nonempty → ∀ (p : Fin (3 : ℕ)) (AD : bf.AttemptData p)
      (d : bf.Vtx) (s : ℕ) (δ : ℝ) (kD : ℝ),
    let fp : bf.FamParams := AD.fp;
    let dB : ℕ := A.dBnd;
    let Nl : ℝ := AD.n (fp.Lc + (5 : ℕ));
    ∀ (hNl0 : (0 : ℝ) ≤ Nl),
    let Hm : ℝ := max (max A.Hsrc (Real.exp (↑dB : ℝ))) (max ((5832 : ℝ) * max A.H padW ^ (4 : ℕ))
        ((↑dB : ℝ) * (bumpConst * (8 : ℝ) ^ (32 : ℕ) * ((2 : ℝ) / δ))));
    ∀ (S : ModeSchedule), (2 : ℝ) ≤ S.Dstar → ∀ (hK1 : (1 : ℕ) ≤ S.K),
    let Lf : SearchLeaf := leafAt A.famFuel fp.Lc (A.basicSlot p) s;
    let ks : ℕ := Lf.k;
    let S0 : Finset (ℤ × ℤ) := {I ∈ AD.Tc | ¬∃ c ∈ fp.failRoots, dyadicGridCell A.G I.1 I.2 ⊆
        dyadicGridCell A.G c.1 c.2};
    let gs : ℤ × ℤ → Finset bf.Grp := fun (I : ℤ × ℤ) ↦ fp.groupsAt I ks;
    let gset : Finset bf.Grp := S0.biUnion gs;
    ∀ (hlenMc : ∀ (l : Fin (4 : ℕ)), (AD.cat l).length ≤ fp.Mc),
    let mbs : (l : Fin (4 : ℕ)) → bf.MainBudget (AD.cat l) := fun (l : Fin (4 : ℕ)) ↦
        MainBudget.ofCounts bf fp.Mc (AD.cat l) (hlenMc l) l (fun (e : CatCol bf.Vtx) (he : e ∈
        AD.cat l) ↦ AD.hTc (AD.hT l e he).left) (fun (e : CatCol bf.Vtx) (he : e ∈ AD.cat l) ↦
        (AD.hT l e he).right.left) hNl0 fun (I : ℤ × ℤ) (_ : I ∈ A.cells) ↦ AD.hlab l I
        (AD.fp.Lc + (5 : ℕ)) le_rfl;
    ∀ (Ms : Fin (4 : ℕ) → bf.Grp → ModeSystem A.G (Fintype.card (bf.Lab ⊕ Fin fp.Mc))),
      (∀ (l : Fin (4 : ℕ)), ∀ G ∈ gset, (∀ (q : (Ms l G).Key), (Ms l G).dvOf q + (Ms l G).zc.dim ≤
        (2 : ℕ) * dB + (2 : ℕ)) ∧ (Ms l G).Λ ≤ S.Dstar ∧ gaugeSqNorm (Ms l G).zc.dim (Ms l G).δc ≤
        S.Dstar ∧ (2 : ℝ) * gaugeTail (Ms l G).zc.dim (Ms l G).δc / (2 : ℝ) ^ fp.Kstar Dm0 dB Hm δ
        Nl kD δ * S.Dstar ^ (300 : ℕ) ≤ (1 : ℝ) ∧ (∀ (m : (Ms l G).Md), S.Dstar⁻¹ ≤ (Ms l G).L.εM
        m) ∧ (∀ (V : ℤ × ℤ), (↑((Ms l G).alive V).card : ℝ) ≤ S.Dstar) ∧ ∀ (V : ℤ × ℤ),
        (↑(Finset.image (Ms l G).keyOf ((Ms l G).alive V)).card : ℝ) ≤ Nl) →
      ∀ (hA6 : (6 : ℝ) ≤ S.A0),
    let qG : bf.Grp → ℕ := fun (G : bf.Grp) ↦ clearInt (bf.vtag (bf.grpCenter d G)).C;
    ∀ (U : ℝ), (1 : ℝ) ≤ S.Dstar → (16 : ℝ) ≤ U → ∀ (ε : ℝ)
      (c : (l : Fin (4 : ℕ)) → (G : ↥gset) → ℤ → ℤ × ℤ → (Ms l (↑G : bf.Grp)).Md → ℂ),
      (∀ (l : Fin (4 : ℕ)) (G : ↥gset), ∀ b ∈ Finset.image (fun (β : ℕ) ↦ A.R.1 + (↑(S.K *
        β) : ℤ)) (Finset.range (A.treeDepth + (1 : ℕ))), ∀ J ∈ fp.retainedV (↑G : bf.Grp) b S.K, ∑
        m ∈ (Ms l (↑G : bf.Grp)).alive (ancAt A.G J (b - (4 : ℤ) * (↑S.K : ℤ))), ‖c l G b J m‖ ^
        (2 : ℕ) ≤ (4 : ℝ) * S.Dstar ^ (2 : ℕ) * (1 : ℝ)) → ∀ (Cut : Fin (4 : ℕ) → Finset (ℤ × ℤ)),
    let cf : (l : Fin (4 : ℕ)) → (G : bf.Grp) → ℤ → ℤ × ℤ → (Ms l G).Md → ℂ := fun (l : Fin
        (4 : ℕ)) (G : bf.Grp) ↦ if hG : G ∈ gset then c l ⟨G, hG⟩ else fun (_ : ℤ) (_ : ℤ × ℤ)
        (_ : (Ms l G).Md) ↦ (0 : ℂ);
    let D₀ : fp.SideInput :=
      { cat := AD.cat, mbs := mbs, Lf := Lf, u := A.uslot p, S := S, hA := hA6, SP := S.sideParams
          (1 / 1024 : ℝ), hK := hK1, n := Fintype.card (bf.Lab ⊕ Fin fp.Mc), Ms := Ms, c := cf };
    ∀ (hcat : Fin (4 : ℕ) → List (CatCol bf.Vtx))
      (hmbb : ∀ (l : Fin (4 : ℕ)), ∀ e ∈ AD.cat l ++ hcat l, e.birth ∈ A.cells)
      (hmbT : ∀ (l : Fin (4 : ℕ)) (y : ℝ), (8 : ℝ) * A.colBudget + (↑(bf.tmplPath (AD.cat l ++
        hcat l) y) : ℝ) ≤ (8 : ℝ) * A.colBudget + ((1 : ℝ) + (↑AD.Mp : ℝ)) * Nl),
    let mb' : (l : Fin (4 : ℕ)) → bf.MainBudget (AD.cat l ++ hcat l) :=
      fun (l : Fin (4 : ℕ)) ↦ { hb := hmbb l, B := (8 : ℝ) * A.colBudget + ((1 : ℝ) + (↑AD.Mp :
                                  ℝ)) * Nl, hTp := hmbT l };
    let D : fp.SideInput := D₀.appendCat hcat mb';
    let S1 : Finset (ℤ × ℤ) := {I ∈ S0 | ∀ (j : Fin (4 : ℕ)), ∀ e ∈ Cut j, ¬dyadicGridCell A.G I.1
        I.2 ⊆ dyadicGridCell A.G e.1 e.2};
    S1 ⊆ S0 → S1 ⊆ A.cells →
      (∀ I ∈ A.cells, A.blkStart S.K I.1 ∈ Finset.image (fun (β : ℕ) ↦ A.R.1 + (↑(S.K * β) : ℤ))
        (Finset.range (A.treeDepth + (1 : ℕ)))) →
      (∀ (j : Fin (4 : ℕ)) (G : ↥gset), D.c j (↑G : bf.Grp) = c j G) →
    let Iw : ℕ := ⌊Real.logb (2 : ℝ) (S.Dstar ^ (250 : ℕ))⌋₊;
    ∀ (C : Finset (ℤ × ℤ)) (C₂ : Finset (ℤ × ℤ)),
    let S₂ : Finset (ℤ × ℤ) := {I ∈ {I ∈ S1 | ¬∃ e ∈ C, dyadicGridCell A.G I.1 I.2 ⊆
        dyadicGridCell A.G e.1 e.2} | ¬∃ e ∈ C₂, dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G
        e.1 e.2};
    (∀ (l : Fin (4 : ℕ)), ∀ I ∈ S₂, ∀ G ∈ gs I, √((dyadicGridLength A.G I.1)⁻¹ * ∫ (y : ℝ) in
        dyadicGridLeft A.G I.1 I.2..dyadicGridLeft A.G I.1 I.2 + dyadicGridLength A.G I.1,
        ‖augPhys ((D.withQ0 (qG G)).toLeaf.sv l G I) y‖ ^ (2 : ℕ)) ≤ U) → S₂ ⊆ S1 →
      (S.Dstar * (√S.Dstar * √((4 : ℝ) * S.Dstar ^ (2 : ℕ) * (1 : ℝ)))) ^ (4 : ℕ) = (16 : ℝ) *
        S.Dstar ^ (10 : ℕ) →
      (S.Dstar * (√S.Dstar * √((4 : ℝ) * S.Dstar ^ (2 : ℕ) * (1 : ℝ)) + (1 : ℝ))) ^ (4 : ℕ) ≤
        (81 : ℝ) * S.Dstar ^ (10 : ℕ) →
    let ι : ℝ := (S.Dstar ^ (100 : ℕ))⁻¹ * S.Dstar ^ (10 : ℕ);
    ι = (S.Dstar ^ (100 : ℕ))⁻¹ * S.Dstar ^ (10 : ℕ) →
    let Qe : ℝ := (16 : ℝ) * fourErrC κ (3 : ℕ) * ι + K1c * ((2 : ℝ) * fourKC κ (3 : ℕ) *
        (12 : ℝ) ^ (4 : ℕ) * ε * U ^ (3 : ℕ) * S.Dstar ^ (4 : ℕ)) + (4 : ℝ) * ((81 : ℝ) *
        threeErrC κ (3 : ℕ) (1 : ℕ) * ι * U + K1c * ((8 : ℝ) * entryCU κ (3 : ℕ) (1 : ℕ) *
        (2 : ℝ) ^ ((1 : ℕ) + (4 : ℕ)) * (12 : ℝ) ^ (3 : ℕ) * ε * U ^ (3 : ℕ) * (S.Dstar ^
        (3 : ℕ) * ((↑Iw : ℝ) + (1 : ℝ)))));
    Qe = (16 : ℝ) * fourErrC κ (3 : ℕ) * ι + K1c * ((2 : ℝ) * fourKC κ (3 : ℕ) * (12 : ℝ) ^
        (4 : ℕ) * ε * U ^ (3 : ℕ) * S.Dstar ^ (4 : ℕ)) + (4 : ℝ) * ((81 : ℝ) * threeErrC κ (3 : ℕ)
        (1 : ℕ) * ι * U + K1c * ((8 : ℝ) * entryCU κ (3 : ℕ) (1 : ℕ) * (2 : ℝ) ^ ((1 : ℕ) +
        (4 : ℕ)) * (12 : ℝ) ^ (3 : ℕ) * ε * U ^ (3 : ℕ) * (S.Dstar ^ (3 : ℕ) * ((↑Iw : ℝ) +
        (1 : ℝ))))) →
    ∀ I ∈ S₂, D.coreE qG gs 3 1 Iw U ε I ≤ (gs I).card * Qe := by
  intro κ c₀ cc hcc Dm0 A bf hne p AD d s δ kD fp dB Nl hNl0 Hm S hD2 hK1 Lf ks S0 gs gset hlenMc
    mbs Ms hsch' hA6 qG U hD1 hU16 ε c hcB Cut cf D₀ hcat hmbb hmbT mb' D S1 hS1S0 hS1c hIB hcD Iw
    C C₂ S₂ hUs hS₂S1 h4pow h3pow ι hι Qe hQe I hI
  have! hI1 := hS₂S1 hI
  have hK1 : D.K1 = K1c := rfl
  have! hfour : ∀ G ∈ gs I, (D.withQ0 (qG G)).fourErr 3 G I ≤ 16 * fourErrC κ 3 * ι := by
    intro G hG
    have! hGs : G ∈ gset := Finset.mem_biUnion.mpr ⟨I, hS1S0 hI1, hG⟩
    have h := (D.withQ0 (qG G)).fourErr_le 3 G I (Cc := 4 * S.Dstar ^ 2 * 1)
      hD1 (fun l hne => ?_) (fun l => (hsch' l G hGs).2.2.2.2.2.1 _)
    · refine h.trans (le_of_eq ?_)
      change fourErrC κ 3 * (S.Dstar ^ 100)⁻¹ *
        (S.Dstar * (Real.sqrt S.Dstar * Real.sqrt (4 * S.Dstar ^ 2 * 1))) ^ 4 = _
      rw [h4pow, hι]; ring
    · have! hret : (D.withQ0 (qG G)).preAt I ∈ fp.retainedV G (A.blkStart S.K I.1) S.K := by
        unfold FamParams.SideInput.compsAt at hne
        split_ifs at hne with hcond
        · exact hcond.2
        · exact absurd rfl hne
      have! hcc := hcB l ⟨G, hGs⟩ _ (hIB I (hS1c hI1)) _ hret
      rw [← hcD l ⟨G, hGs⟩] at hcc
      exact hcc
  have! hthree : ∀ l, ∀ G ∈ gs I, (D.withQ0 (qG G)).threeErr 3 1 l G I ≤
      81 * threeErrC κ 3 1 * ι * U := by
    intro l G hG
    have! hGs : G ∈ gset := Finset.mem_biUnion.mpr ⟨I, hS1S0 hI1, hG⟩
    have h := (D.withQ0 (qG G)).threeErr_le 3 1 l G I (Cc := 4 * S.Dstar ^ 2 * 1)
      hD1 (fun l hne => ?_) (fun l => (hsch' l G hGs).2.2.2.2.2.1 _)
      (hUs l I hI G hG)
    · refine h.trans ?_
      change threeErrC κ 3 1 * (S.Dstar ^ 100)⁻¹ * U *
        (S.Dstar * (Real.sqrt S.Dstar * Real.sqrt (4 * S.Dstar ^ 2 * 1) + 1)) ^ 4 ≤ _
      have! h0 : 0 ≤ threeErrC κ 3 1 * (S.Dstar ^ 100)⁻¹ * U := by
        have! this := threeErrC_nonneg κ 3 1; positivity
      calc threeErrC κ 3 1 * (S.Dstar ^ 100)⁻¹ * U *
          (S.Dstar * (Real.sqrt S.Dstar * Real.sqrt (4 * S.Dstar ^ 2 * 1) + 1)) ^ 4
          ≤ threeErrC κ 3 1 * (S.Dstar ^ 100)⁻¹ * U * (81 * S.Dstar ^ 10) :=
            mul_le_mul_of_nonneg_left h3pow h0
        _ = _ := by rw [hι]; ring
    · have! hret : (D.withQ0 (qG G)).preAt I ∈ fp.retainedV G (A.blkStart S.K I.1) S.K := by
        unfold FamParams.SideInput.compsAt at hne
        split_ifs at hne with hcond
        · exact hcond.2
        · exact absurd rfl hne
      have! hcc := hcB l ⟨G, hGs⟩ _ (hIB I (hS1c hI1)) _ hret
      rw [← hcD l ⟨G, hGs⟩] at hcc
      exact hcc
  unfold FamParams.SideInput.coreE
  rw [hK1]
  have hS : D.S.Dstar = S.Dstar := rfl
  rw [hS]
  have! e1 : ∑ G ∈ gs I, ((D.withQ0 (qG G)).fourErr 3 G I + K1c * (2 * fourKC κ 3 * 12 ^ 4 * ε *
      U ^ 3 * S.Dstar ^ 4)) ≤ (gs I).card * (16 * fourErrC κ 3 * ι + K1c * (2 * fourKC κ 3 *
        12 ^ 4 * ε * U ^ 3 * S.Dstar ^ 4)) := by
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum fun G hG => by linarith only [hfour G hG]
  have! e2 : ∑ l, ∑ G ∈ gs I, ((D.withQ0 (qG G)).threeErr 3 1 l G I + K1c * (8 * entryCU κ 3 1 *
      2 ^ (1 + 4) * 12 ^ 3 * ε * U ^ 3 * (S.Dstar ^ 3 * (Iw + 1)))) ≤
      (gs I).card * (4 * (81 * threeErrC κ 3 1 * ι * U + K1c * (8 * entryCU κ 3 1 *
        2 ^ (1 + 4) * 12 ^ 3 * ε * U ^ 3 * (S.Dstar ^ 3 * (Iw + 1))))) := by
    calc _ ≤ ∑ _l : Fin 4, (gs I).card * (81 * threeErrC κ 3 1 * ι * U + K1c *
          (8 * entryCU κ 3 1 * 2 ^ (1 + 4) * 12 ^ 3 * ε * U ^ 3 * (S.Dstar ^ 3 * (Iw + 1)))) := by
          refine Finset.sum_le_sum fun l _ => ?_
          rw [← nsmul_eq_mul, ← Finset.sum_const]
          exact Finset.sum_le_sum fun G hG => by linarith only [hthree l G hG]
      _ = _ := by simp; ring
  have! e3 : ((gs I).card : ℝ) * (16 * fourErrC κ 3 * ι + K1c * (2 * fourKC κ 3 * 12 ^ 4 * ε *
      U ^ 3 * S.Dstar ^ 4)) + (gs I).card * (4 * (81 * threeErrC κ 3 1 * ι * U + K1c *
        (8 * entryCU κ 3 1 * 2 ^ (1 + 4) * 12 ^ 3 * ε * U ^ 3 * (S.Dstar ^ 3 * (Iw + 1))))) =
      (gs I).card * Qe := by rw [hQe]; ring
  linarith only [e1, e2, e3]



end ActiveSetup.BasicFamilies
end TrilinearHT.Auto
end
