/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

/- Adapted for Lean Pool from roos-j/lean-trilinearht at
7b4209609e6a7fb9d9935973ee8541495f943660. Imports, names, proof organization and
Mathlib interfaces have been updated; original authorship is retained above. -/

public import LeanPool.TrilinearHilbertTransform.Auto.Sec163SummingUpdateLevels.RetainedNumericExp

/-!
# Trilinear Hilbert transform: retainedMin_holds
-/

@[expose] public section

section
namespace TrilinearHT.Auto
open MeasureTheory Metric
open scoped FourierTransform ComplexConjugate ENNReal

open scoped Classical in
private def RetainedMinHoldsNh3Statement : Prop :=
  ∀ (κ : LocalKernelClass)
    (c' : ℕ)
    (Cb : ℕ)
    (θ₀ : ℝ),
  let b : ℕ :=
    Cb + (1 : ℕ)
  ∀ (Cl : ℕ)
    (_ : (1 : ℕ) ≤ Cl),
  let α : ℝ :=
    (1 / 1200 : ℝ) / ((4 : ℝ) * ((↑Cl : ℝ) + (1 : ℝ) + (1 : ℝ)))
  ∀ (Mpad : ℝ),
  let L₄ : ℝ :=
    Real.log ((4 : ℝ) + Mpad)
  ∀ (hMpad0 : (0 : ℝ) ≤ Mpad)
    (_ : (0 : ℝ) ≤ L₄)
    (k : ℕ)
    (B : ActiveSetup κ c')
    (p : Fin (3 : ℕ))
    (_ : (3 : ℕ) ≤ k),
  let η₀ : ℝ :=
    Real.exp ((-2 : ℝ) * (↑k : ℝ) ^ θ₀)
  let A : ActiveSetup κ c' :=
    B.padDc Mpad hMpad0
  ∀ (bf : A.BasicFamilies),
  let Y : ℝ :=
    L₄ + (2 : ℝ) * (↑k : ℝ) ^ b
  ∀ (_ : (4 : ℝ) * ((6000 : ℝ) ^ (30 : ℕ) * Y ^ (30 : ℕ) + (1 : ℝ)) * (↑Cl : ℝ) * ((2 : ℝ) +
      ((↑Cl : ℝ) + (1 : ℝ)) * ((2 : ℝ) * α * (↑k : ℝ) ^ θ₀ + (1 : ℝ))) ^ (6 : ℕ) *
      Real.exp (((1 : ℝ) + Real.log ((2 : ℝ) * (↑k : ℝ))) ^ (2 : ℕ)) ^ Cl ≤ Real.exp (α
      * (↑k : ℝ) ^ θ₀ / (4 : ℝ))),
  let P : ℕ :=
    ⌈η₀ ^ (-α)⌉₊
  ∀ (_ : Real.exp ((2 : ℝ) * α * (↑k : ℝ) ^ θ₀) ≤ (↑P : ℝ))
    (_ : (↑P : ℝ) ≤ Real.exp ((2 : ℝ) * α * (↑k : ℝ) ^ θ₀) + (1 : ℝ))
    (_ : (1 : ℝ) ≤ (↑P : ℝ))
    (fp : bf.FamParams)
    (_ : ∀ (x y : ℝ), Real.exp x * Real.exp y = Real.exp (x + y)),
  let Nl : ℕ :=
    (searchList A.famFuel fp.Lc (A.basicSlot p)).length
  ∀ (_ : (↑Nl : ℝ) ≤ (4 : ℝ) * ((6000 : ℝ) ^ (30 : ℕ) * Y ^ (30 : ℕ) + (1 : ℝ))),
  (↑Nl : ℝ) * (↑Cl : ℝ) * ((2 : ℝ) + ((↑Cl : ℝ) + (1 : ℝ)) * Real.log (↑P : ℝ)) ^ (6 :
    ℕ) * Real.exp (((1 : ℝ) + Real.log ((2 : ℝ) * (↑k : ℝ))) ^ (2 : ℕ)) ^ Cl ≤ (↑P :
    ℝ) ^ (1 / 8 : ℝ)


open scoped Classical in
private def RetainedMinHoldsNB6Statement : Prop :=
  ∀ (κ : LocalKernelClass)
    (c' : ℕ)
    (Cb : ℕ)
    (_ : (1 : ℕ) ≤ c')
    (Dst : ℕ)
    (hst : SameTagBound κ (max c' ((2 : ℕ) * tagKρ)) Dst)
    (Ca : ℝ),
  let b : ℕ :=
    Cb + (1 : ℕ)
  let m : ℕ :=
    (3 : ℕ) * Cb + (2 : ℕ)
  let c₃ : ℕ :=
    (3 : ℕ) * Cb + (3 : ℕ)
  let c : ℕ :=
    (90 : ℕ) * b + c₃ + (100 : ℕ)
  ∀ (C : ℕ),
  let Dg : ℕ :=
    Classical.choose (curvatureGraph κ (max c' (2 * tagKρ) + 1) (by omega))
  let a₀ : ℕ :=
    C + c + (1 : ℕ)
  let cc : ℕ :=
    (a₀ + (1 : ℕ)) * (Dg + (2 : ℕ))
  ∀ (Mpad : ℝ),
  let L₄ : ℝ :=
    Real.log ((4 : ℝ) + Mpad)
  ∀ (hMpad0 : (0 : ℝ) ≤ Mpad)
    (k : ℕ)
    (B : ActiveSetup κ c')
    (p : Fin (3 : ℕ)),
  let δa : ℝ :=
    Real.exp (-(↑k : ℝ) ^ (Cb + (2 : ℕ)))
  let A : ActiveSetup κ c' :=
    B.padDc Mpad hMpad0
  ∀ (bf : A.BasicFamilies),
  let Y : ℝ :=
    L₄ + (2 : ℝ) * (↑k : ℝ) ^ b
  ∀ (_ : A.colBudget ≤ Real.exp Y)
    (_ : (2 : ℝ) ≤ A.colBudget),
  let Tc : Finset (ℤ × ℤ) :=
    Finset.filter (A.active δa) A.cells
  ∀ (hTcA : Tc ⊆ A.cells),
  let Mp : ℕ :=
    ⌈Real.exp (Ca * (↑k : ℝ) ^ ((3 : ℕ) * Cb + (2 : ℕ)))⌉₊
  ∀ (hMp1 : (1 : ℕ) ≤ Mp)
    (hmultTc : ∀ (I : ℤ × ℤ), (Finset.card ({I' ∈ Tc | dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell
      A.G I'.1 I'.2})) ≤ Mp),
  let τ₃ : ℝ :=
    Real.exp (-(↑k : ℝ) ^ c₃)
  ∀ (hτ0 : (0 : ℝ) < τ₃)
    (hτ1 : τ₃ ≤ (1 : ℝ))
    (_ : (↑Mp : ℝ) ≤ Real.exp (Ca * (↑k : ℝ) ^ m) + (1 : ℝ))
    (fp : bf.FamParams)
    (cat : Fin (4 : ℕ) → List (CatCol bf.Vtx))
    (Kt : ℕ)
    (n : ℕ → ℝ)
    (Tmax : ℕ)
    (hLc : fp.Lc = A.famLc)
    (hmH : fp.mH = (2 : ℕ) * A.famFuel + (2 : ℕ))
    (hMc : fp.Mc = Tc.card * Tmax + Tc.card * Tmax)
    (hHed : fp.Hed = max (Real.exp ((↑k : ℝ) ^ cc)) (max (2 : ℝ) (Real.exp ((↑A.Dg : ℝ) * ((1 :
      ℝ) + Real.log A.Hsrc + Real.log (τ₃ / ((↑A.famVtxBound : ℝ) ^ (2 : ℕ) * n (A.famLc
      + (1 : ℕ))))⁻¹) ^ A.Dg))))
    (hcolr : IsMonotoneColoring bf.admT (bf.tagDist fp.Hed) A.famVtxBound (A.fcb1 fp.Hmax)
      (ActiveSetup.cb2 fp.Hmax) Finset.univ admCellSet (dyadicGridCell A.G A.R.1 A.R.2)
      fp.ωp fp.ωh)
    (hKh : ∀ (I : ℤ × ℤ), Fintype.card (fp.HelperName I (Fin A.famVtxBound)) ≤ Kt)
    (hn0 : (2 : ℝ) * A.colBudget ≤ n (0 : ℕ))
    (hgrow : ∀ (r : ℕ), ((1 : ℝ) + ((↑fp.Lc : ℝ) + (6 : ℝ)) * (↑Mp : ℝ) * closureRatio
      A.famVtxBound Kt fp.mH Tmax (Real.exp ((↑Dst : ℝ) * ((1 : ℝ) + Real.log A.Hsrc) ^
      Dst)) τ₃) * n r ≤ n (r + (1 : ℕ)))
    (hcapH : closureRatio A.famVtxBound Kt fp.mH Tmax (Real.exp ((↑Dst : ℝ) * ((1 : ℝ) + Real.log
      A.Hsrc) ^ Dst)) τ₃ * n (fp.Lc + (4 : ℕ)) < (↑Tmax : ℝ))
    (hcats : ∀ (l : Fin (4 : ℕ)), (∀ I ∈ Tc, ∀ (w : fp.TestName I Unit), (fp.testOf l I (fun (_ :
      Unit) => bf.patIn fp.Mc p I l) w).Pass A.G (bf.origCols l) I A.csrc A.Hsrc bf.vtag
      (A.w I) (catThreshold A.famVtxBound τ₃ n (fp.testOf l I (fun (_ : Unit) =>
      bf.patIn fp.Mc p I l) w).r) fp.mH (cat l)) ∧ (∀ e ∈ cat l, e.birth ∈ Tc ∧ e.rank ≤
      fp.Lc + (5 : ℕ) ∧ ∃ R ∈ residueBox (bf.vtag e.tag).dim (9 : ℕ), ∃ (γ : ℝ), e =
      templateCol (bf.vtag e.tag) l R γ e.birth e.rank e.tag) ∧ (∀ e ∈ cat l,
      bf.occAvail (↑e.tag.2 : ℤ × ℤ) e.tag.1) ∧ (∀ (I : ℤ × ℤ), ∀ r ≤ fp.Lc + (5 : ℕ),
      (↑(mainLabels A.G fp.Mc (bf.origCols l) (cat l) I r).card : ℝ) ≤ n r) ∧ (cat
      l).length ≤ Tc.card * Tmax)
    (_ : ∀ (r : ℕ), (0 : ℝ) ≤ n r)
    (_ : ∀ r ≤ fp.Lc + (5 : ℕ), n r ≤ Real.exp ((↑k : ℝ) ^ C)),
  let T : ℝ :=
    Y + (↑k : ℝ) ^ C + Ca * (↑k : ℝ) ^ m + (2 : ℝ)
  ∀ (_ : Real.log (20 : ℝ) + T ≤ (↑k : ℝ) ^ cc)
    (_ : (0 : ℝ) ≤ (↑k : ℝ) ^ C)
    (_ : (0 : ℝ) ≤ Ca * (↑k : ℝ) ^ m)
    (_ : (0 : ℝ) ≤ Y)
    (_ : ∀ (x y : ℝ), Real.exp x * Real.exp y = Real.exp (x + y))
    (nHedV : (18 : ℝ) * max A.H ActiveSetup.padW ^ (2 : ℕ) ≤ Real.exp ((↑k : ℝ) ^ cc))
    (nHedτ₂ : Real.exp ((↑A.Dg : ℝ) * ((1 : ℝ) + Real.log A.Hsrc + Real.log (τ₃ / ((1 : ℝ) +
      A.colBudget * √(n (fp.Lc + (4 : ℕ))) * (A.colBudget * √((2 : ℝ) * A.colBudget +
      ((1 : ℝ) + (↑Mp : ℝ)) * n (fp.Lc + (5 : ℕ))))))⁻¹) ^ A.Dg) ≤ Real.exp ((↑k : ℝ) ^
      cc))
    (nHedτ' : Real.exp ((↑A.Dg : ℝ) * ((1 : ℝ) + Real.log A.Hsrc + Real.log ((1 : ℝ) + (↑⌈(8 : ℝ)
      * A.colBudget + n (fp.Lc + (5 : ℕ))⌉₊ : ℝ) * A.colBudget ^ (2 : ℕ))) ^ A.Dg) ≤
      Real.exp ((↑k : ℝ) ^ cc))
    (hHedge : Real.exp ((↑k : ℝ) ^ cc) ≤ fp.Hed),
  let AD : bf.AttemptData p :=
    { fp := fp, cat := cat, Tc := Tc, hTc := hTcA, Mp := Mp, hMp1 := hMp1, hmult := hmultTc,
      Dst := Dst, hst := hst, τ₃ := τ₃, hτ₃ := hτ0, hτ₃1 := hτ1, Kt := Kt, n := n, Tmax := Tmax,
      hLc := hLc, hmH := hmH, hMc := hMc, hcol := hcolr, hKh := hKh, hn0 := hn0, hgrow := hgrow,
      hcapH := hcapH, hpassM := fun l => (hcats l).1, hT := fun l => (hcats l).2.1,
      htag := fun l => (hcats l).2.2.1, hlab := fun l => (hcats l).2.2.2.1,
      hlen := fun l => (hcats l).2.2.2.2, hHedV := nHedV.trans hHedge,
      hHed2 := by rw [hHed]; exact le_max_of_le_right (le_max_left _ _),
      hHedτ₂ := nHedτ₂.trans hHedge, hHedτ' := nHedτ'.trans hHedge }
  Real.log ((2 : ℝ) * ((8 : ℝ) * A.colBudget + ((1 : ℝ) + (↑AD.Mp : ℝ)) * AD.n
    (AD.fp.Lc + (5 : ℕ)))) ≤ (↑k : ℝ) ^ cc


open scoped Classical in
private def RetainedMinHoldsNB12Statement : Prop :=
  ∀ (κ : LocalKernelClass)
    (c' : ℕ)
    (Cb : ℕ)
    (_ : ℝ)
    (_ : (1 : ℕ) ≤ c')
    (Dst : ℕ)
    (hst : SameTagBound κ (max c' ((2 : ℕ) * tagKρ)) Dst)
    (Ca : ℝ),
  let b : ℕ :=
    Cb + (1 : ℕ)
  let m : ℕ :=
    (3 : ℕ) * Cb + (2 : ℕ)
  let c₃ : ℕ :=
    (3 : ℕ) * Cb + (3 : ℕ)
  let c : ℕ :=
    (90 : ℕ) * b + c₃ + (100 : ℕ)
  ∀ (C : ℕ)
    (_ : ℝ),
  let Dg : ℕ :=
    Classical.choose (curvatureGraph κ (max c' (2 * tagKρ) + 1) (by omega))
  let a₀ : ℕ :=
    C + c + (1 : ℕ)
  let cc : ℕ :=
    (a₀ + (1 : ℕ)) * (Dg + (2 : ℕ))
  ∀ (_ : ℕ)
    (_ : ℝ)
    (Mpad : ℝ),
  let L₄ : ℝ :=
    Real.log ((4 : ℝ) + Mpad)
  let lW : ℝ :=
    Real.log ActiveSetup.padW
  let cH : ℝ :=
    Real.log ((↑tagKρ : ℝ) ^ ((2 : ℕ) * tagKρ) + (20 : ℝ))
  ∀ (hMpad0 : (0 : ℝ) ≤ Mpad)
    (_ : ℕ)
    (k : ℕ)
    (B : ActiveSetup κ c')
    (p : Fin (3 : ℕ))
    (_ : (3 : ℕ) ≤ k),
  let δa : ℝ :=
    Real.exp (-(↑k : ℝ) ^ (Cb + (2 : ℕ)))
  let A : ActiveSetup κ c' :=
    B.padDc Mpad hMpad0
  ∀ (bf : A.BasicFamilies)
    (_ : (1 : ℝ) ≤ (↑k : ℝ)),
  let Y : ℝ :=
    L₄ + (2 : ℝ) * (↑k : ℝ) ^ b
  ∀ (_ : (↑A.famVtxBound : ℝ) ≤ Real.exp (Y + (3 : ℝ)))
    (_ : Real.log A.Hsrc ≤ Real.log ((↑tagKρ : ℝ) ^ ((2 : ℕ) * tagKρ) + (20 : ℝ)) + (2 : ℝ) *
      (Real.log ActiveSetup.padW + Y)),
  let Tc : Finset (ℤ × ℤ) :=
    Finset.filter (A.active δa) A.cells
  ∀ (hTcA : Tc ⊆ A.cells),
  let Mp : ℕ :=
    ⌈Real.exp (Ca * (↑k : ℝ) ^ ((3 : ℕ) * Cb + (2 : ℕ)))⌉₊
  ∀ (hMp1 : (1 : ℕ) ≤ Mp)
    (hmultTc : ∀ (I : ℤ × ℤ), (Finset.card ({I' ∈ Tc | dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell
      A.G I'.1 I'.2})) ≤ Mp),
  let τ₃ : ℝ :=
    Real.exp (-(↑k : ℝ) ^ c₃)
  ∀ (_ : τ₃ = Real.exp (-(↑k : ℝ) ^ c₃))
    (hτ0 : (0 : ℝ) < τ₃)
    (hτ1 : τ₃ ≤ (1 : ℝ))
    (fp : bf.FamParams)
    (cat : Fin (4 : ℕ) → List (CatCol bf.Vtx))
    (Kt : ℕ)
    (n : ℕ → ℝ)
    (Tmax : ℕ)
    (hLc : fp.Lc = A.famLc)
    (hmH : fp.mH = (2 : ℕ) * A.famFuel + (2 : ℕ))
    (hMc : fp.Mc = Tc.card * Tmax + Tc.card * Tmax)
    (hHed : fp.Hed = max (Real.exp ((↑k : ℝ) ^ cc)) (max (2 : ℝ) (Real.exp ((↑A.Dg : ℝ) * ((1 :
      ℝ) + Real.log A.Hsrc + Real.log (τ₃ / ((↑A.famVtxBound : ℝ) ^ (2 : ℕ) * n (A.famLc
      + (1 : ℕ))))⁻¹) ^ A.Dg))))
    (hcolr : IsMonotoneColoring bf.admT (bf.tagDist fp.Hed) A.famVtxBound (A.fcb1 fp.Hmax)
      (ActiveSetup.cb2 fp.Hmax) Finset.univ admCellSet (dyadicGridCell A.G A.R.1 A.R.2)
      fp.ωp fp.ωh)
    (hKh : ∀ (I : ℤ × ℤ), Fintype.card (fp.HelperName I (Fin A.famVtxBound)) ≤ Kt)
    (hn0 : (2 : ℝ) * A.colBudget ≤ n (0 : ℕ))
    (hgrow : ∀ (r : ℕ), ((1 : ℝ) + ((↑fp.Lc : ℝ) + (6 : ℝ)) * (↑Mp : ℝ) * closureRatio
      A.famVtxBound Kt fp.mH Tmax (Real.exp ((↑Dst : ℝ) * ((1 : ℝ) + Real.log A.Hsrc) ^
      Dst)) τ₃) * n r ≤ n (r + (1 : ℕ)))
    (hcapH : closureRatio A.famVtxBound Kt fp.mH Tmax (Real.exp ((↑Dst : ℝ) * ((1 : ℝ) + Real.log
      A.Hsrc) ^ Dst)) τ₃ * n (fp.Lc + (4 : ℕ)) < (↑Tmax : ℝ))
    (hcats : ∀ (l : Fin (4 : ℕ)), (∀ I ∈ Tc, ∀ (w : fp.TestName I Unit), (fp.testOf l I (fun (_ :
      Unit) => bf.patIn fp.Mc p I l) w).Pass A.G (bf.origCols l) I A.csrc A.Hsrc bf.vtag
      (A.w I) (catThreshold A.famVtxBound τ₃ n (fp.testOf l I (fun (_ : Unit) =>
      bf.patIn fp.Mc p I l) w).r) fp.mH (cat l)) ∧ (∀ e ∈ cat l, e.birth ∈ Tc ∧ e.rank ≤
      fp.Lc + (5 : ℕ) ∧ ∃ R ∈ residueBox (bf.vtag e.tag).dim (9 : ℕ), ∃ (γ : ℝ), e =
      templateCol (bf.vtag e.tag) l R γ e.birth e.rank e.tag) ∧ (∀ e ∈ cat l,
      bf.occAvail (↑e.tag.2 : ℤ × ℤ) e.tag.1) ∧ (∀ (I : ℤ × ℤ), ∀ r ≤ fp.Lc + (5 : ℕ),
      (↑(mainLabels A.G fp.Mc (bf.origCols l) (cat l) I r).card : ℝ) ≤ n r) ∧ (cat
      l).length ≤ Tc.card * Tmax)
    (_ : ∀ (r : ℕ), (4 : ℝ) ≤ n r)
    (_ : ∀ r ≤ fp.Lc + (5 : ℕ), n r ≤ Real.exp ((↑k : ℝ) ^ C))
    (_ : (0 : ℝ) ≤ (↑k : ℝ) ^ C)
    (_ : (0 : ℝ) ≤ Ca * (↑k : ℝ) ^ m)
    (_ : (0 : ℝ) ≤ Y)
    (_ : (2 : ℝ) ≤ Real.log A.Hsrc)
    (_ : ∀ (w : ℝ), (0 : ℝ) ≤ w → w ≤ (1 : ℝ) + (cH + (2 : ℝ) * (lW + Y)) + Real.log (6 : ℝ)
      + (3 : ℝ) * (Y + (↑k : ℝ) ^ C + Ca * (↑k : ℝ) ^ m + (2 : ℝ)) + (↑k : ℝ) ^ c₃ + (2
      : ℝ) * (Y + (3 : ℝ)) → (↑A.Dg : ℝ) * w ^ A.Dg ≤ (↑k : ℝ) ^ cc)
    (_ : (0 : ℝ) ≤ Real.log (6 : ℝ))
    (nHedV : (18 : ℝ) * max A.H ActiveSetup.padW ^ (2 : ℕ) ≤ Real.exp ((↑k : ℝ) ^ cc))
    (nHedτ₂ : Real.exp ((↑A.Dg : ℝ) * ((1 : ℝ) + Real.log A.Hsrc + Real.log (τ₃ / ((1 : ℝ) +
      A.colBudget * √(n (fp.Lc + (4 : ℕ))) * (A.colBudget * √((2 : ℝ) * A.colBudget +
      ((1 : ℝ) + (↑Mp : ℝ)) * n (fp.Lc + (5 : ℕ))))))⁻¹) ^ A.Dg) ≤ Real.exp ((↑k : ℝ) ^
      cc))
    (nHedτ' : Real.exp ((↑A.Dg : ℝ) * ((1 : ℝ) + Real.log A.Hsrc + Real.log ((1 : ℝ) + (↑⌈(8 : ℝ)
      * A.colBudget + n (fp.Lc + (5 : ℕ))⌉₊ : ℝ) * A.colBudget ^ (2 : ℕ))) ^ A.Dg) ≤
      Real.exp ((↑k : ℝ) ^ cc))
    (hHedge : Real.exp ((↑k : ℝ) ^ cc) ≤ fp.Hed),
  let AD : bf.AttemptData p :=
    { fp := fp, cat := cat, Tc := Tc, hTc := hTcA, Mp := Mp, hMp1 := hMp1, hmult := hmultTc,
      Dst := Dst, hst := hst, τ₃ := τ₃, hτ₃ := hτ0, hτ₃1 := hτ1, Kt := Kt, n := n, Tmax := Tmax,
      hLc := hLc, hmH := hmH, hMc := hMc, hcol := hcolr, hKh := hKh, hn0 := hn0, hgrow := hgrow,
      hcapH := hcapH, hpassM := fun l => (hcats l).1, hT := fun l => (hcats l).2.1,
      htag := fun l => (hcats l).2.2.1, hlab := fun l => (hcats l).2.2.2.1,
      hlen := fun l => (hcats l).2.2.2.2, hHedV := nHedV.trans hHedge,
      hHed2 := by rw [hHed]; exact le_max_of_le_right (le_max_left _ _),
      hHedτ₂ := nHedτ₂.trans hHedge, hHedτ' := nHedτ'.trans hHedge }
  Real.log AD.fp.Hed ≤ (↑k : ℝ) ^ cc


open scoped Classical in
private def RetainedMinHoldsNh4Statement : Prop :=
  ∀ (κ : LocalKernelClass)
    (c' : ℕ)
    (Cb : ℕ)
    (θ₀ : ℝ)
    (_ : (1 : ℕ) ≤ c')
    (Ca : ℝ),
  let b : ℕ :=
    Cb + (1 : ℕ)
  let m : ℕ :=
    (3 : ℕ) * Cb + (2 : ℕ)
  let c₃ : ℕ :=
    (3 : ℕ) * Cb + (3 : ℕ)
  let c : ℕ :=
    (90 : ℕ) * b + c₃ + (100 : ℕ)
  ∀ (C : ℕ),
  let Dg : ℕ :=
    Classical.choose (curvatureGraph κ (max c' (2 * tagKρ) + 1) (by omega))
  let a₀ : ℕ :=
    C + c + (1 : ℕ)
  let cc : ℕ :=
    (a₀ + (1 : ℕ)) * (Dg + (2 : ℕ))
  ∀ (Cl : ℕ)
    (_ : (1 : ℕ) ≤ Cl),
  let α : ℝ :=
    (1 / 1200 : ℝ) / ((4 : ℝ) * ((↑Cl : ℝ) + (1 : ℝ) + (1 : ℝ)))
  ∀ (Mpad : ℝ),
  let L₄ : ℝ :=
    Real.log ((4 : ℝ) + Mpad)
  ∀ (hMpad0 : (0 : ℝ) ≤ Mpad)
    (_ : (0 : ℝ) ≤ L₄)
    (k : ℕ)
    (B : ActiveSetup κ c')
    (p : Fin (3 : ℕ))
    (_ : (3 : ℕ) ≤ k)
    (_ : B.S = (2 : ℝ)),
  let η₀ : ℝ :=
    Real.exp ((-2 : ℝ) * (↑k : ℝ) ^ θ₀)
  let A : ActiveSetup κ c' :=
    B.padDc Mpad hMpad0
  ∀ (bf : A.BasicFamilies),
  let Y : ℝ :=
    L₄ + (2 : ℝ) * (↑k : ℝ) ^ b
  ∀ (_ : (↑A.famVtxBound : ℝ) ≤ Real.exp (Y + (3 : ℝ))),
  let Mp : ℕ :=
    ⌈Real.exp (Ca * (↑k : ℝ) ^ ((3 : ℕ) * Cb + (2 : ℕ)))⌉₊
  let P : ℕ :=
    ⌈η₀ ^ (-α)⌉₊
  let τ₃ : ℝ :=
    Real.exp (-(↑k : ℝ) ^ c₃)
  ∀ (_ : (0 : ℝ) < τ₃)
    (_ : (↑P : ℝ) ≤ Real.exp ((2 : ℝ) * α * (↑k : ℝ) ^ θ₀) + (1 : ℝ))
    (_ : (1 : ℝ) ≤ (↑P : ℝ))
    (_ : (↑Mp : ℝ) ≤ Real.exp (Ca * (↑k : ℝ) ^ m) + (1 : ℝ))
    (fp : bf.FamParams)
    (_ : ∀ (x y : ℝ), Real.exp x * Real.exp y = Real.exp (x + y)),
  let kD : ℝ :=
    ((2 : ℝ) * (↑Cl : ℝ) + (2 : ℝ)) * (↑k : ℝ) ^ (cc + (1 : ℕ))
  let δ : ℝ :=
    Real.exp (-kD)
  ∀ (_ : (4 : ℝ) * ((6000 : ℝ) ^ (30 : ℕ) * Y ^ (30 : ℕ) + (1 : ℝ)) * ((↑Cl : ℝ) * kD ^ Cl *
      (Real.exp ((2 : ℝ) * α * (↑k : ℝ) ^ θ₀) + (1 : ℝ)) ^ Cl * Real.exp (((1 : ℝ) +
      Real.log ((2 : ℝ) * (↑k : ℝ))) ^ (2 : ℕ)) ^ Cl * ((Real.exp ((2 : ℝ) * α * (↑k :
      ℝ) ^ θ₀) + (2 : ℝ)) ^ (2 : ℕ) * τ₃ + Real.exp ((↑Cl : ℝ) * (↑k : ℝ) ^ cc) *
      (Real.exp (-kD / (2 : ℝ)) + δ)) + (↑Cl : ℝ) * Real.exp (-(↑k : ℝ))) + (Real.exp
      (Ca * (↑k : ℝ) ^ m) + (1 : ℝ)) * ((4 : ℝ) * ((6000 : ℝ) ^ (30 : ℕ) * Y ^ (30 : ℕ)
      + (1 : ℝ)) * ((9 : ℝ) * (Real.exp (Y + (3 : ℝ)) + (1 : ℝ)) * τ₃ * (16 : ℝ))) ≤ η₀
      ^ min ((1 / 1200 : ℝ) / (2 : ℝ)) (α / (4 : ℝ)))
    (_ : δ = Real.exp (-kD)),
  let Nl : ℕ :=
    (searchList A.famFuel fp.Lc (A.basicSlot p)).length
  let W : ℝ :=
    (↑Nl : ℝ) * ((9 : ℝ) * ((↑A.famVtxBound : ℝ) + (1 : ℝ)) * τ₃ * max (2 : ℝ) A.S ^ (4
      : ℕ))
  ∀ (_ : W = (↑Nl : ℝ) * ((9 : ℝ) * ((↑A.famVtxBound : ℝ) + (1 : ℝ)) * τ₃ * max (2 : ℝ) A.S ^
      (4 : ℕ)))
    (_ : (↑Nl : ℝ) ≤ (4 : ℝ) * ((6000 : ℝ) ^ (30 : ℕ) * Y ^ (30 : ℕ) + (1 : ℝ))),
  (↑Nl : ℝ) * ((↑Cl : ℝ) * (kD * (↑P : ℝ)) ^ Cl * Real.exp (((1 : ℝ) + Real.log ((2 :
    ℝ) * (↑k : ℝ))) ^ (2 : ℕ)) ^ Cl * (((↑P : ℝ) + (1 : ℝ)) ^ (2 : ℕ) * τ₃ + Real.exp
    ((↑Cl : ℝ) * (↑k : ℝ) ^ cc) * (√δ + Real.exp (-kD))) + (↑Cl : ℝ) * Real.exp (-(↑k
    : ℝ))) + (↑Mp : ℝ) * W ≤ η₀ ^ min ((1 / 1200 : ℝ) / (2 : ℝ)) ((1 / 1200 : ℝ) / ((4
    : ℝ) * ((↑Cl : ℝ) + (1 : ℝ) + (1 : ℝ))) / (4 : ℝ))


open scoped Classical in
private def RetainedMinHoldsStage4Statement : Prop :=
  ∀ (κ : LocalKernelClass)
    (c' : ℕ)
    (Cb : ℕ)
    (θ₀ : ℝ)
    (_ : (1 : ℕ) ≤ c')
    (Dst : ℕ)
    (hst : SameTagBound κ (max c' ((2 : ℕ) * tagKρ)) Dst)
    (Ca : ℝ),
  let b : ℕ :=
    Cb + (1 : ℕ)
  let m : ℕ :=
    (3 : ℕ) * Cb + (2 : ℕ)
  ∀ (hmult : ∀ (k : ℕ), (1 : ℕ) ≤ k → ∀ (B : ActiveSetup κ c') (η₀ : ℝ), B.LevelProps k Cb η₀ → ∀
      (y : ℝ), (↑(Finset.card ({I ∈ B.cells | y ∈ dyadicGridCell B.G I.1 I.2 ∧ B.active
      (Real.exp (-(↑k : ℝ) ^ (Cb + (2 : ℕ)))) I})) : ℝ) ≤ Real.exp (Ca * (↑k : ℝ) ^ m)),
  let c₃ : ℕ :=
    (3 : ℕ) * Cb + (3 : ℕ)
  let c : ℕ :=
    (90 : ℕ) * b + c₃ + (100 : ℕ)
  ∀ (C : ℕ)
    (_ : ℝ),
  let Dg : ℕ :=
    Classical.choose (curvatureGraph κ (max c' (2 * tagKρ) + 1) (by omega))
  let a₀ : ℕ :=
    C + c + (1 : ℕ)
  let cc : ℕ :=
    (a₀ + (1 : ℕ)) * (Dg + (2 : ℕ))
  ∀ (_ : cc = (a₀ + (1 : ℕ)) * (Dg + (2 : ℕ)))
    (Cl : ℕ)
    (K₀ : ℝ)
    (_ : (1 : ℕ) ≤ Cl)
    (_ : ∀ {A : ActiveSetup κ c'} (bf : A.BasicFamilies) (k : ℕ) {η₀ E : ℝ}, A.AncClosed → (∀
      I ∈ A.cells, ∀ (s s' : Fin (4 : ℕ)), s ≠ s' → PairSmall (dyadicGridLeft A.G I.1
      I.2) (dyadicGridLength A.G I.1) (A.w I) s s' (A.Y I s) (A.Y I s') ((2 : ℝ) * η₀))
      → A.SubRootProps η₀ E → A.S = (2 : ℝ) → A.η = (4 : ℝ) * η₀ → (0 : ℝ) < η₀ →
      A.cells.Nonempty → ∀ {q : ℝ} (hq2 : (2 : ℝ) < q) (hq3 : q < (3 : ℝ)) {Nd : ℕ},
      A.DepthWin Nd → ∀ (p : Fin (3 : ℕ)) (AD : bf.AttemptData p) (x : bf.Vtx) (s : ℕ)
      {δ ρ kD : ℝ}, (0 : ℝ) < δ → δ ≤ (1 / 8 : ℝ) → (8 : ℝ) * (↑A.dBnd : ℝ) * δ ≤ (1 :
      ℝ) → δ ^ (2 : ℕ) * AD.n (AD.fp.Lc + (5 : ℕ)) * A.colBudget ^ (2 : ℕ) ≤ (1 : ℝ) →
      (0 : ℝ) < ρ → ρ < (1 : ℝ) → K₀ ≤ (↑k : ℝ) → (↑k : ℝ) ^ cc ≤ kD → Real.log ((2 : ℝ)
      * ((8 : ℝ) * A.colBudget + ((1 : ℝ) + (↑AD.Mp : ℝ)) * AD.n (AD.fp.Lc + (5 : ℕ))))
      ≤ (↑k : ℝ) ^ cc → Real.log ((2 : ℝ) * A.colBudget) ≤ (↑k : ℝ) ^ cc → (↑((2 : ℕ) *
      A.famFuel + (2 : ℕ)) : ℝ) ≤ (↑cc : ℝ) * (Real.log (↑k : ℝ) + (1 : ℝ)) → (↑AD.fp.Lc
      : ℝ) + (6 : ℝ) ≤ (↑k : ℝ) ^ cc → (↑AD.fp.Hmax : ℝ) + (1 : ℝ) ≤ ((↑k : ℝ) *
      (↑AD.fp.P : ℝ)) ^ cc → (↑A.dBnd : ℝ) ≤ (↑k : ℝ) ^ cc → Real.log AD.fp.Hed ≤ (↑k :
      ℝ) ^ cc → Real.log A.Hsrc ≤ (↑k : ℝ) ^ cc → Real.log (max A.H ActiveSetup.padW) ≤
      (↑k : ℝ) ^ cc → δ⁻¹ ≤ Real.exp kD → E ≤ (↑k : ℝ) ^ cc → ρ⁻¹ ≤ (↑k : ℝ) ^ cc → ∃ (F
      : Fin (6 : ℕ) → Finset (ℤ × ℤ)), (∀ (i : Fin (6 : ℕ)), ∀ c ∈ F i, dyadicGridCell
      A.G c.1 c.2 ⊆ dyadicGridCell A.G A.R.1 A.R.2) ∧ (∀ (i : Fin (6 : ℕ)),
      dyadicRootLength A.G (F i) ≤ (2 : ℝ) * ρ * dyadicGridLength A.G A.R.1) ∧ ∀ cs ⊆
      AD.Tc, (∀ I ∈ cs, ¬∃ c ∈ AD.fp.failRoots, dyadicGridCell A.G I.1 I.2 ⊆
      dyadicGridCell A.G c.1 c.2) → (∀ I ∈ cs, ∀ (i : Fin (6 : ℕ)), ∀ e ∈ F i,
      ¬dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G e.1 e.2) → ∑ I ∈ cs,
      dyadicGridLength A.G I.1 * min A.η ‖∑ G ∈ AD.fp.groupsAt I (leafAt A.famFuel
      AD.fp.Lc (A.basicSlot p) s).k, (AD.fp.Λc I : (Fin (4 : ℕ) → ↥(ColumnL2 (bf.Lab ⊕
      Fin AD.fp.Mc))) → ℂ) fun (l : Fin (4 : ℕ)) => (AD.fp.ballFilt l (AD.cat l) I G
      ((leafAt A.famFuel AD.fp.Lc (A.basicSlot p) s).role l) : ↥(ColumnL2 (bf.Lab ⊕ Fin
      AD.fp.Mc)) → ↥(ColumnL2 (bf.Lab ⊕ Fin AD.fp.Mc))) (AD.fp.inputL AD.cat I (bf.patIn
      AD.fp.Mc p I) (leafAt A.famFuel AD.fp.Lc (A.basicSlot p) s).layers l)‖ ≤ leafBnd
      Cl kD AD.fp.P k cc A.η η₀ AD.τ₃ δ (finiteDepthConstant κ q Nd) (nbCM κ hq2 hq3 +
      nbCUM κ hq2 hq3) q (dyadicGridLength A.G A.R.1))
    (q : ℝ)
    (hq2 : (2 : ℝ) < q)
    (hq3 : q < (3 : ℝ))
    (_ : (2 : ℝ) * ((↑Cl : ℝ) + (1 : ℝ)) * ((q - (2 : ℝ)) / (q - (1 : ℝ))) < (1 / 8 : ℝ)),
  let α : ℝ :=
    (1 / 1200 : ℝ) / ((4 : ℝ) * ((↑Cl : ℝ) + (1 : ℝ) + (1 : ℝ)))
  let cs : ℝ :=
    min ((1 / 1200 : ℝ) / (2 : ℝ)) (α / (4 : ℝ))
  ∀ (_ : cs = min ((1 / 1200 : ℝ) / (2 : ℝ)) (α / (4 : ℝ))),
  let Cq : ℝ :=
    nbCM κ hq2 hq3 + nbCUM κ hq2 hq3
  ∀ (_ : (0 : ℝ) ≤ Cq),
  let Cfin : ℝ :=
    ((3 : ℝ) + Cq) * ((2 : ℝ) ^ ((↑Cl : ℝ) + (1 : ℝ)) + (1 : ℝ)) + (1 : ℝ)
  ∀ (Mpad : ℝ)
    (_ : Mpad = (800 : ℝ) * (2001 : ℝ) ^ (7 : ℕ)),
  let L₄ : ℝ :=
    Real.log ((4 : ℝ) + Mpad)
  let lW : ℝ :=
    Real.log ActiveSetup.padW
  let cH : ℝ :=
    Real.log ((↑tagKρ : ℝ) ^ ((2 : ℕ) * tagKρ) + (20 : ℝ))
  ∀ (hMpad0 : (0 : ℝ) ≤ Mpad)
    (_ : (0 : ℝ) ≤ L₄)
    (_ : ℕ)
    (k : ℕ)
    (N : ℕ)
    (d₀ : ℤ)
    (B : ActiveSetup κ c')
    (_ : ∀ I ∈ B.cells, B.w I ≠ (0 : ℝ × ℝ → ℂ) → d₀ ≤ I.1 ∧ I.1 < d₀ + (↑N : ℤ))
    (p : Fin (3 : ℕ))
    (_ : (3 : ℕ) ≤ k)
    (_ : K₀ ≤ (↑k : ℝ))
    (_ : ∀ I ∈ B.cells, ∀ (J' : ℤ × ℤ), dyadicGridCell B.G I.1 I.2 ⊆ dyadicGridCell B.G J'.1
      J'.2 → dyadicGridCell B.G J'.1 J'.2 ⊆ dyadicGridCell B.G B.R.1 B.R.2 → J' ∈
      B.cells)
    (_ : B.S = (2 : ℝ))
    (hcol : B.HasColumnRep (1 : ℝ)),
  let η₀ : ℝ :=
    Real.exp ((-2 : ℝ) * (↑k : ℝ) ^ θ₀)
  ∀ (_ : ∀ I ∈ B.cells, ∀ (s s' : Fin (4 : ℕ)), s ≠ s' → PairSmall (dyadicGridLeft B.G I.1
      I.2) (dyadicGridLength B.G I.1) (B.w I) s s' (B.Y I s) (B.Y I s') ((2 : ℝ) * η₀))
    (_ : B.η = (4 : ℝ) * η₀)
    (_ : (0 : ℝ) < η₀),
  let δa : ℝ :=
    Real.exp (-(↑k : ℝ) ^ (Cb + (2 : ℕ)))
  ∀ (_ : (0 : ℝ) < dyadicGridLength B.G B.R.1)
    (_ : ¬Fintype.card B.L = (0 : ℕ)),
  let A : ActiveSetup κ c' :=
    B.padDc Mpad hMpad0
  ∀ (bf : A.BasicFamilies)
    (_ : A.SubRootProps η₀ ((↑k : ℝ) ^ Cb))
    (_ : B.cells.Nonempty)
    (_ : bf.Vtx)
    (_ : (1 : ℝ) ≤ (↑k : ℝ)),
  let Y : ℝ :=
    L₄ + (2 : ℝ) * (↑k : ℝ) ^ b
  ∀ (_ : lW + Y + (1 : ℝ) ≤ (↑k : ℝ) ^ cc)
    (_ : cH + (2 : ℝ) * (lW + Y) ≤ (↑k : ℝ) ^ cc)
    (_ : (96 : ℝ) * ((4 : ℝ) * ((6000 : ℝ) ^ (30 : ℕ) * Y ^ (30 : ℕ) + (1 : ℝ))) ≤ (↑k : ℝ) ^
      cc)
    (_ : (4 : ℝ) * ((6000 : ℝ) ^ (30 : ℕ) * Y ^ (30 : ℕ) + (1 : ℝ)) * (↑Cl : ℝ) * ((2 : ℝ) +
      ((↑Cl : ℝ) + (1 : ℝ)) * ((2 : ℝ) * α * (↑k : ℝ) ^ θ₀ + (1 : ℝ))) ^ (6 : ℕ) *
      Real.exp (((1 : ℝ) + Real.log ((2 : ℝ) * (↑k : ℝ))) ^ (2 : ℕ)) ^ Cl ≤ Real.exp (α
      * (↑k : ℝ) ^ θ₀ / (4 : ℝ)))
    (_ : (↑A.famVtxBound : ℝ) ≤ Real.exp (Y + (3 : ℝ)))
    (_ : Real.log (max A.H ActiveSetup.padW) ≤ Real.log ActiveSetup.padW + Y)
    (_ : Real.log A.Hsrc ≤ Real.log ((↑tagKρ : ℝ) ^ ((2 : ℕ) * tagKρ) + (20 : ℝ)) + (2 : ℝ) *
      (Real.log ActiveSetup.padW + Y)),
  let Tc : Finset (ℤ × ℤ) :=
    Finset.filter (A.active δa) A.cells
  ∀ (hTc : Tc = Finset.filter (A.active δa) A.cells)
    (hTcA : Tc ⊆ A.cells),
  let Mp : ℕ :=
    ⌈Real.exp (Ca * (↑k : ℝ) ^ ((3 : ℕ) * Cb + (2 : ℕ)))⌉₊
  ∀ (hMp1 : (1 : ℕ) ≤ Mp)
    (_ : ∀ (y : ℝ), (↑(Finset.card ({I ∈ A.cells | y ∈ dyadicGridCell A.G I.1 I.2 ∧ A.active
      δa I})) : ℝ) ≤ (↑Mp : ℝ))
    (hmultTc : ∀ (I : ℤ × ℤ), (Finset.card ({I' ∈ Tc | dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell
      A.G I'.1 I'.2})) ≤ Mp),
  let P : ℕ :=
    ⌈η₀ ^ (-α)⌉₊
  let τ₃ : ℝ :=
    Real.exp (-(↑k : ℝ) ^ c₃)
  ∀ (hτ0 : (0 : ℝ) < τ₃)
    (hτ1 : τ₃ ≤ (1 : ℝ))
    (_ : Real.exp ((2 : ℝ) * α * (↑k : ℝ) ^ θ₀) ≤ (↑P : ℝ))
    (_ : (↑P : ℝ) ≤ Real.exp ((2 : ℝ) * α * (↑k : ℝ) ^ θ₀) + (1 : ℝ))
    (_ : (1 : ℝ) ≤ (↑P : ℝ))
    (_ : (↑Mp : ℝ) ≤ Real.exp (Ca * (↑k : ℝ) ^ m) + (1 : ℝ))
    (fp : bf.FamParams)
    (cat : Fin (4 : ℕ) → List (CatCol bf.Vtx))
    (Kt : ℕ)
    (n : ℕ → ℝ)
    (Tmax : ℕ)
    (_ : fp.P = P)
    (hLc : fp.Lc = A.famLc)
    (hmH : fp.mH = (2 : ℕ) * A.famFuel + (2 : ℕ))
    (hMc : fp.Mc = Tc.card * Tmax + Tc.card * Tmax)
    (hHed : fp.Hed = max (Real.exp ((↑k : ℝ) ^ cc)) (max (2 : ℝ) (Real.exp ((↑A.Dg : ℝ) * ((1 :
      ℝ) + Real.log A.Hsrc + Real.log (τ₃ / ((↑A.famVtxBound : ℝ) ^ (2 : ℕ) * n (A.famLc
      + (1 : ℕ))))⁻¹) ^ A.Dg))))
    (hcolr : IsMonotoneColoring bf.admT (bf.tagDist fp.Hed) A.famVtxBound (A.fcb1 fp.Hmax)
      (ActiveSetup.cb2 fp.Hmax) Finset.univ admCellSet (dyadicGridCell A.G A.R.1 A.R.2)
      fp.ωp fp.ωh)
    (hKh : ∀ (I : ℤ × ℤ), Fintype.card (fp.HelperName I (Fin A.famVtxBound)) ≤ Kt)
    (hn0 : (2 : ℝ) * A.colBudget ≤ n (0 : ℕ))
    (hgrow : ∀ (r : ℕ), ((1 : ℝ) + ((↑fp.Lc : ℝ) + (6 : ℝ)) * (↑Mp : ℝ) * closureRatio
      A.famVtxBound Kt fp.mH Tmax (Real.exp ((↑Dst : ℝ) * ((1 : ℝ) + Real.log A.Hsrc) ^
      Dst)) τ₃) * n r ≤ n (r + (1 : ℕ)))
    (hcapH : closureRatio A.famVtxBound Kt fp.mH Tmax (Real.exp ((↑Dst : ℝ) * ((1 : ℝ) + Real.log
      A.Hsrc) ^ Dst)) τ₃ * n (fp.Lc + (4 : ℕ)) < (↑Tmax : ℝ))
    (hcats : ∀ (l : Fin (4 : ℕ)), (∀ I ∈ Tc, ∀ (w : fp.TestName I Unit), (fp.testOf l I (fun (_ :
      Unit) => bf.patIn fp.Mc p I l) w).Pass A.G (bf.origCols l) I A.csrc A.Hsrc bf.vtag
      (A.w I) (catThreshold A.famVtxBound τ₃ n (fp.testOf l I (fun (_ : Unit) =>
      bf.patIn fp.Mc p I l) w).r) fp.mH (cat l)) ∧ (∀ e ∈ cat l, e.birth ∈ Tc ∧ e.rank ≤
      fp.Lc + (5 : ℕ) ∧ ∃ R ∈ residueBox (bf.vtag e.tag).dim (9 : ℕ), ∃ (γ : ℝ), e =
      templateCol (bf.vtag e.tag) l R γ e.birth e.rank e.tag) ∧ (∀ e ∈ cat l,
      bf.occAvail (↑e.tag.2 : ℤ × ℤ) e.tag.1) ∧ (∀ (I : ℤ × ℤ), ∀ r ≤ fp.Lc + (5 : ℕ),
      (↑(mainLabels A.G fp.Mc (bf.origCols l) (cat l) I r).card : ℝ) ≤ n r) ∧ (cat
      l).length ≤ Tc.card * Tmax)
    (_ : ∀ cs ⊆ Tc, (∀ I ∈ cs, ¬∃ e ∈ fp.failRoots, dyadicGridCell A.G I.1 I.2 ⊆
      dyadicGridCell A.G e.1 e.2) → ∀ {η : ℝ}, (0 : ℝ) ≤ η → ∑ I ∈ cs, dyadicGridLength
      A.G I.1 * min η ‖A.Hf I (A.z p.castSucc I)‖ ≤ ∑ s ∈ Finset.range (searchList
      A.famFuel fp.Lc (A.basicSlot p)).length, ∑ I ∈ cs, dyadicGridLength A.G I.1 * min
      η ‖∑ G ∈ fp.groupsAt I (leafAt A.famFuel fp.Lc (A.basicSlot p) s).k, (fp.Λc I :
      (Fin (4 : ℕ) → ↥(ColumnL2 (bf.Lab ⊕ Fin fp.Mc))) → ℂ) fun (l : Fin (4 : ℕ)) =>
      (fp.ballFilt l (cat l) I G ((leafAt A.famFuel fp.Lc (A.basicSlot p) s).role l) :
      ↥(ColumnL2 (bf.Lab ⊕ Fin fp.Mc)) → ↥(ColumnL2 (bf.Lab ⊕ Fin fp.Mc))) (fp.inputL
      cat I (bf.patIn fp.Mc p I) (leafAt A.famFuel fp.Lc (A.basicSlot p) s).layers l)‖ +
      (∑ I ∈ cs, dyadicGridLength A.G I.1) * ((↑(searchList A.famFuel fp.Lc (A.basicSlot
      p)).length : ℝ) * ((9 : ℝ) * ((↑A.famVtxBound : ℝ) + (1 : ℝ)) * τ₃ * max (2 : ℝ)
      A.S ^ (4 : ℕ))))
    (_ : ∀ (x y : ℝ), Real.exp x * Real.exp y = Real.exp (x + y))
    (nHedV : (18 : ℝ) * max A.H ActiveSetup.padW ^ (2 : ℕ) ≤ Real.exp ((↑k : ℝ) ^ cc))
    (nHedτ₂ : Real.exp ((↑A.Dg : ℝ) * ((1 : ℝ) + Real.log A.Hsrc + Real.log (τ₃ / ((1 : ℝ) +
      A.colBudget * √(n (fp.Lc + (4 : ℕ))) * (A.colBudget * √((2 : ℝ) * A.colBudget +
      ((1 : ℝ) + (↑Mp : ℝ)) * n (fp.Lc + (5 : ℕ))))))⁻¹) ^ A.Dg) ≤ Real.exp ((↑k : ℝ) ^
      cc))
    (nHedτ' : Real.exp ((↑A.Dg : ℝ) * ((1 : ℝ) + Real.log A.Hsrc + Real.log ((1 : ℝ) + (↑⌈(8 : ℝ)
      * A.colBudget + n (fp.Lc + (5 : ℕ))⌉₊ : ℝ) * A.colBudget ^ (2 : ℕ))) ^ A.Dg) ≤
      Real.exp ((↑k : ℝ) ^ cc))
    (hHedge : Real.exp ((↑k : ℝ) ^ cc) ≤ fp.Hed),
  let AD : bf.AttemptData p :=
    { fp := fp, cat := cat, Tc := Tc, hTc := hTcA, Mp := Mp, hMp1 := hMp1, hmult := hmultTc,
      Dst := Dst, hst := hst, τ₃ := τ₃, hτ₃ := hτ0, hτ₃1 := hτ1, Kt := Kt, n := n, Tmax := Tmax,
      hLc := hLc, hmH := hmH, hMc := hMc, hcol := hcolr, hKh := hKh, hn0 := hn0, hgrow := hgrow,
      hcapH := hcapH, hpassM := fun l => (hcats l).1, hT := fun l => (hcats l).2.1,
      htag := fun l => (hcats l).2.2.1, hlab := fun l => (hcats l).2.2.2.1,
      hlen := fun l => (hcats l).2.2.2.2, hHedV := nHedV.trans hHedge,
      hHed2 := by rw [hHed]; exact le_max_of_le_right (le_max_left _ _),
      hHedτ₂ := nHedτ₂.trans hHedge, hHedτ' := nHedτ'.trans hHedge }
  let kD : ℝ :=
    ((2 : ℝ) * (↑Cl : ℝ) + (2 : ℝ)) * (↑k : ℝ) ^ (cc + (1 : ℕ))
  ∀ (_ : (4 : ℝ) * ((6000 : ℝ) ^ (30 : ℕ) * Y ^ (30 : ℕ) + (1 : ℝ)) * (↑Cl : ℝ) * kD ^ Cl *
      Real.exp (((1 : ℝ) + Real.log ((2 : ℝ) * (↑k : ℝ))) ^ (2 : ℕ)) ^ Cl ≤ Real.exp ((2
      : ℝ) * α * (↑k : ℝ) ^ θ₀))
    (_ : (↑Cl : ℝ) * kD ^ Cl + (2 : ℝ) ≤ Real.exp ((2 : ℝ) * α * (↑k : ℝ) ^ θ₀)),
  let δ : ℝ :=
    Real.exp (-kD)
  ∀ (_ : (4 : ℝ) * ((6000 : ℝ) ^ (30 : ℕ) * Y ^ (30 : ℕ) + (1 : ℝ)) * ((↑Cl : ℝ) * kD ^ Cl *
      (Real.exp ((2 : ℝ) * α * (↑k : ℝ) ^ θ₀) + (1 : ℝ)) ^ Cl * Real.exp (((1 : ℝ) +
      Real.log ((2 : ℝ) * (↑k : ℝ))) ^ (2 : ℕ)) ^ Cl * ((Real.exp ((2 : ℝ) * α * (↑k :
      ℝ) ^ θ₀) + (2 : ℝ)) ^ (2 : ℕ) * τ₃ + Real.exp ((↑Cl : ℝ) * (↑k : ℝ) ^ cc) *
      (Real.exp (-kD / (2 : ℝ)) + δ)) + (↑Cl : ℝ) * Real.exp (-(↑k : ℝ))) + (Real.exp
      (Ca * (↑k : ℝ) ^ m) + (1 : ℝ)) * ((4 : ℝ) * ((6000 : ℝ) ^ (30 : ℕ) * Y ^ (30 : ℕ)
      + (1 : ℝ)) * ((9 : ℝ) * (Real.exp (Y + (3 : ℝ)) + (1 : ℝ)) * τ₃ * (16 : ℝ))) ≤ η₀
      ^ min ((1 / 1200 : ℝ) / (2 : ℝ)) (α / (4 : ℝ)))
    (_ : δ = Real.exp (-kD)),
  let ρ : ℝ :=
    (1 : ℝ) / ((96 : ℝ) * (2 : ℝ) ^ A.famFuel)
  ∀ (_ : ρ = (1 : ℝ) / ((96 : ℝ) * (2 : ℝ) ^ A.famFuel))
    (_ : (0 : ℝ) ≤ (↑k : ℝ) ^ (cc + (1 : ℕ)))
    (_ : (↑k : ℝ) ^ (cc + (1 : ℕ)) ≤ kD)
    (_ : δ ≤ (1 / 8 : ℝ))
    (_ : (8 : ℝ) * (↑A.dBnd : ℝ) * δ ≤ (1 : ℝ))
    (_ : δ ^ (2 : ℕ) * AD.n (AD.fp.Lc + (5 : ℕ)) * A.colBudget ^ (2 : ℕ) ≤ (1 : ℝ))
    (_ : (0 : ℝ) < ρ)
    (_ : (2 : ℝ) ^ A.famFuel ≤ (4 : ℝ) * ((6000 : ℝ) ^ (30 : ℕ) * Y ^ (30 : ℕ) + (1 : ℝ)))
    (_ : ρ < (1 : ℝ))
    (_ : (↑k : ℝ) ^ cc ≤ kD)
    (_ : Real.log ((2 : ℝ) * ((8 : ℝ) * A.colBudget + ((1 : ℝ) + (↑AD.Mp : ℝ)) * AD.n
      (AD.fp.Lc + (5 : ℕ)))) ≤ (↑k : ℝ) ^ cc)
    (_ : Real.log ((2 : ℝ) * A.colBudget) ≤ (↑k : ℝ) ^ cc)
    (_ : (↑((2 : ℕ) * A.famFuel + (2 : ℕ)) : ℝ) ≤ (↑cc : ℝ) * (Real.log (↑k : ℝ) + (1 : ℝ)))
    (_ : (↑AD.fp.Lc : ℝ) + (6 : ℝ) ≤ (↑k : ℝ) ^ cc)
    (_ : (↑AD.fp.Hmax : ℝ) + (1 : ℝ) ≤ ((↑k : ℝ) * (↑AD.fp.P : ℝ)) ^ cc)
    (_ : (↑A.dBnd : ℝ) ≤ (↑k : ℝ) ^ cc)
    (_ : Real.log AD.fp.Hed ≤ (↑k : ℝ) ^ cc),
  ∃ (X : Finset (ℤ × ℤ)), (∀ c ∈ X, dyadicGridCell B.G c.1 c.2 ⊆ dyadicGridCell B.G
    B.R.1 B.R.2) ∧ (∀ c ∈ X, ∀ c'_1 ∈ X, c ≠ c'_1 → Disjoint (dyadicGridCell B.G c.1
    c.2) (dyadicGridCell B.G c'_1.1 c'_1.2)) ∧ ∑ c ∈ X, dyadicGridLength B.G c.1 ≤ (1
    / 4 : ℝ) * dyadicGridLength B.G B.R.1 ∧ ∑ I ∈ {I ∈ B.cells | ¬∃ c ∈ X,
    dyadicGridCell B.G I.1 I.2 ⊆ dyadicGridCell B.G c.1 c.2} with (B.active δa) I,
    dyadicGridLength B.G I.1 * min B.η ‖B.Hf I (B.z p.castSucc I)‖ ≤ Cfin * η₀ ^ cs *
    ((1 : ℝ) + finiteDepthConstant κ q N) * dyadicGridLength B.G B.R.1


open scoped Classical in
private def RetainedMinHoldsStage3Statement : Prop :=
  ∀ (κ : LocalKernelClass)
    (c' : ℕ)
    (Cb : ℕ)
    (θ₀ : ℝ)
    (_ : (1 : ℕ) ≤ c')
    (Dst : ℕ)
    (hst : SameTagBound κ (max c' ((2 : ℕ) * tagKρ)) Dst)
    (Ca : ℝ),
  let b : ℕ :=
    Cb + (1 : ℕ)
  let m : ℕ :=
    (3 : ℕ) * Cb + (2 : ℕ)
  ∀ (hmult : ∀ (k : ℕ), (1 : ℕ) ≤ k → ∀ (B : ActiveSetup κ c') (η₀ : ℝ), B.LevelProps k Cb η₀ → ∀
      (y : ℝ), (↑(Finset.card ({I ∈ B.cells | y ∈ dyadicGridCell B.G I.1 I.2 ∧ B.active
      (Real.exp (-(↑k : ℝ) ^ (Cb + (2 : ℕ)))) I})) : ℝ) ≤ Real.exp (Ca * (↑k : ℝ) ^ m)),
  let c₃ : ℕ :=
    (3 : ℕ) * Cb + (3 : ℕ)
  let c : ℕ :=
    (90 : ℕ) * b + c₃ + (100 : ℕ)
  ∀ (C : ℕ)
    (_ : ℝ),
  let Dg : ℕ :=
    Classical.choose (curvatureGraph κ (max c' (2 * tagKρ) + 1) (by omega))
  let a₀ : ℕ :=
    C + c + (1 : ℕ)
  let cc : ℕ :=
    (a₀ + (1 : ℕ)) * (Dg + (2 : ℕ))
  ∀ (_ : cc = (a₀ + (1 : ℕ)) * (Dg + (2 : ℕ)))
    (_ : (1 : ℕ) ≤ cc)
    (Cl : ℕ)
    (K₀ : ℝ)
    (_ : (1 : ℕ) ≤ Cl)
    (_ : ∀ {A : ActiveSetup κ c'} (bf : A.BasicFamilies) (k : ℕ) {η₀ E : ℝ}, A.AncClosed → (∀
      I ∈ A.cells, ∀ (s s' : Fin (4 : ℕ)), s ≠ s' → PairSmall (dyadicGridLeft A.G I.1
      I.2) (dyadicGridLength A.G I.1) (A.w I) s s' (A.Y I s) (A.Y I s') ((2 : ℝ) * η₀))
      → A.SubRootProps η₀ E → A.S = (2 : ℝ) → A.η = (4 : ℝ) * η₀ → (0 : ℝ) < η₀ →
      A.cells.Nonempty → ∀ {q : ℝ} (hq2 : (2 : ℝ) < q) (hq3 : q < (3 : ℝ)) {Nd : ℕ},
      A.DepthWin Nd → ∀ (p : Fin (3 : ℕ)) (AD : bf.AttemptData p) (x : bf.Vtx) (s : ℕ)
      {δ ρ kD : ℝ}, (0 : ℝ) < δ → δ ≤ (1 / 8 : ℝ) → (8 : ℝ) * (↑A.dBnd : ℝ) * δ ≤ (1 :
      ℝ) → δ ^ (2 : ℕ) * AD.n (AD.fp.Lc + (5 : ℕ)) * A.colBudget ^ (2 : ℕ) ≤ (1 : ℝ) →
      (0 : ℝ) < ρ → ρ < (1 : ℝ) → K₀ ≤ (↑k : ℝ) → (↑k : ℝ) ^ cc ≤ kD → Real.log ((2 : ℝ)
      * ((8 : ℝ) * A.colBudget + ((1 : ℝ) + (↑AD.Mp : ℝ)) * AD.n (AD.fp.Lc + (5 : ℕ))))
      ≤ (↑k : ℝ) ^ cc → Real.log ((2 : ℝ) * A.colBudget) ≤ (↑k : ℝ) ^ cc → (↑((2 : ℕ) *
      A.famFuel + (2 : ℕ)) : ℝ) ≤ (↑cc : ℝ) * (Real.log (↑k : ℝ) + (1 : ℝ)) → (↑AD.fp.Lc
      : ℝ) + (6 : ℝ) ≤ (↑k : ℝ) ^ cc → (↑AD.fp.Hmax : ℝ) + (1 : ℝ) ≤ ((↑k : ℝ) *
      (↑AD.fp.P : ℝ)) ^ cc → (↑A.dBnd : ℝ) ≤ (↑k : ℝ) ^ cc → Real.log AD.fp.Hed ≤ (↑k :
      ℝ) ^ cc → Real.log A.Hsrc ≤ (↑k : ℝ) ^ cc → Real.log (max A.H ActiveSetup.padW) ≤
      (↑k : ℝ) ^ cc → δ⁻¹ ≤ Real.exp kD → E ≤ (↑k : ℝ) ^ cc → ρ⁻¹ ≤ (↑k : ℝ) ^ cc → ∃ (F
      : Fin (6 : ℕ) → Finset (ℤ × ℤ)), (∀ (i : Fin (6 : ℕ)), ∀ c ∈ F i, dyadicGridCell
      A.G c.1 c.2 ⊆ dyadicGridCell A.G A.R.1 A.R.2) ∧ (∀ (i : Fin (6 : ℕ)),
      dyadicRootLength A.G (F i) ≤ (2 : ℝ) * ρ * dyadicGridLength A.G A.R.1) ∧ ∀ cs ⊆
      AD.Tc, (∀ I ∈ cs, ¬∃ c ∈ AD.fp.failRoots, dyadicGridCell A.G I.1 I.2 ⊆
      dyadicGridCell A.G c.1 c.2) → (∀ I ∈ cs, ∀ (i : Fin (6 : ℕ)), ∀ e ∈ F i,
      ¬dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G e.1 e.2) → ∑ I ∈ cs,
      dyadicGridLength A.G I.1 * min A.η ‖∑ G ∈ AD.fp.groupsAt I (leafAt A.famFuel
      AD.fp.Lc (A.basicSlot p) s).k, (AD.fp.Λc I : (Fin (4 : ℕ) → ↥(ColumnL2 (bf.Lab ⊕
      Fin AD.fp.Mc))) → ℂ) fun (l : Fin (4 : ℕ)) => (AD.fp.ballFilt l (AD.cat l) I G
      ((leafAt A.famFuel AD.fp.Lc (A.basicSlot p) s).role l) : ↥(ColumnL2 (bf.Lab ⊕ Fin
      AD.fp.Mc)) → ↥(ColumnL2 (bf.Lab ⊕ Fin AD.fp.Mc))) (AD.fp.inputL AD.cat I (bf.patIn
      AD.fp.Mc p I) (leafAt A.famFuel AD.fp.Lc (A.basicSlot p) s).layers l)‖ ≤ leafBnd
      Cl kD AD.fp.P k cc A.η η₀ AD.τ₃ δ (finiteDepthConstant κ q Nd) (nbCM κ hq2 hq3 +
      nbCUM κ hq2 hq3) q (dyadicGridLength A.G A.R.1))
    (q : ℝ)
    (hq2 : (2 : ℝ) < q)
    (hq3 : q < (3 : ℝ))
    (_ : (2 : ℝ) * ((↑Cl : ℝ) + (1 : ℝ)) * ((q - (2 : ℝ)) / (q - (1 : ℝ))) < (1 / 8 : ℝ)),
  let α : ℝ :=
    (1 / 1200 : ℝ) / ((4 : ℝ) * ((↑Cl : ℝ) + (1 : ℝ) + (1 : ℝ)))
  let cs : ℝ :=
    min ((1 / 1200 : ℝ) / (2 : ℝ)) (α / (4 : ℝ))
  ∀ (_ : cs = min ((1 / 1200 : ℝ) / (2 : ℝ)) (α / (4 : ℝ))),
  let Cq : ℝ :=
    nbCM κ hq2 hq3 + nbCUM κ hq2 hq3
  ∀ (_ : (0 : ℝ) ≤ Cq),
  let Cfin : ℝ :=
    ((3 : ℝ) + Cq) * ((2 : ℝ) ^ ((↑Cl : ℝ) + (1 : ℝ)) + (1 : ℝ)) + (1 : ℝ)
  ∀ (Mpad : ℝ)
    (_ : Mpad = (800 : ℝ) * (2001 : ℝ) ^ (7 : ℕ)),
  let L₄ : ℝ :=
    Real.log ((4 : ℝ) + Mpad)
  let lW : ℝ :=
    Real.log ActiveSetup.padW
  let cH : ℝ :=
    Real.log ((↑tagKρ : ℝ) ^ ((2 : ℕ) * tagKρ) + (20 : ℝ))
  ∀ (hMpad0 : (0 : ℝ) ≤ Mpad)
    (_ : (0 : ℝ) ≤ L₄)
    (_ : ℕ)
    (k : ℕ)
    (N : ℕ)
    (d₀ : ℤ)
    (B : ActiveSetup κ c')
    (_ : ∀ I ∈ B.cells, B.w I ≠ (0 : ℝ × ℝ → ℂ) → d₀ ≤ I.1 ∧ I.1 < d₀ + (↑N : ℤ))
    (p : Fin (3 : ℕ))
    (_ : (3 : ℕ) ≤ k)
    (_ : K₀ ≤ (↑k : ℝ))
    (_ : ∀ I ∈ B.cells, ∀ (J' : ℤ × ℤ), dyadicGridCell B.G I.1 I.2 ⊆ dyadicGridCell B.G J'.1
      J'.2 → dyadicGridCell B.G J'.1 J'.2 ⊆ dyadicGridCell B.G B.R.1 B.R.2 → J' ∈
      B.cells)
    (_ : B.S = (2 : ℝ))
    (hcol : B.HasColumnRep (1 : ℝ)),
  let η₀ : ℝ :=
    Real.exp ((-2 : ℝ) * (↑k : ℝ) ^ θ₀)
  ∀ (_ : ∀ I ∈ B.cells, ∀ (s s' : Fin (4 : ℕ)), s ≠ s' → PairSmall (dyadicGridLeft B.G I.1
      I.2) (dyadicGridLength B.G I.1) (B.w I) s s' (B.Y I s) (B.Y I s') ((2 : ℝ) * η₀))
    (_ : B.η = (4 : ℝ) * η₀)
    (_ : (0 : ℝ) < η₀),
  let δa : ℝ :=
    Real.exp (-(↑k : ℝ) ^ (Cb + (2 : ℕ)))
  ∀ (_ : (0 : ℝ) < dyadicGridLength B.G B.R.1)
    (_ : ¬Fintype.card B.L = (0 : ℕ)),
  let A : ActiveSetup κ c' :=
    B.padDc Mpad hMpad0
  ∀ (bf : A.BasicFamilies)
    (_ : A.SubRootProps η₀ ((↑k : ℝ) ^ Cb))
    (_ : B.cells.Nonempty)
    (_ : bf.Vtx)
    (_ : (1 : ℝ) ≤ (↑k : ℝ)),
  let Y : ℝ :=
    L₄ + (2 : ℝ) * (↑k : ℝ) ^ b
  ∀ (_ : Real.log (2 : ℝ) + Y ≤ (↑k : ℝ) ^ cc)
    (_ : (20 : ℝ) * ((6000 : ℝ) ^ (30 : ℕ) * Y ^ (30 : ℕ) + (1 : ℝ)) + (61 : ℝ) ≤ (↑k : ℝ) ^
      cc)
    (_ : lW + Y + (1 : ℝ) ≤ (↑k : ℝ) ^ cc)
    (_ : cH + (2 : ℝ) * (lW + Y) ≤ (↑k : ℝ) ^ cc)
    (_ : (96 : ℝ) * ((4 : ℝ) * ((6000 : ℝ) ^ (30 : ℕ) * Y ^ (30 : ℕ) + (1 : ℝ))) ≤ (↑k : ℝ) ^
      cc)
    (_ : (4 : ℝ) * ((6000 : ℝ) ^ (30 : ℕ) * Y ^ (30 : ℕ) + (1 : ℝ)) * (↑Cl : ℝ) * ((2 : ℝ) +
      ((↑Cl : ℝ) + (1 : ℝ)) * ((2 : ℝ) * α * (↑k : ℝ) ^ θ₀ + (1 : ℝ))) ^ (6 : ℕ) *
      Real.exp (((1 : ℝ) + Real.log ((2 : ℝ) * (↑k : ℝ))) ^ (2 : ℕ)) ^ Cl ≤ Real.exp (α
      * (↑k : ℝ) ^ θ₀ / (4 : ℝ)))
    (_ : A.colBudget ≤ Real.exp Y)
    (_ : (↑A.famVtxBound : ℝ) ≤ Real.exp (Y + (3 : ℝ)))
    (_ : (↑A.famLc : ℝ) ≤ (6000 : ℝ) ^ (30 : ℕ) * Y ^ (30 : ℕ) + (1 : ℝ))
    (_ : Real.log (max A.H ActiveSetup.padW) ≤ Real.log ActiveSetup.padW + Y)
    (_ : Real.log A.Hsrc ≤ Real.log ((↑tagKρ : ℝ) ^ ((2 : ℕ) * tagKρ) + (20 : ℝ)) + (2 : ℝ) *
      (Real.log ActiveSetup.padW + Y))
    (_ : (2 : ℝ) ≤ A.colBudget),
  let Tc : Finset (ℤ × ℤ) :=
    Finset.filter (A.active δa) A.cells
  ∀ (hTc : Tc = Finset.filter (A.active δa) A.cells)
    (hTcA : Tc ⊆ A.cells),
  let Mp : ℕ :=
    ⌈Real.exp (Ca * (↑k : ℝ) ^ ((3 : ℕ) * Cb + (2 : ℕ)))⌉₊
  ∀ (hMp1 : (1 : ℕ) ≤ Mp)
    (_ : ∀ (y : ℝ), (↑(Finset.card ({I ∈ A.cells | y ∈ dyadicGridCell A.G I.1 I.2 ∧ A.active
      δa I})) : ℝ) ≤ (↑Mp : ℝ))
    (hmultTc : ∀ (I : ℤ × ℤ), (Finset.card ({I' ∈ Tc | dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell
      A.G I'.1 I'.2})) ≤ Mp),
  let P : ℕ :=
    ⌈η₀ ^ (-α)⌉₊
  let τ₃ : ℝ :=
    Real.exp (-(↑k : ℝ) ^ c₃)
  ∀ (_ : τ₃ = Real.exp (-(↑k : ℝ) ^ c₃))
    (hτ0 : (0 : ℝ) < τ₃)
    (hτ1 : τ₃ ≤ (1 : ℝ))
    (_ : Real.exp ((2 : ℝ) * α * (↑k : ℝ) ^ θ₀) ≤ (↑P : ℝ))
    (_ : (↑P : ℝ) ≤ Real.exp ((2 : ℝ) * α * (↑k : ℝ) ^ θ₀) + (1 : ℝ))
    (_ : (1 : ℝ) ≤ (↑P : ℝ))
    (_ : (↑((2 : ℕ) * A.famFuel + (2 : ℕ)) : ℝ) ≤ (↑c : ℝ) * (Real.log (↑k : ℝ) + (1 : ℝ)))
    (_ : (↑Mp : ℝ) ≤ Real.exp (Ca * (↑k : ℝ) ^ m) + (1 : ℝ))
    (fp : bf.FamParams)
    (cat : Fin (4 : ℕ) → List (CatCol bf.Vtx))
    (Kt : ℕ)
    (n : ℕ → ℝ)
    (Tmax : ℕ)
    (_ : fp.P = P)
    (hLc : fp.Lc = A.famLc)
    (hmH : fp.mH = (2 : ℕ) * A.famFuel + (2 : ℕ))
    (_ : fp.Hmax = A.famHmax P)
    (hMc : fp.Mc = Tc.card * Tmax + Tc.card * Tmax)
    (hHed : fp.Hed = max (Real.exp ((↑k : ℝ) ^ cc)) (max (2 : ℝ) (Real.exp ((↑A.Dg : ℝ) * ((1 :
      ℝ) + Real.log A.Hsrc + Real.log (τ₃ / ((↑A.famVtxBound : ℝ) ^ (2 : ℕ) * n (A.famLc
      + (1 : ℕ))))⁻¹) ^ A.Dg))))
    (hcolr : IsMonotoneColoring bf.admT (bf.tagDist fp.Hed) A.famVtxBound (A.fcb1 fp.Hmax)
      (ActiveSetup.cb2 fp.Hmax) Finset.univ admCellSet (dyadicGridCell A.G A.R.1 A.R.2)
      fp.ωp fp.ωh)
    (hKh : ∀ (I : ℤ × ℤ), Fintype.card (fp.HelperName I (Fin A.famVtxBound)) ≤ Kt)
    (hn0 : (2 : ℝ) * A.colBudget ≤ n (0 : ℕ))
    (hgrow : ∀ (r : ℕ), ((1 : ℝ) + ((↑fp.Lc : ℝ) + (6 : ℝ)) * (↑Mp : ℝ) * closureRatio
      A.famVtxBound Kt fp.mH Tmax (Real.exp ((↑Dst : ℝ) * ((1 : ℝ) + Real.log A.Hsrc) ^
      Dst)) τ₃) * n r ≤ n (r + (1 : ℕ)))
    (hcapH : closureRatio A.famVtxBound Kt fp.mH Tmax (Real.exp ((↑Dst : ℝ) * ((1 : ℝ) + Real.log
      A.Hsrc) ^ Dst)) τ₃ * n (fp.Lc + (4 : ℕ)) < (↑Tmax : ℝ))
    (hcats : ∀ (l : Fin (4 : ℕ)), (∀ I ∈ Tc, ∀ (w : fp.TestName I Unit), (fp.testOf l I (fun (_ :
      Unit) => bf.patIn fp.Mc p I l) w).Pass A.G (bf.origCols l) I A.csrc A.Hsrc bf.vtag
      (A.w I) (catThreshold A.famVtxBound τ₃ n (fp.testOf l I (fun (_ : Unit) =>
      bf.patIn fp.Mc p I l) w).r) fp.mH (cat l)) ∧ (∀ e ∈ cat l, e.birth ∈ Tc ∧ e.rank ≤
      fp.Lc + (5 : ℕ) ∧ ∃ R ∈ residueBox (bf.vtag e.tag).dim (9 : ℕ), ∃ (γ : ℝ), e =
      templateCol (bf.vtag e.tag) l R γ e.birth e.rank e.tag) ∧ (∀ e ∈ cat l,
      bf.occAvail (↑e.tag.2 : ℤ × ℤ) e.tag.1) ∧ (∀ (I : ℤ × ℤ), ∀ r ≤ fp.Lc + (5 : ℕ),
      (↑(mainLabels A.G fp.Mc (bf.origCols l) (cat l) I r).card : ℝ) ≤ n r) ∧ (cat
      l).length ≤ Tc.card * Tmax)
    (_ : ∀ cs ⊆ Tc, (∀ I ∈ cs, ¬∃ e ∈ fp.failRoots, dyadicGridCell A.G I.1 I.2 ⊆
      dyadicGridCell A.G e.1 e.2) → ∀ {η : ℝ}, (0 : ℝ) ≤ η → ∑ I ∈ cs, dyadicGridLength
      A.G I.1 * min η ‖A.Hf I (A.z p.castSucc I)‖ ≤ ∑ s ∈ Finset.range (searchList
      A.famFuel fp.Lc (A.basicSlot p)).length, ∑ I ∈ cs, dyadicGridLength A.G I.1 * min
      η ‖∑ G ∈ fp.groupsAt I (leafAt A.famFuel fp.Lc (A.basicSlot p) s).k, (fp.Λc I :
      (Fin (4 : ℕ) → ↥(ColumnL2 (bf.Lab ⊕ Fin fp.Mc))) → ℂ) fun (l : Fin (4 : ℕ)) =>
      (fp.ballFilt l (cat l) I G ((leafAt A.famFuel fp.Lc (A.basicSlot p) s).role l) :
      ↥(ColumnL2 (bf.Lab ⊕ Fin fp.Mc)) → ↥(ColumnL2 (bf.Lab ⊕ Fin fp.Mc))) (fp.inputL
      cat I (bf.patIn fp.Mc p I) (leafAt A.famFuel fp.Lc (A.basicSlot p) s).layers l)‖ +
      (∑ I ∈ cs, dyadicGridLength A.G I.1) * ((↑(searchList A.famFuel fp.Lc (A.basicSlot
      p)).length : ℝ) * ((9 : ℝ) * ((↑A.famVtxBound : ℝ) + (1 : ℝ)) * τ₃ * max (2 : ℝ)
      A.S ^ (4 : ℕ))))
    (_ : ∀ (r : ℕ), (0 : ℝ) ≤ n r)
    (_ : ∀ (r : ℕ), (4 : ℝ) ≤ n r)
    (_ : ∀ r ≤ fp.Lc + (5 : ℕ), n r ≤ Real.exp ((↑k : ℝ) ^ C)),
  let T : ℝ :=
    Y + (↑k : ℝ) ^ C + Ca * (↑k : ℝ) ^ m + (2 : ℝ)
  ∀ (_ : Real.log (20 : ℝ) + T ≤ (↑k : ℝ) ^ cc)
    (_ : (0 : ℝ) ≤ (↑k : ℝ) ^ C)
    (_ : (0 : ℝ) ≤ Ca * (↑k : ℝ) ^ m)
    (_ : (0 : ℝ) ≤ Y)
    (_ : ∀ (x y : ℝ), Real.exp x * Real.exp y = Real.exp (x + y))
    (_ : (2 : ℝ) ≤ Real.log A.Hsrc)
    (_ : ∀ (w : ℝ), (0 : ℝ) ≤ w → w ≤ (1 : ℝ) + (cH + (2 : ℝ) * (lW + Y)) + Real.log (6 : ℝ)
      + (3 : ℝ) * (Y + (↑k : ℝ) ^ C + Ca * (↑k : ℝ) ^ m + (2 : ℝ)) + (↑k : ℝ) ^ c₃ + (2
      : ℝ) * (Y + (3 : ℝ)) → (↑A.Dg : ℝ) * w ^ A.Dg ≤ (↑k : ℝ) ^ cc)
    (_ : (0 : ℝ) ≤ Real.log (6 : ℝ))
    (nHedV : (18 : ℝ) * max A.H ActiveSetup.padW ^ (2 : ℕ) ≤ Real.exp ((↑k : ℝ) ^ cc))
    (nHedτ₂ : Real.exp ((↑A.Dg : ℝ) * ((1 : ℝ) + Real.log A.Hsrc + Real.log (τ₃ / ((1 : ℝ) +
      A.colBudget * √(n (fp.Lc + (4 : ℕ))) * (A.colBudget * √((2 : ℝ) * A.colBudget +
      ((1 : ℝ) + (↑Mp : ℝ)) * n (fp.Lc + (5 : ℕ))))))⁻¹) ^ A.Dg) ≤ Real.exp ((↑k : ℝ) ^
      cc))
    (nHedτ' : Real.exp ((↑A.Dg : ℝ) * ((1 : ℝ) + Real.log A.Hsrc + Real.log ((1 : ℝ) + (↑⌈(8 : ℝ)
      * A.colBudget + n (fp.Lc + (5 : ℕ))⌉₊ : ℝ) * A.colBudget ^ (2 : ℕ))) ^ A.Dg) ≤
      Real.exp ((↑k : ℝ) ^ cc))
    (hHedge : Real.exp ((↑k : ℝ) ^ cc) ≤ fp.Hed),
  let AD : bf.AttemptData p :=
    { fp := fp, cat := cat, Tc := Tc, hTc := hTcA, Mp := Mp, hMp1 := hMp1, hmult := hmultTc,
      Dst := Dst, hst := hst, τ₃ := τ₃, hτ₃ := hτ0, hτ₃1 := hτ1, Kt := Kt, n := n, Tmax := Tmax,
      hLc := hLc, hmH := hmH, hMc := hMc, hcol := hcolr, hKh := hKh, hn0 := hn0, hgrow := hgrow,
      hcapH := hcapH, hpassM := fun l => (hcats l).1, hT := fun l => (hcats l).2.1,
      htag := fun l => (hcats l).2.2.1, hlab := fun l => (hcats l).2.2.2.1,
      hlen := fun l => (hcats l).2.2.2.2, hHedV := nHedV.trans hHedge,
      hHed2 := by rw [hHed]; exact le_max_of_le_right (le_max_left _ _),
      hHedτ₂ := nHedτ₂.trans hHedge, hHedτ' := nHedτ'.trans hHedge }
  let kD : ℝ :=
    ((2 : ℝ) * (↑Cl : ℝ) + (2 : ℝ)) * (↑k : ℝ) ^ (cc + (1 : ℕ))
  ∀ (_ : (4 : ℝ) * ((6000 : ℝ) ^ (30 : ℕ) * Y ^ (30 : ℕ) + (1 : ℝ)) * (↑Cl : ℝ) * kD ^ Cl *
      Real.exp (((1 : ℝ) + Real.log ((2 : ℝ) * (↑k : ℝ))) ^ (2 : ℕ)) ^ Cl ≤ Real.exp ((2
      : ℝ) * α * (↑k : ℝ) ^ θ₀))
    (_ : (↑Cl : ℝ) * kD ^ Cl + (2 : ℝ) ≤ Real.exp ((2 : ℝ) * α * (↑k : ℝ) ^ θ₀)),
  let δ : ℝ :=
    Real.exp (-kD)
  ∀ (_ : (4 : ℝ) * ((6000 : ℝ) ^ (30 : ℕ) * Y ^ (30 : ℕ) + (1 : ℝ)) * ((↑Cl : ℝ) * kD ^ Cl *
      (Real.exp ((2 : ℝ) * α * (↑k : ℝ) ^ θ₀) + (1 : ℝ)) ^ Cl * Real.exp (((1 : ℝ) +
      Real.log ((2 : ℝ) * (↑k : ℝ))) ^ (2 : ℕ)) ^ Cl * ((Real.exp ((2 : ℝ) * α * (↑k :
      ℝ) ^ θ₀) + (2 : ℝ)) ^ (2 : ℕ) * τ₃ + Real.exp ((↑Cl : ℝ) * (↑k : ℝ) ^ cc) *
      (Real.exp (-kD / (2 : ℝ)) + δ)) + (↑Cl : ℝ) * Real.exp (-(↑k : ℝ))) + (Real.exp
      (Ca * (↑k : ℝ) ^ m) + (1 : ℝ)) * ((4 : ℝ) * ((6000 : ℝ) ^ (30 : ℕ) * Y ^ (30 : ℕ)
      + (1 : ℝ)) * ((9 : ℝ) * (Real.exp (Y + (3 : ℝ)) + (1 : ℝ)) * τ₃ * (16 : ℝ))) ≤ η₀
      ^ min ((1 / 1200 : ℝ) / (2 : ℝ)) (α / (4 : ℝ)))
    (_ : δ = Real.exp (-kD)),
  let ρ : ℝ :=
    (1 : ℝ) / ((96 : ℝ) * (2 : ℝ) ^ A.famFuel)
  ∀ (_ : ρ = (1 : ℝ) / ((96 : ℝ) * (2 : ℝ) ^ A.famFuel))
    (_ : (↑k : ℝ) ^ cc ≤ (↑k : ℝ) ^ (cc + (1 : ℕ)))
    (_ : (0 : ℝ) ≤ (↑k : ℝ) ^ (cc + (1 : ℕ)))
    (_ : (↑k : ℝ) ^ (cc + (1 : ℕ)) ≤ kD)
    (_ : δ ≤ (1 / 8 : ℝ))
    (_ : (↑A.dBnd : ℝ) ≤ lW + Y + (1 : ℝ))
    (_ : (8 : ℝ) * (↑A.dBnd : ℝ) * δ ≤ (1 : ℝ))
    (_ : δ ^ (2 : ℕ) * AD.n (AD.fp.Lc + (5 : ℕ)) * A.colBudget ^ (2 : ℕ) ≤ (1 : ℝ))
    (_ : (0 : ℝ) < ρ)
    (_ : (2 : ℝ) ^ A.famFuel ≤ (4 : ℝ) * ((6000 : ℝ) ^ (30 : ℕ) * Y ^ (30 : ℕ) + (1 : ℝ))),
  ∃ (X : Finset (ℤ × ℤ)), (∀ c ∈ X, dyadicGridCell B.G c.1 c.2 ⊆ dyadicGridCell B.G
    B.R.1 B.R.2) ∧ (∀ c ∈ X, ∀ c'_1 ∈ X, c ≠ c'_1 → Disjoint (dyadicGridCell B.G c.1
    c.2) (dyadicGridCell B.G c'_1.1 c'_1.2)) ∧ ∑ c ∈ X, dyadicGridLength B.G c.1 ≤ (1
    / 4 : ℝ) * dyadicGridLength B.G B.R.1 ∧ ∑ I ∈ {I ∈ B.cells | ¬∃ c ∈ X,
    dyadicGridCell B.G I.1 I.2 ⊆ dyadicGridCell B.G c.1 c.2} with (B.active δa) I,
    dyadicGridLength B.G I.1 * min B.η ‖B.Hf I (B.z p.castSucc I)‖ ≤ Cfin * η₀ ^ cs *
    ((1 : ℝ) + finiteDepthConstant κ q N) * dyadicGridLength B.G B.R.1


open scoped Classical in
private def RetainedMinHoldsStage2Statement : Prop :=
  ∀ (κ : LocalKernelClass)
    (c' : ℕ)
    (Cb : ℕ)
    (θ₀ : ℝ)
    (_ : (1 : ℕ) ≤ c')
    (Dst : ℕ)
    (_ : SameTagBound κ (max c' ((2 : ℕ) * tagKρ)) Dst)
    (Ca : ℝ)
    (_ : (0 : ℝ) < Ca),
  let b : ℕ :=
    Cb + (1 : ℕ)
  let m : ℕ :=
    (3 : ℕ) * Cb + (2 : ℕ)
  ∀ (_ : ∀ (k : ℕ), (1 : ℕ) ≤ k → ∀ (B : ActiveSetup κ c') (η₀ : ℝ), B.LevelProps k Cb η₀ → ∀
      (y : ℝ), (↑(Finset.card ({I ∈ B.cells | y ∈ dyadicGridCell B.G I.1 I.2 ∧ B.active
      (Real.exp (-(↑k : ℝ) ^ (Cb + (2 : ℕ)))) I})) : ℝ) ≤ Real.exp (Ca * (↑k : ℝ) ^ m)),
  let c₃ : ℕ :=
    (3 : ℕ) * Cb + (3 : ℕ)
  let c : ℕ :=
    (90 : ℕ) * b + c₃ + (100 : ℕ)
  ∀ (C : ℕ)
    (_ : ℝ),
  let Dg : ℕ :=
    Classical.choose (curvatureGraph κ (max c' (2 * tagKρ) + 1) (by omega))
  let a₀ : ℕ :=
    C + c + (1 : ℕ)
  let cc : ℕ :=
    (a₀ + (1 : ℕ)) * (Dg + (2 : ℕ))
  ∀ (_ : cc = (a₀ + (1 : ℕ)) * (Dg + (2 : ℕ)))
    (_ : (1 : ℕ) ≤ cc)
    (Cl : ℕ)
    (K₀ : ℝ)
    (_ : (1 : ℕ) ≤ Cl)
    (_ : ∀ {A : ActiveSetup κ c'} (bf : A.BasicFamilies) (k : ℕ) {η₀ E : ℝ}, A.AncClosed → (∀
      I ∈ A.cells, ∀ (s s' : Fin (4 : ℕ)), s ≠ s' → PairSmall (dyadicGridLeft A.G I.1
      I.2) (dyadicGridLength A.G I.1) (A.w I) s s' (A.Y I s) (A.Y I s') ((2 : ℝ) * η₀))
      → A.SubRootProps η₀ E → A.S = (2 : ℝ) → A.η = (4 : ℝ) * η₀ → (0 : ℝ) < η₀ →
      A.cells.Nonempty → ∀ {q : ℝ} (hq2 : (2 : ℝ) < q) (hq3 : q < (3 : ℝ)) {Nd : ℕ},
      A.DepthWin Nd → ∀ (p : Fin (3 : ℕ)) (AD : bf.AttemptData p) (x : bf.Vtx) (s : ℕ)
      {δ ρ kD : ℝ}, (0 : ℝ) < δ → δ ≤ (1 / 8 : ℝ) → (8 : ℝ) * (↑A.dBnd : ℝ) * δ ≤ (1 :
      ℝ) → δ ^ (2 : ℕ) * AD.n (AD.fp.Lc + (5 : ℕ)) * A.colBudget ^ (2 : ℕ) ≤ (1 : ℝ) →
      (0 : ℝ) < ρ → ρ < (1 : ℝ) → K₀ ≤ (↑k : ℝ) → (↑k : ℝ) ^ cc ≤ kD → Real.log ((2 : ℝ)
      * ((8 : ℝ) * A.colBudget + ((1 : ℝ) + (↑AD.Mp : ℝ)) * AD.n (AD.fp.Lc + (5 : ℕ))))
      ≤ (↑k : ℝ) ^ cc → Real.log ((2 : ℝ) * A.colBudget) ≤ (↑k : ℝ) ^ cc → (↑((2 : ℕ) *
      A.famFuel + (2 : ℕ)) : ℝ) ≤ (↑cc : ℝ) * (Real.log (↑k : ℝ) + (1 : ℝ)) → (↑AD.fp.Lc
      : ℝ) + (6 : ℝ) ≤ (↑k : ℝ) ^ cc → (↑AD.fp.Hmax : ℝ) + (1 : ℝ) ≤ ((↑k : ℝ) *
      (↑AD.fp.P : ℝ)) ^ cc → (↑A.dBnd : ℝ) ≤ (↑k : ℝ) ^ cc → Real.log AD.fp.Hed ≤ (↑k :
      ℝ) ^ cc → Real.log A.Hsrc ≤ (↑k : ℝ) ^ cc → Real.log (max A.H ActiveSetup.padW) ≤
      (↑k : ℝ) ^ cc → δ⁻¹ ≤ Real.exp kD → E ≤ (↑k : ℝ) ^ cc → ρ⁻¹ ≤ (↑k : ℝ) ^ cc → ∃ (F
      : Fin (6 : ℕ) → Finset (ℤ × ℤ)), (∀ (i : Fin (6 : ℕ)), ∀ c ∈ F i, dyadicGridCell
      A.G c.1 c.2 ⊆ dyadicGridCell A.G A.R.1 A.R.2) ∧ (∀ (i : Fin (6 : ℕ)),
      dyadicRootLength A.G (F i) ≤ (2 : ℝ) * ρ * dyadicGridLength A.G A.R.1) ∧ ∀ cs ⊆
      AD.Tc, (∀ I ∈ cs, ¬∃ c ∈ AD.fp.failRoots, dyadicGridCell A.G I.1 I.2 ⊆
      dyadicGridCell A.G c.1 c.2) → (∀ I ∈ cs, ∀ (i : Fin (6 : ℕ)), ∀ e ∈ F i,
      ¬dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G e.1 e.2) → ∑ I ∈ cs,
      dyadicGridLength A.G I.1 * min A.η ‖∑ G ∈ AD.fp.groupsAt I (leafAt A.famFuel
      AD.fp.Lc (A.basicSlot p) s).k, (AD.fp.Λc I : (Fin (4 : ℕ) → ↥(ColumnL2 (bf.Lab ⊕
      Fin AD.fp.Mc))) → ℂ) fun (l : Fin (4 : ℕ)) => (AD.fp.ballFilt l (AD.cat l) I G
      ((leafAt A.famFuel AD.fp.Lc (A.basicSlot p) s).role l) : ↥(ColumnL2 (bf.Lab ⊕ Fin
      AD.fp.Mc)) → ↥(ColumnL2 (bf.Lab ⊕ Fin AD.fp.Mc))) (AD.fp.inputL AD.cat I (bf.patIn
      AD.fp.Mc p I) (leafAt A.famFuel AD.fp.Lc (A.basicSlot p) s).layers l)‖ ≤ leafBnd
      Cl kD AD.fp.P k cc A.η η₀ AD.τ₃ δ (finiteDepthConstant κ q Nd) (nbCM κ hq2 hq3 +
      nbCUM κ hq2 hq3) q (dyadicGridLength A.G A.R.1))
    (q : ℝ)
    (hq2 : (2 : ℝ) < q)
    (hq3 : q < (3 : ℝ))
    (_ : (2 : ℝ) * ((↑Cl : ℝ) + (1 : ℝ)) * ((q - (2 : ℝ)) / (q - (1 : ℝ))) < (1 / 8 : ℝ)),
  let α : ℝ :=
    (1 / 1200 : ℝ) / ((4 : ℝ) * ((↑Cl : ℝ) + (1 : ℝ) + (1 : ℝ)))
  let cs : ℝ :=
    min ((1 / 1200 : ℝ) / (2 : ℝ)) (α / (4 : ℝ))
  ∀ (_ : cs = min ((1 / 1200 : ℝ) / (2 : ℝ)) (α / (4 : ℝ))),
  let Cq : ℝ :=
    nbCM κ hq2 hq3 + nbCUM κ hq2 hq3
  ∀ (_ : (0 : ℝ) ≤ Cq),
  let Cfin : ℝ :=
    ((3 : ℝ) + Cq) * ((2 : ℝ) ^ ((↑Cl : ℝ) + (1 : ℝ)) + (1 : ℝ)) + (1 : ℝ)
  ∀ (Mpad : ℝ)
    (_ : Mpad = (800 : ℝ) * (2001 : ℝ) ^ (7 : ℕ)),
  let L₄ : ℝ :=
    Real.log ((4 : ℝ) + Mpad)
  let lW : ℝ :=
    Real.log ActiveSetup.padW
  let cH : ℝ :=
    Real.log ((↑tagKρ : ℝ) ^ ((2 : ℕ) * tagKρ) + (20 : ℝ))
  ∀ (hMpad0 : (0 : ℝ) ≤ Mpad)
    (_ : (0 : ℝ) ≤ L₄)
    (_ : (1 : ℝ) ≤ ActiveSetup.padW)
    (_ : ℕ)
    (k : ℕ)
    (N : ℕ)
    (d₀ : ℤ)
    (B : ActiveSetup κ c')
    (_ : ∀ I ∈ B.cells, B.w I ≠ (0 : ℝ × ℝ → ℂ) → d₀ ≤ I.1 ∧ I.1 < d₀ + (↑N : ℤ))
    (p : Fin (3 : ℕ))
    (_ : (3 : ℕ) ≤ k)
    (_ : (↑Cl : ℝ) * (((2 : ℝ) * (↑Cl : ℝ) + (2 : ℝ)) * (↑k : ℝ) ^ (cc + (1 : ℕ))) ^ Cl + (2
      : ℝ) ≤ Real.exp ((2 : ℝ) * α * (↑k : ℝ) ^ θ₀))
    (_ : K₀ ≤ (↑k : ℝ))
    (_ : ∀ I ∈ B.cells, ∀ (J' : ℤ × ℤ), dyadicGridCell B.G I.1 I.2 ⊆ dyadicGridCell B.G J'.1
      J'.2 → dyadicGridCell B.G J'.1 J'.2 ⊆ dyadicGridCell B.G B.R.1 B.R.2 → J' ∈
      B.cells)
    (_ : (1 : ℝ) ≤ B.H)
    (_ : B.S = (2 : ℝ))
    (_ : B.HasColumnRep (1 : ℝ)),
  let η₀ : ℝ :=
    Real.exp ((-2 : ℝ) * (↑k : ℝ) ^ θ₀)
  ∀ (_ : ∀ I ∈ B.cells, ∀ (s s' : Fin (4 : ℕ)), s ≠ s' → PairSmall (dyadicGridLeft B.G I.1
      I.2) (dyadicGridLength B.G I.1) (B.w I) s s' (B.Y I s) (B.Y I s') ((2 : ℝ) * η₀))
    (_ : B.η = (4 : ℝ) * η₀)
    (_ : (0 : ℝ) < η₀),
  let δa : ℝ :=
    Real.exp (-(↑k : ℝ) ^ (Cb + (2 : ℕ)))
  ∀ (_ : (0 : ℝ) < dyadicGridLength B.G B.R.1)
    (_ : ¬Fintype.card B.L = (0 : ℕ)),
  let A : ActiveSetup κ c' :=
    B.padDc Mpad hMpad0
  ∀ (bf : A.BasicFamilies)
    (_ : A.SubRootProps η₀ ((↑k : ℝ) ^ Cb))
    (_ : B.cells.Nonempty)
    (_ : bf.Vtx)
    (_ : (1 : ℝ) ≤ (↑k : ℝ)),
  let Y : ℝ :=
    L₄ + (2 : ℝ) * (↑k : ℝ) ^ b
  ∀ (_ : Real.log (18 : ℝ) + (2 : ℝ) * (lW + Y) ≤ (↑k : ℝ) ^ cc)
    (_ : (↑Dg : ℝ) * ((1 : ℝ) + (cH + (2 : ℝ) * (lW + Y)) + Real.log (6 : ℝ) + (3 : ℝ) * (Y +
      (↑k : ℝ) ^ C + Ca * (↑k : ℝ) ^ m + (2 : ℝ)) + (↑k : ℝ) ^ c₃ + (2 : ℝ) * (Y + (3 :
      ℝ))) ^ Dg ≤ (↑k : ℝ) ^ cc)
    (_ : (↑k : ℝ) ^ C + (2 : ℝ) * Y ≤ (↑k : ℝ) ^ (cc + (1 : ℕ)))
    (_ : Real.log (20 : ℝ) + (Y + (↑k : ℝ) ^ C + Ca * (↑k : ℝ) ^ m + (2 : ℝ)) ≤ (↑k : ℝ) ^ cc)
    (_ : Real.log (2 : ℝ) + Y ≤ (↑k : ℝ) ^ cc)
    (_ : (20 : ℝ) * ((6000 : ℝ) ^ (30 : ℕ) * Y ^ (30 : ℕ) + (1 : ℝ)) + (61 : ℝ) ≤ (↑k : ℝ) ^
      cc)
    (_ : lW + Y + (1 : ℝ) ≤ (↑k : ℝ) ^ cc)
    (_ : cH + (2 : ℝ) * (lW + Y) ≤ (↑k : ℝ) ^ cc)
    (_ : (96 : ℝ) * ((4 : ℝ) * ((6000 : ℝ) ^ (30 : ℕ) * Y ^ (30 : ℕ) + (1 : ℝ))) ≤ (↑k : ℝ) ^
      cc)
    (_ : (8 : ℝ) * (lW + Y + (1 : ℝ)) ≤ Real.exp (((2 : ℝ) * (↑Cl : ℝ) + (2 : ℝ)) * (↑k : ℝ)
      ^ (cc + (1 : ℕ))))
    (_ : (4 : ℝ) * ((6000 : ℝ) ^ (30 : ℕ) * Y ^ (30 : ℕ) + (1 : ℝ)) * (↑Cl : ℝ) * (((2 : ℝ) *
      (↑Cl : ℝ) + (2 : ℝ)) * (↑k : ℝ) ^ (cc + (1 : ℕ))) ^ Cl * Real.exp (((1 : ℝ) +
      Real.log ((2 : ℝ) * (↑k : ℝ))) ^ (2 : ℕ)) ^ Cl ≤ Real.exp ((2 : ℝ) * α * (↑k : ℝ)
      ^ θ₀))
    (_ : (4 : ℝ) * ((6000 : ℝ) ^ (30 : ℕ) * Y ^ (30 : ℕ) + (1 : ℝ)) * (↑Cl : ℝ) * ((2 : ℝ) +
      ((↑Cl : ℝ) + (1 : ℝ)) * ((2 : ℝ) * α * (↑k : ℝ) ^ θ₀ + (1 : ℝ))) ^ (6 : ℕ) *
      Real.exp (((1 : ℝ) + Real.log ((2 : ℝ) * (↑k : ℝ))) ^ (2 : ℕ)) ^ Cl ≤ Real.exp (α
      * (↑k : ℝ) ^ θ₀ / (4 : ℝ)))
    (_ : (1 : ℝ) ≤ Y)
    (_ : A.colBudget ≤ Real.exp Y)
    (_ : (↑A.famVtxBound : ℝ) ≤ Real.exp (Y + (3 : ℝ)))
    (_ : (↑A.famLc : ℝ) ≤ (6000 : ℝ) ^ (30 : ℕ) * Y ^ (30 : ℕ) + (1 : ℝ))
    (_ : (2 : ℝ) ^ A.famFuel ≤ (4 : ℝ) * (↑A.famLc : ℝ))
    (_ : Real.log (max A.H ActiveSetup.padW) ≤ Real.log ActiveSetup.padW + Y)
    (_ : Real.log A.Hsrc ≤ Real.log ((↑tagKρ : ℝ) ^ ((2 : ℕ) * tagKρ) + (20 : ℝ)) + (2 : ℝ) *
      (Real.log ActiveSetup.padW + Y))
    (_ : (2 : ℝ) ≤ A.colBudget),
  let Tc : Finset (ℤ × ℤ) :=
    Finset.filter (A.active δa) A.cells
  ∀ (_ : Tc = Finset.filter (A.active δa) A.cells)
    (_ : Tc ⊆ A.cells),
  let Mp : ℕ :=
    ⌈Real.exp (Ca * (↑k : ℝ) ^ ((3 : ℕ) * Cb + (2 : ℕ)))⌉₊
  ∀ (_ : (1 : ℕ) ≤ Mp)
    (_ : ∀ (y : ℝ), (↑(Finset.card ({I ∈ A.cells | y ∈ dyadicGridCell A.G I.1 I.2 ∧ A.active
      δa I})) : ℝ) ≤ (↑Mp : ℝ))
    (_ : ∀ (I : ℤ × ℤ), (Finset.card ({I' ∈ Tc | dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell
      A.G I'.1 I'.2})) ≤ Mp),
  let P : ℕ :=
    ⌈η₀ ^ (-α)⌉₊
  let τ₃ : ℝ :=
    Real.exp (-(↑k : ℝ) ^ c₃)
  ∀ (_ : (4 : ℝ) * ((6000 : ℝ) ^ (30 : ℕ) * Y ^ (30 : ℕ) + (1 : ℝ)) * ((↑Cl : ℝ) * (((2 : ℝ)
      * (↑Cl : ℝ) + (2 : ℝ)) * (↑k : ℝ) ^ (cc + (1 : ℕ))) ^ Cl * (Real.exp ((2 : ℝ) * α
      * (↑k : ℝ) ^ θ₀) + (1 : ℝ)) ^ Cl * Real.exp (((1 : ℝ) + Real.log ((2 : ℝ) * (↑k :
      ℝ))) ^ (2 : ℕ)) ^ Cl * ((Real.exp ((2 : ℝ) * α * (↑k : ℝ) ^ θ₀) + (2 : ℝ)) ^ (2 :
      ℕ) * τ₃ + Real.exp ((↑Cl : ℝ) * (↑k : ℝ) ^ cc) * (Real.exp (-(((2 : ℝ) * (↑Cl : ℝ)
      + (2 : ℝ)) * (↑k : ℝ) ^ (cc + (1 : ℕ))) / (2 : ℝ)) + Real.exp (-(((2 : ℝ) * (↑Cl :
      ℝ) + (2 : ℝ)) * (↑k : ℝ) ^ (cc + (1 : ℕ)))))) + (↑Cl : ℝ) * Real.exp (-(↑k : ℝ)))
      + (Real.exp (Ca * (↑k : ℝ) ^ m) + (1 : ℝ)) * ((4 : ℝ) * ((6000 : ℝ) ^ (30 : ℕ) * Y
      ^ (30 : ℕ) + (1 : ℝ)) * ((9 : ℝ) * (Real.exp (Y + (3 : ℝ)) + (1 : ℝ)) * τ₃ * (16 :
      ℝ))) ≤ η₀ ^ min ((1 / 1200 : ℝ) / (2 : ℝ)) (α / (4 : ℝ)))
    (_ : τ₃ = Real.exp (-(↑k : ℝ) ^ c₃))
    (_ : (0 : ℝ) < τ₃)
    (_ : τ₃ ≤ (1 : ℝ))
    (_ : Real.exp ((2 : ℝ) * α * (↑k : ℝ) ^ θ₀) ≤ (↑P : ℝ))
    (_ : (↑P : ℝ) ≤ Real.exp ((2 : ℝ) * α * (↑k : ℝ) ^ θ₀) + (1 : ℝ))
    (_ : (1 : ℝ) ≤ (↑P : ℝ))
    (_ : (↑((2 : ℕ) * A.famFuel + (2 : ℕ)) : ℝ) ≤ (↑c : ℝ) * (Real.log (↑k : ℝ) + (1 : ℝ)))
    (_ : (↑Mp : ℝ) ≤ Real.exp (Ca * (↑k : ℝ) ^ m) + (1 : ℝ))
    (fp : bf.FamParams)
    (cat : Fin (4 : ℕ) → List (CatCol bf.Vtx))
    (Kt : ℕ)
    (n : ℕ → ℝ)
    (Tmax : ℕ)
    (_ : fp.P = P)
    (_ : fp.Lc = A.famLc)
    (_ : fp.mH = (2 : ℕ) * A.famFuel + (2 : ℕ))
    (_ : fp.Hmax = A.famHmax P)
    (_ : fp.Mc = Tc.card * Tmax + Tc.card * Tmax)
    (_ : fp.Hed = max (Real.exp ((↑k : ℝ) ^ cc)) (max (2 : ℝ) (Real.exp ((↑A.Dg : ℝ) * ((1 :
      ℝ) + Real.log A.Hsrc + Real.log (τ₃ / ((↑A.famVtxBound : ℝ) ^ (2 : ℕ) * n (A.famLc
      + (1 : ℕ))))⁻¹) ^ A.Dg))))
    (_ : IsMonotoneColoring bf.admT (bf.tagDist fp.Hed) A.famVtxBound (A.fcb1 fp.Hmax)
      (ActiveSetup.cb2 fp.Hmax) Finset.univ admCellSet (dyadicGridCell A.G A.R.1 A.R.2)
      fp.ωp fp.ωh)
    (_ : ∀ (I : ℤ × ℤ), Fintype.card (fp.HelperName I (Fin A.famVtxBound)) ≤ Kt)
    (_ : (2 : ℝ) * A.colBudget ≤ n (0 : ℕ))
    (_ : ∀ (r : ℕ), ((1 : ℝ) + ((↑fp.Lc : ℝ) + (6 : ℝ)) * (↑Mp : ℝ) * closureRatio
      A.famVtxBound Kt fp.mH Tmax (Real.exp ((↑Dst : ℝ) * ((1 : ℝ) + Real.log A.Hsrc) ^
      Dst)) τ₃) * n r ≤ n (r + (1 : ℕ)))
    (_ : closureRatio A.famVtxBound Kt fp.mH Tmax (Real.exp ((↑Dst : ℝ) * ((1 : ℝ) + Real.log
      A.Hsrc) ^ Dst)) τ₃ * n (fp.Lc + (4 : ℕ)) < (↑Tmax : ℝ))
    (_ : ∀ (l : Fin (4 : ℕ)), (∀ I ∈ Tc, ∀ (w : fp.TestName I Unit), (fp.testOf l I (fun (_ :
      Unit) => bf.patIn fp.Mc p I l) w).Pass A.G (bf.origCols l) I A.csrc A.Hsrc bf.vtag
      (A.w I) (catThreshold A.famVtxBound τ₃ n (fp.testOf l I (fun (_ : Unit) =>
      bf.patIn fp.Mc p I l) w).r) fp.mH (cat l)) ∧ (∀ e ∈ cat l, e.birth ∈ Tc ∧ e.rank ≤
      fp.Lc + (5 : ℕ) ∧ ∃ R ∈ residueBox (bf.vtag e.tag).dim (9 : ℕ), ∃ (γ : ℝ), e =
      templateCol (bf.vtag e.tag) l R γ e.birth e.rank e.tag) ∧ (∀ e ∈ cat l,
      bf.occAvail (↑e.tag.2 : ℤ × ℤ) e.tag.1) ∧ (∀ (I : ℤ × ℤ), ∀ r ≤ fp.Lc + (5 : ℕ),
      (↑(mainLabels A.G fp.Mc (bf.origCols l) (cat l) I r).card : ℝ) ≤ n r) ∧ (cat
      l).length ≤ Tc.card * Tmax)
    (_ : ∀ cs ⊆ Tc, (∀ I ∈ cs, ¬∃ e ∈ fp.failRoots, dyadicGridCell A.G I.1 I.2 ⊆
      dyadicGridCell A.G e.1 e.2) → ∀ {η : ℝ}, (0 : ℝ) ≤ η → ∑ I ∈ cs, dyadicGridLength
      A.G I.1 * min η ‖A.Hf I (A.z p.castSucc I)‖ ≤ ∑ s ∈ Finset.range (searchList
      A.famFuel fp.Lc (A.basicSlot p)).length, ∑ I ∈ cs, dyadicGridLength A.G I.1 * min
      η ‖∑ G ∈ fp.groupsAt I (leafAt A.famFuel fp.Lc (A.basicSlot p) s).k, (fp.Λc I :
      (Fin (4 : ℕ) → ↥(ColumnL2 (bf.Lab ⊕ Fin fp.Mc))) → ℂ) fun (l : Fin (4 : ℕ)) =>
      (fp.ballFilt l (cat l) I G ((leafAt A.famFuel fp.Lc (A.basicSlot p) s).role l) :
      ↥(ColumnL2 (bf.Lab ⊕ Fin fp.Mc)) → ↥(ColumnL2 (bf.Lab ⊕ Fin fp.Mc))) (fp.inputL
      cat I (bf.patIn fp.Mc p I) (leafAt A.famFuel fp.Lc (A.basicSlot p) s).layers l)‖ +
      (∑ I ∈ cs, dyadicGridLength A.G I.1) * ((↑(searchList A.famFuel fp.Lc (A.basicSlot
      p)).length : ℝ) * ((9 : ℝ) * ((↑A.famVtxBound : ℝ) + (1 : ℝ)) * τ₃ * max (2 : ℝ)
      A.S ^ (4 : ℕ))))
    (_ : ∀ (r : ℕ), (0 : ℝ) ≤ n r)
    (_ : ∀ (r : ℕ), (4 : ℝ) ≤ n r)
    (_ : ∀ r ≤ fp.Lc + (5 : ℕ), n r ≤ Real.exp ((↑k : ℝ) ^ C))
    (_ : ∀ (x : ℝ), (1 : ℝ) ≤ x → √x ≤ x),
  ∃ (X : Finset (ℤ × ℤ)), (∀ c ∈ X, dyadicGridCell B.G c.1 c.2 ⊆ dyadicGridCell B.G
    B.R.1 B.R.2) ∧ (∀ c ∈ X, ∀ c'_1 ∈ X, c ≠ c'_1 → Disjoint (dyadicGridCell B.G c.1
    c.2) (dyadicGridCell B.G c'_1.1 c'_1.2)) ∧ ∑ c ∈ X, dyadicGridLength B.G c.1 ≤ (1
    / 4 : ℝ) * dyadicGridLength B.G B.R.1 ∧ ∑ I ∈ {I ∈ B.cells | ¬∃ c ∈ X,
    dyadicGridCell B.G I.1 I.2 ⊆ dyadicGridCell B.G c.1 c.2} with (B.active δa) I,
    dyadicGridLength B.G I.1 * min B.η ‖B.Hf I (B.z p.castSucc I)‖ ≤ Cfin * η₀ ^ cs *
    ((1 : ℝ) + finiteDepthConstant κ q N) * dyadicGridLength B.G B.R.1


open scoped Classical in
private def RetainedMinHoldsStage1Statement : Prop :=
  ∀ (κ : LocalKernelClass)
    (c' : ℕ)
    (Cb : ℕ)
    (θ₀ : ℝ)
    (_ : (1 : ℕ) ≤ c')
    (Dst : ℕ)
    (_ : SameTagBound κ (max c' ((2 : ℕ) * tagKρ)) Dst)
    (Ca : ℝ)
    (_ : (0 : ℝ) < Ca),
  let b : ℕ :=
    Cb + (1 : ℕ)
  let m : ℕ :=
    (3 : ℕ) * Cb + (2 : ℕ)
  ∀ (_ : ∀ (k : ℕ), (1 : ℕ) ≤ k → ∀ (B : ActiveSetup κ c') (η₀ : ℝ), B.LevelProps k Cb η₀ → ∀
      (y : ℝ), (↑(Finset.card ({I ∈ B.cells | y ∈ dyadicGridCell B.G I.1 I.2 ∧ B.active
      (Real.exp (-(↑k : ℝ) ^ (Cb + (2 : ℕ)))) I})) : ℝ) ≤ Real.exp (Ca * (↑k : ℝ) ^ m)),
  let c₃ : ℕ :=
    (3 : ℕ) * Cb + (3 : ℕ)
  let c : ℕ :=
    (90 : ℕ) * b + c₃ + (100 : ℕ)
  ∀ (C : ℕ)
    (k₀ : ℝ)
    (_ : ∀ {κ : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ c₀} (bf : A.BasicFamilies) {k :
      ℝ}, k₀ ≤ k → SameTagBound κ A.csrc Dst → ∀ (p : Fin (3 : ℕ)), ∀ Tc ⊆ A.cells, ∀ (x
      : bf.Vtx) (P : ℕ), (0 : ℕ) < P → ∀ {τ₃ : ℝ} {Mp : ℕ} (Bh : Type) [Fintype Bh]
      (Hlow : ℕ → (ℕ → ℝ) → ℕ → ℝ) (Mx : ℕ → (ℕ → ℝ) → ℕ → ℕ), (↑A.famLc : ℝ) + (6 : ℝ)
      ≤ k ^ c → (↑A.famVtxBound : ℝ) ≤ Real.exp (k ^ c) → (↑(A.famHmax P) : ℝ) + (1 : ℝ)
      ≤ Real.exp (k ^ c) → (↑((2 : ℕ) * A.famFuel + (2 : ℕ)) : ℝ) ≤ (↑c : ℝ) * (Real.log
      k + (1 : ℝ)) → Real.log A.Hsrc ≤ k ^ c → (0 : ℝ) < τ₃ → τ₃ ≤ (1 : ℝ) → τ₃⁻¹ ≤
      Real.exp (k ^ c) → (1 : ℕ) ≤ Mp → (↑Mp : ℝ) ≤ Real.exp (k ^ c) → (2 : ℝ) *
      A.colBudget ≤ Real.exp (k ^ c) → (↑(Fintype.card Bh) : ℝ) ≤ Real.exp (k ^ c) → (∀
      (I : ℤ × ℤ), (Finset.card ({I' ∈ Tc | dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell
      A.G I'.1 I'.2})) ≤ Mp) → ∃ (fp : bf.FamParams) (cat : Fin (4 : ℕ) → List (CatCol
      bf.Vtx)) (Kt : ℕ) (n : ℕ → ℝ) (Tmax : ℕ), fp.P = P ∧ fp.Lc = A.famLc ∧ fp.mH = (2
      : ℕ) * A.famFuel + (2 : ℕ) ∧ fp.Hmax = A.famHmax P ∧ fp.Mc = Tc.card * Tmax + Mx
      Kt n Tmax ∧ fp.Hed = max (Hlow Kt n Tmax) (max (2 : ℝ) (Real.exp ((↑A.Dg : ℝ) *
      ((1 : ℝ) + Real.log A.Hsrc + Real.log (τ₃ / ((↑A.famVtxBound : ℝ) ^ (2 : ℕ) * n
      (A.famLc + (1 : ℕ))))⁻¹) ^ A.Dg))) ∧ IsMonotoneColoring bf.admT (bf.tagDist
      fp.Hed) A.famVtxBound (A.fcb1 fp.Hmax) (ActiveSetup.cb2 fp.Hmax) Finset.univ
      admCellSet (dyadicGridCell A.G A.R.1 A.R.2) fp.ωp fp.ωh ∧ (∀ (I : ℤ × ℤ),
      Fintype.card (fp.TestName I Unit) ≤ Kt) ∧ (∀ (I : ℤ × ℤ), Fintype.card
      (fp.HelperName I Bh) ≤ Kt) ∧ Real.log (↑Kt : ℝ) ≤ k ^ C ∧ (2 : ℝ) * A.colBudget ≤
      n (0 : ℕ) ∧ (∀ (r : ℕ), ((1 : ℝ) + ((↑fp.Lc : ℝ) + (6 : ℝ)) * (↑Mp : ℝ) *
      closureRatio A.famVtxBound Kt fp.mH Tmax (Real.exp ((↑Dst : ℝ) * ((1 : ℝ) +
      Real.log A.Hsrc) ^ Dst)) τ₃) * n r ≤ n (r + (1 : ℕ))) ∧ n (fp.Lc + (5 : ℕ)) ≤
      (↑Tmax : ℝ) ∧ closureRatio A.famVtxBound Kt fp.mH Tmax (Real.exp ((↑Dst : ℝ) * ((1
      : ℝ) + Real.log A.Hsrc) ^ Dst)) τ₃ * n (fp.Lc + (4 : ℕ)) < (↑Tmax : ℝ) ∧ Real.log
      (n (fp.Lc + (5 : ℕ))) ≤ k ^ C ∧ Real.log (↑Tmax : ℝ) ≤ k ^ C ∧ (∀ (l : Fin (4 :
      ℕ)), (∀ I ∈ Tc, ∀ (w : fp.TestName I Unit), (fp.testOf l I (fun (_ : Unit) =>
      bf.patIn fp.Mc p I l) w).Pass A.G (bf.origCols l) I A.csrc A.Hsrc bf.vtag (A.w I)
      (catThreshold A.famVtxBound τ₃ n (fp.testOf l I (fun (_ : Unit) => bf.patIn fp.Mc
      p I l) w).r) fp.mH (cat l)) ∧ (∀ e ∈ cat l, e.birth ∈ Tc ∧ e.rank ≤ fp.Lc + (5 :
      ℕ) ∧ ∃ R ∈ residueBox (bf.vtag e.tag).dim (9 : ℕ), ∃ (γ : ℝ), e = templateCol
      (bf.vtag e.tag) l R γ e.birth e.rank e.tag) ∧ (∀ e ∈ cat l, bf.occAvail (↑e.tag.2
      : ℤ × ℤ) e.tag.1) ∧ (∀ (I : ℤ × ℤ), ∀ r ≤ fp.Lc + (5 : ℕ), (↑(mainLabels A.G fp.Mc
      (bf.origCols l) (cat l) I r).card : ℝ) ≤ n r) ∧ (cat l).length ≤ Tc.card * Tmax) ∧
      ∀ cs ⊆ Tc, (∀ I ∈ cs, ¬∃ e ∈ fp.failRoots, dyadicGridCell A.G I.1 I.2 ⊆
      dyadicGridCell A.G e.1 e.2) → ∀ {η : ℝ}, (0 : ℝ) ≤ η → ∑ I ∈ cs, dyadicGridLength
      A.G I.1 * min η ‖A.Hf I (A.z p.castSucc I)‖ ≤ ∑ s ∈ Finset.range (searchList
      A.famFuel fp.Lc (A.basicSlot p)).length, ∑ I ∈ cs, dyadicGridLength A.G I.1 * min
      η ‖∑ G ∈ fp.groupsAt I (leafAt A.famFuel fp.Lc (A.basicSlot p) s).k, (fp.Λc I :
      (Fin (4 : ℕ) → ↥(ColumnL2 (bf.Lab ⊕ Fin fp.Mc))) → ℂ) fun (l : Fin (4 : ℕ)) =>
      (fp.ballFilt l (cat l) I G ((leafAt A.famFuel fp.Lc (A.basicSlot p) s).role l) :
      ↥(ColumnL2 (bf.Lab ⊕ Fin fp.Mc)) → ↥(ColumnL2 (bf.Lab ⊕ Fin fp.Mc))) (fp.inputL
      cat I (bf.patIn fp.Mc p I) (leafAt A.famFuel fp.Lc (A.basicSlot p) s).layers l)‖ +
      (∑ I ∈ cs, dyadicGridLength A.G I.1) * ((↑(searchList A.famFuel fp.Lc (A.basicSlot
      p)).length : ℝ) * ((9 : ℝ) * ((↑A.famVtxBound : ℝ) + (1 : ℝ)) * τ₃ * max (2 : ℝ)
      A.S ^ (4 : ℕ)))),
  let Dg : ℕ :=
    Classical.choose (curvatureGraph κ (max c' (2 * tagKρ) + 1) (by omega))
  let a₀ : ℕ :=
    C + c + (1 : ℕ)
  let cc : ℕ :=
    (a₀ + (1 : ℕ)) * (Dg + (2 : ℕ))
  ∀ (_ : cc = (a₀ + (1 : ℕ)) * (Dg + (2 : ℕ)))
    (_ : (1 : ℕ) ≤ cc)
    (Cl : ℕ)
    (K₀ : ℝ)
    (_ : (1 : ℕ) ≤ Cl)
    (_ : ∀ {A : ActiveSetup κ c'} (bf : A.BasicFamilies) (k : ℕ) {η₀ E : ℝ}, A.AncClosed → (∀
      I ∈ A.cells, ∀ (s s' : Fin (4 : ℕ)), s ≠ s' → PairSmall (dyadicGridLeft A.G I.1
      I.2) (dyadicGridLength A.G I.1) (A.w I) s s' (A.Y I s) (A.Y I s') ((2 : ℝ) * η₀))
      → A.SubRootProps η₀ E → A.S = (2 : ℝ) → A.η = (4 : ℝ) * η₀ → (0 : ℝ) < η₀ →
      A.cells.Nonempty → ∀ {q : ℝ} (hq2 : (2 : ℝ) < q) (hq3 : q < (3 : ℝ)) {Nd : ℕ},
      A.DepthWin Nd → ∀ (p : Fin (3 : ℕ)) (AD : bf.AttemptData p) (x : bf.Vtx) (s : ℕ)
      {δ ρ kD : ℝ}, (0 : ℝ) < δ → δ ≤ (1 / 8 : ℝ) → (8 : ℝ) * (↑A.dBnd : ℝ) * δ ≤ (1 :
      ℝ) → δ ^ (2 : ℕ) * AD.n (AD.fp.Lc + (5 : ℕ)) * A.colBudget ^ (2 : ℕ) ≤ (1 : ℝ) →
      (0 : ℝ) < ρ → ρ < (1 : ℝ) → K₀ ≤ (↑k : ℝ) → (↑k : ℝ) ^ cc ≤ kD → Real.log ((2 : ℝ)
      * ((8 : ℝ) * A.colBudget + ((1 : ℝ) + (↑AD.Mp : ℝ)) * AD.n (AD.fp.Lc + (5 : ℕ))))
      ≤ (↑k : ℝ) ^ cc → Real.log ((2 : ℝ) * A.colBudget) ≤ (↑k : ℝ) ^ cc → (↑((2 : ℕ) *
      A.famFuel + (2 : ℕ)) : ℝ) ≤ (↑cc : ℝ) * (Real.log (↑k : ℝ) + (1 : ℝ)) → (↑AD.fp.Lc
      : ℝ) + (6 : ℝ) ≤ (↑k : ℝ) ^ cc → (↑AD.fp.Hmax : ℝ) + (1 : ℝ) ≤ ((↑k : ℝ) *
      (↑AD.fp.P : ℝ)) ^ cc → (↑A.dBnd : ℝ) ≤ (↑k : ℝ) ^ cc → Real.log AD.fp.Hed ≤ (↑k :
      ℝ) ^ cc → Real.log A.Hsrc ≤ (↑k : ℝ) ^ cc → Real.log (max A.H ActiveSetup.padW) ≤
      (↑k : ℝ) ^ cc → δ⁻¹ ≤ Real.exp kD → E ≤ (↑k : ℝ) ^ cc → ρ⁻¹ ≤ (↑k : ℝ) ^ cc → ∃ (F
      : Fin (6 : ℕ) → Finset (ℤ × ℤ)), (∀ (i : Fin (6 : ℕ)), ∀ c ∈ F i, dyadicGridCell
      A.G c.1 c.2 ⊆ dyadicGridCell A.G A.R.1 A.R.2) ∧ (∀ (i : Fin (6 : ℕ)),
      dyadicRootLength A.G (F i) ≤ (2 : ℝ) * ρ * dyadicGridLength A.G A.R.1) ∧ ∀ cs ⊆
      AD.Tc, (∀ I ∈ cs, ¬∃ c ∈ AD.fp.failRoots, dyadicGridCell A.G I.1 I.2 ⊆
      dyadicGridCell A.G c.1 c.2) → (∀ I ∈ cs, ∀ (i : Fin (6 : ℕ)), ∀ e ∈ F i,
      ¬dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G e.1 e.2) → ∑ I ∈ cs,
      dyadicGridLength A.G I.1 * min A.η ‖∑ G ∈ AD.fp.groupsAt I (leafAt A.famFuel
      AD.fp.Lc (A.basicSlot p) s).k, (AD.fp.Λc I : (Fin (4 : ℕ) → ↥(ColumnL2 (bf.Lab ⊕
      Fin AD.fp.Mc))) → ℂ) fun (l : Fin (4 : ℕ)) => (AD.fp.ballFilt l (AD.cat l) I G
      ((leafAt A.famFuel AD.fp.Lc (A.basicSlot p) s).role l) : ↥(ColumnL2 (bf.Lab ⊕ Fin
      AD.fp.Mc)) → ↥(ColumnL2 (bf.Lab ⊕ Fin AD.fp.Mc))) (AD.fp.inputL AD.cat I (bf.patIn
      AD.fp.Mc p I) (leafAt A.famFuel AD.fp.Lc (A.basicSlot p) s).layers l)‖ ≤ leafBnd
      Cl kD AD.fp.P k cc A.η η₀ AD.τ₃ δ (finiteDepthConstant κ q Nd) (nbCM κ hq2 hq3 +
      nbCUM κ hq2 hq3) q (dyadicGridLength A.G A.R.1))
    (q : ℝ)
    (hq2 : (2 : ℝ) < q)
    (hq3 : q < (3 : ℝ))
    (_ : (2 : ℝ) * ((↑Cl : ℝ) + (1 : ℝ)) * ((q - (2 : ℝ)) / (q - (1 : ℝ))) < (1 / 8 : ℝ)),
  let α : ℝ :=
    (1 / 1200 : ℝ) / ((4 : ℝ) * ((↑Cl : ℝ) + (1 : ℝ) + (1 : ℝ)))
  let cs : ℝ :=
    min ((1 / 1200 : ℝ) / (2 : ℝ)) (α / (4 : ℝ))
  ∀ (_ : cs = min ((1 / 1200 : ℝ) / (2 : ℝ)) (α / (4 : ℝ))),
  let Cq : ℝ :=
    nbCM κ hq2 hq3 + nbCUM κ hq2 hq3
  ∀ (_ : (0 : ℝ) ≤ Cq),
  let Cfin : ℝ :=
    ((3 : ℝ) + Cq) * ((2 : ℝ) ^ ((↑Cl : ℝ) + (1 : ℝ)) + (1 : ℝ)) + (1 : ℝ)
  ∀ (Mpad : ℝ)
    (_ : Mpad = (800 : ℝ) * (2001 : ℝ) ^ (7 : ℕ)),
  let L₄ : ℝ :=
    Real.log ((4 : ℝ) + Mpad)
  ∀ (_ : L₄ = Real.log ((4 : ℝ) + Mpad)),
  let lW : ℝ :=
    Real.log ActiveSetup.padW
  let cH : ℝ :=
    Real.log ((↑tagKρ : ℝ) ^ ((2 : ℕ) * tagKρ) + (20 : ℝ))
  ∀ (hMpad0 : (0 : ℝ) ≤ Mpad)
    (_ : (0 : ℝ) ≤ L₄)
    (_ : (1 : ℝ) ≤ ActiveSetup.padW)
    (_ : ℕ)
    (k : ℕ)
    (N : ℕ)
    (d₀ : ℤ)
    (B : ActiveSetup κ c')
    (_ : ∀ I ∈ B.cells, B.w I ≠ (0 : ℝ × ℝ → ℂ) → d₀ ≤ I.1 ∧ I.1 < d₀ + (↑N : ℤ))
    (p : Fin (3 : ℕ))
    (_ : (3 : ℕ) ≤ k)
    (_ : (6000 : ℝ) ^ (30 : ℕ) * (L₄ + (2 : ℝ) * (↑k : ℝ) ^ b) ^ (30 : ℕ) + (1 : ℝ) + (6 : ℝ)
      ≤ (↑k : ℝ) ^ c)
    (_ : L₄ + (2 : ℝ) * (↑k : ℝ) ^ b + (3 : ℝ) ≤ (↑k : ℝ) ^ c)
    (_ : (2 : ℝ) * (Real.log ((4 : ℝ) * ((6000 : ℝ) ^ (30 : ℕ) * (L₄ + (2 : ℝ) * (↑k : ℝ) ^
      b) ^ (30 : ℕ) + (1 : ℝ))) / Real.log (2 : ℝ)) + (2 : ℝ) ≤ (↑c : ℝ) * (Real.log (↑k
      : ℝ) + (1 : ℝ)))
    (_ : cH + (2 : ℝ) * (lW + (L₄ + (2 : ℝ) * (↑k : ℝ) ^ b)) ≤ (↑k : ℝ) ^ c)
    (_ : Real.exp (Ca * (↑k : ℝ) ^ m) + (1 : ℝ) ≤ Real.exp ((↑k : ℝ) ^ c))
    (_ : (2 : ℝ) * Real.exp (L₄ + (2 : ℝ) * (↑k : ℝ) ^ b) ≤ Real.exp ((↑k : ℝ) ^ c))
    (_ : Real.log (18 : ℝ) + (2 : ℝ) * (lW + (L₄ + (2 : ℝ) * (↑k : ℝ) ^ b)) ≤ (↑k : ℝ) ^ cc)
    (_ : (↑Dg : ℝ) * ((1 : ℝ) + (cH + (2 : ℝ) * (lW + (L₄ + (2 : ℝ) * (↑k : ℝ) ^ b))) +
      Real.log (6 : ℝ) + (3 : ℝ) * (L₄ + (2 : ℝ) * (↑k : ℝ) ^ b + (↑k : ℝ) ^ C + Ca *
      (↑k : ℝ) ^ m + (2 : ℝ)) + (↑k : ℝ) ^ c₃ + (2 : ℝ) * (L₄ + (2 : ℝ) * (↑k : ℝ) ^ b +
      (3 : ℝ))) ^ Dg ≤ (↑k : ℝ) ^ cc)
    (_ : (↑k : ℝ) ^ C + (2 : ℝ) * (L₄ + (2 : ℝ) * (↑k : ℝ) ^ b) ≤ (↑k : ℝ) ^ (cc + (1 : ℕ)))
    (_ : Real.log (20 : ℝ) + (L₄ + (2 : ℝ) * (↑k : ℝ) ^ b + (↑k : ℝ) ^ C + Ca * (↑k : ℝ) ^ m
      + (2 : ℝ)) ≤ (↑k : ℝ) ^ cc)
    (_ : Real.log (2 : ℝ) + (L₄ + (2 : ℝ) * (↑k : ℝ) ^ b) ≤ (↑k : ℝ) ^ cc)
    (_ : (20 : ℝ) * ((6000 : ℝ) ^ (30 : ℕ) * (L₄ + (2 : ℝ) * (↑k : ℝ) ^ b) ^ (30 : ℕ) + (1 :
      ℝ)) + (61 : ℝ) ≤ (↑k : ℝ) ^ cc)
    (_ : lW + (L₄ + (2 : ℝ) * (↑k : ℝ) ^ b) + (1 : ℝ) ≤ (↑k : ℝ) ^ cc)
    (_ : cH + (2 : ℝ) * (lW + (L₄ + (2 : ℝ) * (↑k : ℝ) ^ b)) ≤ (↑k : ℝ) ^ cc)
    (_ : (96 : ℝ) * ((4 : ℝ) * ((6000 : ℝ) ^ (30 : ℕ) * (L₄ + (2 : ℝ) * (↑k : ℝ) ^ b) ^ (30 :
      ℕ) + (1 : ℝ))) ≤ (↑k : ℝ) ^ cc)
    (_ : (Real.exp ((2 : ℝ) * α * (↑k : ℝ) ^ θ₀) + (1 : ℝ)) * ((20 : ℝ) * ((6000 : ℝ) ^ (30 :
      ℕ) * (L₄ + (2 : ℝ) * (↑k : ℝ) ^ b) ^ (30 : ℕ) + (1 : ℝ)) + (60 : ℝ)) + (1 : ℝ) ≤
      Real.exp ((↑k : ℝ) ^ c))
    (_ : (8 : ℝ) * (lW + (L₄ + (2 : ℝ) * (↑k : ℝ) ^ b) + (1 : ℝ)) ≤ Real.exp (((2 : ℝ) * (↑Cl
      : ℝ) + (2 : ℝ)) * (↑k : ℝ) ^ (cc + (1 : ℕ))))
    (_ : (4 : ℝ) * ((6000 : ℝ) ^ (30 : ℕ) * (L₄ + (2 : ℝ) * (↑k : ℝ) ^ b) ^ (30 : ℕ) + (1 :
      ℝ)) * (↑Cl : ℝ) * (((2 : ℝ) * (↑Cl : ℝ) + (2 : ℝ)) * (↑k : ℝ) ^ (cc + (1 : ℕ))) ^
      Cl * Real.exp (((1 : ℝ) + Real.log ((2 : ℝ) * (↑k : ℝ))) ^ (2 : ℕ)) ^ Cl ≤
      Real.exp ((2 : ℝ) * α * (↑k : ℝ) ^ θ₀))
    (_ : (↑Cl : ℝ) * (((2 : ℝ) * (↑Cl : ℝ) + (2 : ℝ)) * (↑k : ℝ) ^ (cc + (1 : ℕ))) ^ Cl + (2
      : ℝ) ≤ Real.exp ((2 : ℝ) * α * (↑k : ℝ) ^ θ₀))
    (_ : (4 : ℝ) * ((6000 : ℝ) ^ (30 : ℕ) * (L₄ + (2 : ℝ) * (↑k : ℝ) ^ b) ^ (30 : ℕ) + (1 :
      ℝ)) * (↑Cl : ℝ) * ((2 : ℝ) + ((↑Cl : ℝ) + (1 : ℝ)) * ((2 : ℝ) * α * (↑k : ℝ) ^ θ₀
      + (1 : ℝ))) ^ (6 : ℕ) * Real.exp (((1 : ℝ) + Real.log ((2 : ℝ) * (↑k : ℝ))) ^ (2 :
      ℕ)) ^ Cl ≤ Real.exp (α * (↑k : ℝ) ^ θ₀ / (4 : ℝ)))
    (_ : k₀ ≤ (↑k : ℝ))
    (_ : K₀ ≤ (↑k : ℝ))
    (_ : ∀ I ∈ B.cells, ∀ (J' : ℤ × ℤ), dyadicGridCell B.G I.1 I.2 ⊆ dyadicGridCell B.G J'.1
      J'.2 → dyadicGridCell B.G J'.1 J'.2 ⊆ dyadicGridCell B.G B.R.1 B.R.2 → J' ∈
      B.cells)
    (_ : (1 : ℝ) ≤ B.H)
    (_ : B.H ≤ Real.exp ((↑k : ℝ) ^ Cb))
    (_ : B.Dc ≤ Real.exp ((↑k : ℝ) ^ Cb))
    (_ : (↑(Fintype.card B.L) : ℝ) ≤ Real.exp ((↑k : ℝ) ^ Cb))
    (_ : B.S = (2 : ℝ))
    (_ : B.HasColumnRep (1 : ℝ)),
  let η₀ : ℝ :=
    Real.exp ((-2 : ℝ) * (↑k : ℝ) ^ θ₀)
  ∀ (_ : ∀ I ∈ B.cells, ∀ (s s' : Fin (4 : ℕ)), s ≠ s' → PairSmall (dyadicGridLeft B.G I.1
      I.2) (dyadicGridLength B.G I.1) (B.w I) s s' (B.Y I s) (B.Y I s') ((2 : ℝ) * η₀))
    (_ : B.η = (4 : ℝ) * η₀)
    (_ : (4 : ℝ) * ((6000 : ℝ) ^ (30 : ℕ) * (L₄ + (2 : ℝ) * (↑k : ℝ) ^ b) ^ (30 : ℕ) + (1 :
      ℝ)) * ((↑Cl : ℝ) * (((2 : ℝ) * (↑Cl : ℝ) + (2 : ℝ)) * (↑k : ℝ) ^ (cc + (1 : ℕ))) ^
      Cl * (Real.exp ((2 : ℝ) * α * (↑k : ℝ) ^ θ₀) + (1 : ℝ)) ^ Cl * Real.exp (((1 : ℝ)
      + Real.log ((2 : ℝ) * (↑k : ℝ))) ^ (2 : ℕ)) ^ Cl * ((Real.exp ((2 : ℝ) * α * (↑k :
      ℝ) ^ θ₀) + (2 : ℝ)) ^ (2 : ℕ) * Real.exp (-(↑k : ℝ) ^ c₃) + Real.exp ((↑Cl : ℝ) *
      (↑k : ℝ) ^ cc) * (Real.exp (-(((2 : ℝ) * (↑Cl : ℝ) + (2 : ℝ)) * (↑k : ℝ) ^ (cc +
      (1 : ℕ))) / (2 : ℝ)) + Real.exp (-(((2 : ℝ) * (↑Cl : ℝ) + (2 : ℝ)) * (↑k : ℝ) ^
      (cc + (1 : ℕ)))))) + (↑Cl : ℝ) * Real.exp (-(↑k : ℝ))) + (Real.exp (Ca * (↑k : ℝ)
      ^ m) + (1 : ℝ)) * ((4 : ℝ) * ((6000 : ℝ) ^ (30 : ℕ) * (L₄ + (2 : ℝ) * (↑k : ℝ) ^
      b) ^ (30 : ℕ) + (1 : ℝ)) * ((9 : ℝ) * (Real.exp (L₄ + (2 : ℝ) * (↑k : ℝ) ^ b + (3
      : ℝ)) + (1 : ℝ)) * Real.exp (-(↑k : ℝ) ^ c₃) * (16 : ℝ))) ≤ η₀ ^ min ((1 / 1200 :
      ℝ) / (2 : ℝ)) (α / (4 : ℝ)))
    (_ : η₀ = Real.exp ((-2 : ℝ) * (↑k : ℝ) ^ θ₀))
    (_ : (0 : ℝ) < η₀),
  let δa : ℝ :=
    Real.exp (-(↑k : ℝ) ^ (Cb + (2 : ℕ)))
  ∀ (_ : ∀ (y : ℝ), (↑(Finset.card ({I ∈ B.cells | y ∈ dyadicGridCell B.G I.1 I.2 ∧ B.active
      δa I})) : ℝ) ≤ Real.exp (Ca * (↑k : ℝ) ^ m))
    (_ : (0 : ℝ) < dyadicGridLength B.G B.R.1)
    (_ : ¬Fintype.card B.L = (0 : ℕ)),
  let A : ActiveSetup κ c' :=
    B.padDc Mpad hMpad0
  ∀ (bf : A.BasicFamilies)
    (_ : A.SubRootProps η₀ ((↑k : ℝ) ^ Cb))
    (_ : B.cells.Nonempty)
    (_ : Nonempty bf.Vtx),
  ∃ (X : Finset (ℤ × ℤ)), (∀ c ∈ X, dyadicGridCell B.G c.1 c.2 ⊆ dyadicGridCell B.G
    B.R.1 B.R.2) ∧ (∀ c ∈ X, ∀ c'_1 ∈ X, c ≠ c'_1 → Disjoint (dyadicGridCell B.G c.1
    c.2) (dyadicGridCell B.G c'_1.1 c'_1.2)) ∧ ∑ c ∈ X, dyadicGridLength B.G c.1 ≤ (1
    / 4 : ℝ) * dyadicGridLength B.G B.R.1 ∧ ∑ I ∈ {I ∈ B.cells | ¬∃ c ∈ X,
    dyadicGridCell B.G I.1 I.2 ⊆ dyadicGridCell B.G c.1 c.2} with (B.active δa) I,
    dyadicGridLength B.G I.1 * min B.η ‖B.Hf I (B.z p.castSucc I)‖ ≤ Cfin * η₀ ^ cs *
    ((1 : ℝ) + finiteDepthConstant κ q N) * dyadicGridLength B.G B.R.1


private theorem retainedMin_holds_nHedτ₂
    (κ : LocalKernelClass)
    (c' : ℕ)
    (Cb : ℕ)
    (Ca : ℝ)
    (b : ℕ)
    (definition_b : b = Cb + 1)
    (m : ℕ)
    (definition_m : m = 3 * Cb + 2)
    (c₃ : ℕ)
    (definition_c₃ : c₃ = 3 * Cb + 3)
    (C : ℕ)
    (cc : ℕ)
    (Mpad : ℝ)
    (L₄ : ℝ)
    (definition_L₄ : L₄ = Real.log (4 + Mpad))
    (lW : ℝ)
    (definition_lW : lW = Real.log ActiveSetup.padW)
    (cH : ℝ)
    (definition_cH : cH = Real.log (↑tagKρ ^ (2 * tagKρ) + 20))
    (k : ℕ)
    (hk3 : 3 ≤ k)
    (A : ActiveSetup κ c')
    (bf : A.BasicFamilies)
    (Y : ℝ)
    (definition_Y : Y = L₄ + 2 * (k : ℝ) ^ b)
    (hcbY : A.colBudget ≤ Real.exp Y)
    (hHsB : Real.log A.Hsrc ≤ Real.log (↑tagKρ ^ (2 * tagKρ) + 20) + 2 * (Real.log
      ActiveSetup.padW + Y))
    (hcb2 : 2 ≤ A.colBudget)
    (Mp : ℕ)
    (definition_Mp : Mp = ⌈Real.exp (Ca * (k : ℝ) ^ (3 * Cb + 2))⌉₊)
    (τ₃ : ℝ)
    (hτ₃def : τ₃ = Real.exp (-(k : ℝ) ^ c₃))
    (hτ0 : 0 < τ₃)
    (hMpup : ↑Mp ≤ Real.exp (Ca * (k : ℝ) ^ m) + 1)
    (fp : bf.FamParams)
    (n : ℕ → ℝ)
    (hnpos : ∀ (r : ℕ), 0 ≤ n r)
    (hn4 : ∀ (r : ℕ), 4 ≤ n r)
    (hnle : ∀ r ≤ fp.Lc + 5, n r ≤ Real.exp ((k : ℝ) ^ C))
    (hsqle : ∀ (x : ℝ), 1 ≤ x → √x ≤ x)
    (T : ℝ)
    (hTdef : T = Y + (k : ℝ) ^ C + Ca * (k : ℝ) ^ m + 2)
    (hkC0 : 0 ≤ (k : ℝ) ^ C)
    (hkm0 : 0 ≤ Ca * (k : ℝ) ^ m)
    (hY0 : 0 ≤ Y)
    (hexpd : ∀ (x y : ℝ), Real.exp x * Real.exp y = Real.exp (x + y))
    (hHs2 : 2 ≤ Real.log A.Hsrc)
    (hbase : ∀ (w : ℝ),
      0 ≤ w →
        w ≤ 1 + (cH + 2 * (lW + Y)) + Real.log 6 + 3 * (Y + (k : ℝ) ^ C + Ca * (k : ℝ) ^ m + 2)
          + (k : ℝ) ^ c₃ + 2 * (Y + 3) →
          ↑A.Dg * w ^ A.Dg ≤ (k : ℝ) ^ cc)
    : Real.exp
        (↑A.Dg *
          (1 + Real.log A.Hsrc +
              Real.log
                (τ₃ /
                    (1 +
                      A.colBudget * √(n (fp.Lc + 4)) * (A.colBudget * √(2 * A.colBudget + (1 +
                        ↑Mp) * n (fp.Lc + 5)))))⁻¹) ^
            A.Dg) ≤
      Real.exp ((k : ℝ) ^ cc) := by
  classical
  rcases definition_b with rfl
  let b := Cb + 1
  rcases definition_m with rfl
  let m := 3 * Cb + 2
  rcases definition_c₃ with rfl
  let c₃ := 3 * Cb + 3
  rcases definition_L₄ with rfl
  let L₄ := Real.log (4 + Mpad)
  rcases definition_lW with rfl
  let lW := Real.log ActiveSetup.padW
  rcases definition_cH with rfl
  let cH := Real.log (↑tagKρ ^ (2 * tagKρ) + 20)
  rcases definition_Y with rfl
  let Y := L₄ + 2 * (k : ℝ) ^ b
  rcases definition_Mp with rfl
  let Mp := ⌈Real.exp (Ca * (k : ℝ) ^ (3 * Cb + 2))⌉₊
  change A.colBudget ≤ Real.exp Y at hcbY
  change Real.log A.Hsrc ≤ Real.log (↑tagKρ ^ (2 * tagKρ) + 20) + 2 * (Real.log ActiveSetup.padW
    + Y) at hHsB
  change τ₃ = Real.exp (-(k : ℝ) ^ c₃) at hτ₃def
  change ↑Mp ≤ Real.exp (Ca * (k : ℝ) ^ m) + 1 at hMpup
  change T = Y + (k : ℝ) ^ C + Ca * (k : ℝ) ^ m + 2 at hTdef
  change 0 ≤ Ca * (k : ℝ) ^ m at hkm0
  change 0 ≤ Y at hY0
  change ∀ (w : ℝ),
      0 ≤ w →
        w ≤ 1 + (cH + 2 * (lW + Y)) + Real.log 6 + 3 * (Y + (k : ℝ) ^ C + Ca * (k : ℝ) ^ m + 2)
          + (k : ℝ) ^ c₃ + 2 * (Y + 3) →
          ↑A.Dg * w ^ A.Dg ≤ (k : ℝ) ^ cc at hbase
  change Real.exp
        (↑A.Dg *
          (1 + Real.log A.Hsrc +
              Real.log
                (τ₃ /
                    (1 +
                      A.colBudget * √(n (fp.Lc + 4)) * (A.colBudget * √(2 * A.colBudget + (1 +
                        ↑Mp) * n (fp.Lc + 5)))))⁻¹) ^
            A.Dg) ≤
      Real.exp ((k : ℝ) ^ cc)
  apply Real.exp_le_exp.mpr
  set! Z := 2 * A.colBudget + (1 + Mp) * n (fp.Lc + 5) with hZ
  rewrite [← hZ] at ⊢
  have! hcb0 : 0 ≤ A.colBudget := by linarith only [hcb2]
  have! hMp0 : (0 : ℝ) ≤ Mp := Nat.cast_nonneg _
  have! hn5' := hnle (fp.Lc + 5) le_rfl
  have! hZ1 : 1 ≤ Z := by
    have! this := mul_nonneg (by linarith only [hMp0] : (0 : ℝ) ≤ 1 + Mp) (hnpos (fp.Lc + 5))
    rw [hZ]; linarith only [this, hcb2]
  have! hZb : Z ≤ 5 * Real.exp (Y + Ca * (k : ℝ) ^ m + (k : ℝ) ^ C) := by
    have! h1 : 2 * A.colBudget ≤ 2 * Real.exp (Y + Ca * (k : ℝ) ^ m + (k : ℝ) ^ C) := by
      have! this := Real.exp_le_exp.mpr (show Y ≤ Y + Ca * (k : ℝ) ^ m + (k : ℝ) ^ C by
        linarith only [hkC0, hkm0])
      linarith only [hcbY, this]
    have! h2 : (1 + (Mp : ℝ)) * n (fp.Lc + 5) ≤
        (2 + Real.exp (Ca * (k : ℝ) ^ m)) * Real.exp ((k : ℝ) ^ C) :=
      mul_le_mul (by linarith only [hMpup]) hn5' (hnpos _) (by positivity)
    have! h3 : (2 + Real.exp (Ca * (k : ℝ) ^ m)) * Real.exp ((k : ℝ) ^ C) ≤
        3 * Real.exp (Y + Ca * (k : ℝ) ^ m + (k : ℝ) ^ C) := by
      have! e1 : Real.exp (Ca * (k : ℝ) ^ m) * Real.exp ((k : ℝ) ^ C) =
          Real.exp (Ca * (k : ℝ) ^ m + (k : ℝ) ^ C) := hexpd _ _
      have! h4 : Real.exp (Ca * (k : ℝ) ^ m + (k : ℝ) ^ C) ≤
          Real.exp (Y + Ca * (k : ℝ) ^ m + (k : ℝ) ^ C) :=
        Real.exp_le_exp.mpr (by linarith only [hY0])
      have! h5 : Real.exp ((k : ℝ) ^ C) ≤ Real.exp (Y + Ca * (k : ℝ) ^ m + (k : ℝ) ^ C) :=
        Real.exp_le_exp.mpr (by linarith only [hY0, hkm0])
      nlinarith only [e1, h4, h5]
    rw [hZ]; linarith only [h1, h2, h3]
  have! hsq4 : Real.sqrt (n (fp.Lc + 4)) ≤ Real.exp ((k : ℝ) ^ C) :=
    (hsqle _ (by linarith only [hn4 (fp.Lc + 4)])).trans (hnle _ (by omega))
  have! hsqZ := hsqle Z hZ1
  have! hy1 : A.colBudget * Real.sqrt (n (fp.Lc + 4)) * (A.colBudget * Real.sqrt Z) ≤
      Real.exp Y * Real.exp ((k : ℝ) ^ C) *
        (Real.exp Y * (5 * Real.exp (Y + Ca * (k : ℝ) ^ m + (k : ℝ) ^ C))) := by
    gcongr
    exact hsqZ.trans hZb
  have! hy2 : Real.exp Y * Real.exp ((k : ℝ) ^ C) *
      (Real.exp Y * (5 * Real.exp (Y + Ca * (k : ℝ) ^ m + (k : ℝ) ^ C))) =
      5 * Real.exp (3 * Y + 2 * (k : ℝ) ^ C + Ca * (k : ℝ) ^ m) := by
    have! e : Real.exp (3 * Y + 2 * (k : ℝ) ^ C + Ca * (k : ℝ) ^ m) =
        Real.exp Y * Real.exp ((k : ℝ) ^ C) *
          (Real.exp Y * Real.exp (Y + Ca * (k : ℝ) ^ m + (k : ℝ) ^ C)) := by
      rw [hexpd, hexpd, hexpd]; congr 1; ring
    rw [e]; ring
  have! hy3 : 1 + A.colBudget * Real.sqrt (n (fp.Lc + 4)) * (A.colBudget * Real.sqrt Z) ≤
      6 * Real.exp (3 * T) := by
    have! h1 := Real.one_le_exp (show 0 ≤ 3 * Y + 2 * (k : ℝ) ^ C + Ca * (k : ℝ) ^ m by
      linarith only [hY0, hkC0, hkm0])
    have! h2 : Real.exp (3 * Y + 2 * (k : ℝ) ^ C + Ca * (k : ℝ) ^ m) ≤ Real.exp (3 * T) :=
      Real.exp_le_exp.mpr (by rw [hTdef]; linarith only [hkC0, hkm0])
    linarith only [hy1, hy2, h1, h2]
  have! hyp : 0 < 1 + A.colBudget * Real.sqrt (n (fp.Lc + 4)) * (A.colBudget * Real.sqrt Z) := by
    positivity
  have! hlogy : Real.log (1 + A.colBudget * Real.sqrt (n (fp.Lc + 4)) *
      (A.colBudget * Real.sqrt Z)) ≤ Real.log 6 + 3 * T := by
    have! this := Real.log_le_log hyp hy3
    rwa [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp] at this
  have! hlogy0 : 0 ≤ Real.log (1 + A.colBudget * Real.sqrt (n (fp.Lc + 4)) *
      (A.colBudget * Real.sqrt Z)) := Real.log_nonneg (by
    have! this : 0 ≤ A.colBudget * Real.sqrt (n (fp.Lc + 4)) * (A.colBudget * Real.sqrt Z) := by
      positivity
    linarith only [this])
  have! hlτ : Real.log ((τ₃ / (1 + A.colBudget * Real.sqrt (n (fp.Lc + 4)) *
      (A.colBudget * Real.sqrt Z)))⁻¹) = Real.log (1 + A.colBudget *
        Real.sqrt (n (fp.Lc + 4)) * (A.colBudget * Real.sqrt Z)) + (k : ℝ) ^ c₃ := by
    rw [inv_div, Real.log_div hyp.ne' hτ0.ne', hτ₃def, Real.log_exp]; ring
  rw [hlτ]
  have! hkc₃ : (0 : ℝ) ≤ (k : ℝ) ^ c₃ := by positivity
  refine hbase _ (by linarith only [hHs2, hlogy0, hkc₃]) ?_
  rw [hTdef] at hlogy
  linarith only [hHsB, hlogy, hY0]

private theorem retainedMin_holds_nHedτ_
    (κ : LocalKernelClass)
    (c' : ℕ)
    (Cb : ℕ)
    (Ca : ℝ)
    (b : ℕ)
    (definition_b : b = Cb + 1)
    (m : ℕ)
    (definition_m : m = 3 * Cb + 2)
    (c₃ : ℕ)
    (definition_c₃ : c₃ = 3 * Cb + 3)
    (C : ℕ)
    (cc : ℕ)
    (Mpad : ℝ)
    (L₄ : ℝ)
    (definition_L₄ : L₄ = Real.log (4 + Mpad))
    (lW : ℝ)
    (definition_lW : lW = Real.log ActiveSetup.padW)
    (cH : ℝ)
    (definition_cH : cH = Real.log (↑tagKρ ^ (2 * tagKρ) + 20))
    (k : ℕ)
    (hk3 : 3 ≤ k)
    (A : ActiveSetup κ c')
    (bf : A.BasicFamilies)
    (Y : ℝ)
    (definition_Y : Y = L₄ + 2 * (k : ℝ) ^ b)
    (hcbY : A.colBudget ≤ Real.exp Y)
    (hHsB : Real.log A.Hsrc ≤ Real.log (↑tagKρ ^ (2 * tagKρ) + 20) + 2 * (Real.log
      ActiveSetup.padW + Y))
    (hcb2 : 2 ≤ A.colBudget)
    (fp : bf.FamParams)
    (n : ℕ → ℝ)
    (hnpos : ∀ (r : ℕ), 0 ≤ n r)
    (hnle : ∀ r ≤ fp.Lc + 5, n r ≤ Real.exp ((k : ℝ) ^ C))
    (hkC0 : 0 ≤ (k : ℝ) ^ C)
    (hkm0 : 0 ≤ Ca * (k : ℝ) ^ m)
    (hY0 : 0 ≤ Y)
    (hexpd : ∀ (x y : ℝ), Real.exp x * Real.exp y = Real.exp (x + y))
    (hHs2 : 2 ≤ Real.log A.Hsrc)
    (hbase : ∀ (w : ℝ),
      0 ≤ w →
        w ≤ 1 + (cH + 2 * (lW + Y)) + Real.log 6 + 3 * (Y + (k : ℝ) ^ C + Ca * (k : ℝ) ^ m + 2)
          + (k : ℝ) ^ c₃ + 2 * (Y + 3) →
          ↑A.Dg * w ^ A.Dg ≤ (k : ℝ) ^ cc)
    : Real.exp (↑A.Dg * (1 + Real.log A.Hsrc + Real.log (1 + ↑⌈8 * A.colBudget + n (fp.Lc + 5)⌉₊
      * A.colBudget ^ 2)) ^ A.Dg) ≤
      Real.exp ((k : ℝ) ^ cc) := by
  classical
  rcases definition_b with rfl
  let b := Cb + 1
  rcases definition_m with rfl
  let m := 3 * Cb + 2
  rcases definition_c₃ with rfl
  let c₃ := 3 * Cb + 3
  rcases definition_L₄ with rfl
  let L₄ := Real.log (4 + Mpad)
  rcases definition_lW with rfl
  let lW := Real.log ActiveSetup.padW
  rcases definition_cH with rfl
  let cH := Real.log (↑tagKρ ^ (2 * tagKρ) + 20)
  rcases definition_Y with rfl
  let Y := L₄ + 2 * (k : ℝ) ^ b
  change A.colBudget ≤ Real.exp Y at hcbY
  change Real.log A.Hsrc ≤ Real.log (↑tagKρ ^ (2 * tagKρ) + 20) + 2 * (Real.log ActiveSetup.padW
    + Y) at hHsB
  change 0 ≤ Ca * (k : ℝ) ^ m at hkm0
  change 0 ≤ Y at hY0
  change ∀ (w : ℝ),
      0 ≤ w →
        w ≤ 1 + (cH + 2 * (lW + Y)) + Real.log 6 + 3 * (Y + (k : ℝ) ^ C + Ca * (k : ℝ) ^ m + 2)
          + (k : ℝ) ^ c₃ + 2 * (Y + 3) →
          ↑A.Dg * w ^ A.Dg ≤ (k : ℝ) ^ cc at hbase
  apply Real.exp_le_exp.mpr
  have! hcb0 : 0 ≤ A.colBudget := by linarith only [hcb2]
  have! hn5' := hnle (fp.Lc + 5) le_rfl
  have! hc0 : 0 ≤ 8 * A.colBudget + n (fp.Lc + 5) := by
    linarith only [hcb0, hnpos (fp.Lc + 5)]
  have! h1 : (⌈8 * A.colBudget + n (fp.Lc + 5)⌉₊ : ℝ) ≤
      10 * Real.exp (Y + (k : ℝ) ^ C) := by
    have! h2 := (Nat.ceil_lt_add_one hc0).le
    have! h3 : Real.exp Y ≤ Real.exp (Y + (k : ℝ) ^ C) :=
      Real.exp_le_exp.mpr (by linarith only [hkC0])
    have! h4 : Real.exp ((k : ℝ) ^ C) ≤ Real.exp (Y + (k : ℝ) ^ C) :=
      Real.exp_le_exp.mpr (by linarith only [hY0])
    have! h5 := Real.one_le_exp (show 0 ≤ Y + (k : ℝ) ^ C by linarith only [hY0, hkC0])
    linarith only [h2, hcbY, hn5', h3, h4, h5]
  have! h6 : A.colBudget ^ 2 ≤ Real.exp (2 * Y) := by
    rw [show 2 * Y = Y + Y by ring, ← hexpd, sq]
    exact mul_le_mul hcbY hcbY hcb0 (Real.exp_pos _).le
  have! h7 : 1 + (⌈8 * A.colBudget + n (fp.Lc + 5)⌉₊ : ℝ) * A.colBudget ^ 2 ≤
      11 * Real.exp (3 * Y + (k : ℝ) ^ C) := by
    have! h8 := mul_le_mul h1 h6 (by positivity) (by positivity)
    have! e : 10 * Real.exp (Y + (k : ℝ) ^ C) * Real.exp (2 * Y) =
        10 * Real.exp (3 * Y + (k : ℝ) ^ C) := by
      rw [mul_assoc, hexpd]; ring_nf
    have! h9 := Real.one_le_exp (show 0 ≤ 3 * Y + (k : ℝ) ^ C by linarith only [hY0, hkC0])
    linarith only [h8, e, h9]
  have! hpos : 0 < 1 + (⌈8 * A.colBudget + n (fp.Lc + 5)⌉₊ : ℝ) * A.colBudget ^ 2 := by
    positivity
  have! hlog : Real.log (1 + (⌈8 * A.colBudget + n (fp.Lc + 5)⌉₊ : ℝ) * A.colBudget ^ 2) ≤
      Real.log 11 + (3 * Y + (k : ℝ) ^ C) := by
    have! this := Real.log_le_log hpos h7
    rwa [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp] at this
  have! hlog0 : 0 ≤ Real.log (1 + (⌈8 * A.colBudget + n (fp.Lc + 5)⌉₊ : ℝ) *
      A.colBudget ^ 2) := Real.log_nonneg (by
    have! this : 0 ≤ (⌈8 * A.colBudget + n (fp.Lc + 5)⌉₊ : ℝ) * A.colBudget ^ 2 := by positivity
    linarith only [this])
  have! hl11 : Real.log 11 ≤ Real.log 6 + 6 := by
    have! h1 : Real.log 11 ≤ Real.log (6 * Real.exp 6) := Real.log_le_log (by norm_num) (by
      have! this := Real.add_one_le_exp (6 : ℝ); linarith only [this])
    rwa [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp] at h1
  have! hkc₃ : (0 : ℝ) ≤ (k : ℝ) ^ c₃ := by positivity
  refine hbase _ (by linarith only [hHs2, hlog0]) ?_
  linarith only [hHsB, hlog, hl11, hY0, hkC0, hkm0, hkc₃]

private theorem retainedMin_holds_hcbY
    (κ : LocalKernelClass)
    (c' : ℕ)
    (Cb : ℕ)
    (b : ℕ)
    (definition_b : b = Cb + 1)
    (Mpad : ℝ)
    (hMpad : Mpad = 800 * 2001 ^ 7)
    (L₄ : ℝ)
    (definition_L₄ : L₄ = Real.log (4 + Mpad))
    (hL₄ : L₄ = Real.log (4 + Mpad))
    (hMpad0 : 0 ≤ Mpad)
    (k : ℕ)
    (B : ActiveSetup κ c')
    (hk3 : 3 ≤ k)
    (hDck : B.Dc ≤ Real.exp ((k : ℝ) ^ Cb))
    (hLk : ↑(Fintype.card B.L) ≤ Real.exp ((k : ℝ) ^ Cb))
    (A : ActiveSetup κ c')
    (definition_A : A = B.padDc Mpad hMpad0)
    (hkCb : (k : ℝ) ^ Cb ≤ (k : ℝ) ^ b)
    (Y : ℝ)
    (hYdef : Y = L₄ + 2 * (k : ℝ) ^ b)
    : A.colBudget ≤ Real.exp Y := by
  classical
  rcases definition_b with rfl
  let b := Cb + 1
  rcases definition_L₄ with rfl
  let L₄ := Real.log (4 + Mpad)
  rcases definition_A with rfl
  let A := B.padDc Mpad hMpad0
  change L₄ = Real.log (4 + Mpad) at hL₄
  change (k : ℝ) ^ Cb ≤ (k : ℝ) ^ b at hkCb
  change Y = L₄ + 2 * (k : ℝ) ^ b at hYdef
  change A.colBudget ≤ Real.exp Y
  have! h1 := B.colBudget_padDc_le hMpad0
  have! hE1 : 1 ≤ Real.exp ((k : ℝ) ^ Cb) := Real.one_le_exp (by positivity)
  have! hL0' : (0 : ℝ) ≤ Fintype.card B.L := Nat.cast_nonneg _
  have hDc0 := B.Dc_nonneg
  have! h21 : (Fintype.card B.L : ℝ) * (1 + B.Dc + Mpad) ≤
      Real.exp ((k : ℝ) ^ Cb) * (1 + Real.exp ((k : ℝ) ^ Cb) + Mpad) :=
    mul_le_mul hLk (by linarith only [hDck]) (by positivity) (Real.exp_pos _).le
  have! hEE : Real.exp ((k : ℝ) ^ Cb) ≤ Real.exp ((k : ℝ) ^ Cb) * Real.exp ((k : ℝ) ^ Cb) :=
    le_mul_of_one_le_left (Real.exp_pos _).le hE1
  have! hME := mul_le_mul_of_nonneg_left hEE hMpad0
  have! h22 : Real.exp ((k : ℝ) ^ Cb) * (1 + Real.exp ((k : ℝ) ^ Cb) + Mpad) ≤
      (2 + Mpad) * (Real.exp ((k : ℝ) ^ Cb) * Real.exp ((k : ℝ) ^ Cb)) := by
    linarith only [hEE, hME]
  have! h23 : (2 : ℝ) ≤ 2 * (Real.exp ((k : ℝ) ^ Cb) * Real.exp ((k : ℝ) ^ Cb)) := by
    linarith only [hEE, hE1]
  have! h3 : (4 + Mpad) * (Real.exp ((k : ℝ) ^ Cb) * Real.exp ((k : ℝ) ^ Cb)) =
      Real.exp (L₄ + 2 * (k : ℝ) ^ Cb) := by
    rw [show L₄ + 2 * (k : ℝ) ^ Cb = L₄ + (k : ℝ) ^ Cb + (k : ℝ) ^ Cb by ring, Real.exp_add,
      Real.exp_add, hL₄, Real.exp_log (by linarith only [hMpad0])]
    ring
  have! h4 : Real.exp (L₄ + 2 * (k : ℝ) ^ Cb) ≤ Real.exp Y :=
    Real.exp_le_exp.mpr (by rw [hYdef]; linarith only [hkCb])
  have h1' : A.colBudget ≤ 2 + Fintype.card B.L * (1 + B.Dc + Mpad) := h1
  linarith only [h1', h21, h22, h23, h3, h4]




private theorem retainedMin_holds_nh3 : RetainedMinHoldsNh3Statement := by
  classical
  intro κ c' Cb θ₀ b Cl hCl1 α Mpad L₄ hMpad0 hL₄0 k B p hk3 η₀ A bf Y x5 P hPlo hPup hP1 fp hexpd
    Nl hNlF'
  have! hlP0 : 0 ≤ Real.log P := Real.log_nonneg hP1
  have! hlP : Real.log P ≤ 2 * α * (k : ℝ) ^ θ₀ + 1 := by
    have! hPL1 : (1 : ℝ) ≤ Real.exp (2 * α * (k : ℝ) ^ θ₀) := Real.one_le_exp (by positivity)
    have! h1 : (P : ℝ) ≤ Real.exp (2 * α * (k : ℝ) ^ θ₀ + 1) := by
      rw [← hexpd]
      have! he : (2 : ℝ) ≤ Real.exp 1 := by
        have! this := Real.add_one_le_exp (1 : ℝ); linarith only [this]
      nlinarith only [hPup, he, hPL1]
    have! this := Real.log_le_log (by linarith only [hP1]) h1
    rwa [Real.log_exp] at this
  have! h6 : (2 + ((Cl : ℝ) + 1) * Real.log P) ^ 6 ≤
      (2 + ((Cl : ℝ) + 1) * (2 * α * (k : ℝ) ^ θ₀ + 1)) ^ 6 := by
    gcongr
  have! hP8 : Real.exp (α * (k : ℝ) ^ θ₀ / 4) ≤ (P : ℝ) ^ (1 / 8 : ℝ) := by
    have! e :
        Real.exp (α * (k : ℝ) ^ θ₀ / 4) = Real.exp (2 * α * (k : ℝ) ^ θ₀) ^ (1 / 8 : ℝ) := by
      rw [← Real.exp_mul]; ring_nf
    rw [e]
    exact Real.rpow_le_rpow (Real.exp_pos _).le hPlo (by norm_num)
  calc (Nl : ℝ) * Cl * (2 + ((Cl : ℝ) + 1) * Real.log P) ^ 6 *
        Real.exp ((1 + Real.log (2 * (k : ℝ))) ^ 2) ^ Cl
      ≤ 4 * (6000 ^ 30 * Y ^ 30 + 1) * Cl *
          (2 + ((Cl : ℝ) + 1) * (2 * α * (k : ℝ) ^ θ₀ + 1)) ^ 6 *
          Real.exp ((1 + Real.log (2 * (k : ℝ))) ^ 2) ^ Cl := by gcongr
    _ ≤ _ := x5
    _ ≤ _ := hP8



private theorem retainedMin_holds_nB6 : RetainedMinHoldsNB6Statement := by
  classical
  intro κ c' Cb hc' Dst hst Ca b m c₃ c C Dg a₀ cc Mpad L₄ hMpad0 k B p δa A bf Y hcbY hcb2 Tc
    hTcA Mp hMp1 hmultTc τ₃ hτ0 hτ1 hMpup fp cat Kt n Tmax hLc hmH hMc hHed hcolr hKh hn0 hgrow
    hcapH hcats hnpos hnle T p10 hkC0 hkm0 hY0 hexpd nHedV nHedτ₂ nHedτ' hHedge AD
  have! hn5' : n (fp.Lc + 5) ≤ Real.exp ((k : ℝ) ^ C) := hnle _ le_rfl
  have! hMp0 : (0 : ℝ) ≤ Mp := Nat.cast_nonneg _
  have! hcb0 : 0 ≤ A.colBudget := by linarith only [hcb2]
  have! hpos : 0 < 2 * (8 * A.colBudget + (1 + (Mp : ℝ)) * n (fp.Lc + 5)) := by
    have! this := mul_nonneg (by linarith only [hMp0] : (0 : ℝ) ≤ 1 + Mp) (hnpos (fp.Lc + 5))
    linarith only [this, hcb2]
  have! h1 : 2 * (8 * A.colBudget + (1 + (Mp : ℝ)) * n (fp.Lc + 5)) ≤
      20 * Real.exp (Y + (k : ℝ) ^ C + Ca * (k : ℝ) ^ m + 2) := by
    have! h2 : (1 + (Mp : ℝ)) * n (fp.Lc + 5) ≤
        (2 + Real.exp (Ca * (k : ℝ) ^ m)) * Real.exp ((k : ℝ) ^ C) :=
      mul_le_mul (by linarith only [hMpup]) hn5' (hnpos _) (by positivity)
    set! W₀ := Real.exp (Y + (k : ℝ) ^ C + Ca * (k : ℝ) ^ m) with hW₀
    have! h3 : Real.exp Y ≤ W₀ := Real.exp_le_exp.mpr (by linarith only [hkC0, hkm0])
    have! h4 : Real.exp ((k : ℝ) ^ C) ≤ W₀ := Real.exp_le_exp.mpr (by linarith only [hY0, hkm0])
    have! h5 : Real.exp (Ca * (k : ℝ) ^ m) * Real.exp ((k : ℝ) ^ C) ≤ W₀ := by
      rw [hexpd]; exact Real.exp_le_exp.mpr (by linarith only [hY0])
    have! h6 : Real.exp (Y + (k : ℝ) ^ C + Ca * (k : ℝ) ^ m + 2) = W₀ * Real.exp 2 := by
      rw [hW₀, hexpd]
    have! h7 : (7.3 : ℝ) ≤ Real.exp 2 := by
      have := Real.exp_one_gt_d9
      have! h8 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      rw [h8]; nlinarith only [this]
    have! hW0 : 0 ≤ W₀ := (Real.exp_pos _).le
    rw [h6]
    nlinarith only [h2, h3, h4, h5, h7, hW0, hcbY, hcb0]
  have! h2 := Real.log_le_log hpos h1
  rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp] at h2
  exact h2.trans p10



private theorem retainedMin_holds_nB12 : RetainedMinHoldsNB12Statement := by
  classical
  intro κ c' Cb θ₀ hc' Dst hst Ca b m c₃ c C k₀ Dg a₀ cc Cl K₀ Mpad L₄ lW cH hMpad0 K k B p hk3 δa
    A bf hk1 Y hV hHsB Tc hTcA Mp hMp1 hmultTc τ₃ hτ₃def hτ0 hτ1 fp cat Kt n Tmax hLc hmH hMc hHed
    hcolr hKh hn0 hgrow hcapH hcats hn4 hnle hkC0 hkm0 hY0 hHs2 hbase hl6 nHedV nHedτ₂ nHedτ'
    hHedge AD
  have! hHedp : 0 < fp.Hed := lt_of_lt_of_le (Real.exp_pos _) hHedge
  change Real.log fp.Hed ≤ (k : ℝ) ^ cc
  rw [Real.log_le_iff_le_exp hHedp, hHed]
  refine max_le le_rfl (max_le ?_ ?_)
  · have! this := Real.add_one_le_exp ((k : ℝ) ^ cc)
    have! h1 : (1 : ℝ) ≤ (k : ℝ) ^ cc := one_le_pow₀ hk1
    linarith only [this, h1]
  · apply Real.exp_le_exp.mpr
    have! hV1 : (1 : ℝ) ≤ A.famVtxBound := by exact_mod_cast A.one_le_famVtxBound
    have! hn1 : n (A.famLc + 1) ≤ Real.exp ((k : ℝ) ^ C) := by
      have! this := hnle (fp.Lc + 1) (by omega); rwa [hLc] at this
    have! hn14 := hn4 (A.famLc + 1)
    have! hy : 0 < (A.famVtxBound : ℝ) ^ 2 * n (A.famLc + 1) := by positivity
    have! hlτ : Real.log ((τ₃ / ((A.famVtxBound : ℝ) ^ 2 * n (A.famLc + 1)))⁻¹) =
        Real.log ((A.famVtxBound : ℝ) ^ 2 * n (A.famLc + 1)) + (k : ℝ) ^ c₃ := by
      rw [inv_div, Real.log_div hy.ne' hτ0.ne', hτ₃def, Real.log_exp]; ring
    have! hlog : Real.log ((A.famVtxBound : ℝ) ^ 2 * n (A.famLc + 1)) ≤
        2 * (Y + 3) + (k : ℝ) ^ C := by
      have! h1 : (A.famVtxBound : ℝ) ^ 2 * n (A.famLc + 1) ≤
          Real.exp (Y + 3) ^ 2 * Real.exp ((k : ℝ) ^ C) :=
        mul_le_mul (pow_le_pow_left₀ (by linarith only [hV1]) hV 2) hn1 (by positivity)
          (by positivity)
      have! h2 := Real.log_le_log hy h1
      rwa [Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_pow, Real.log_exp,
        Real.log_exp] at h2
    have! hlog0 : 0 ≤ Real.log ((A.famVtxBound : ℝ) ^ 2 * n (A.famLc + 1)) :=
      Real.log_nonneg (by nlinarith only [hV1, hn14])
    have! hkc₃ : (0 : ℝ) ≤ (k : ℝ) ^ c₃ := by positivity
    rw [hlτ]
    refine hbase _ (by linarith only [hHs2, hlog0, hkc₃]) ?_
    linarith only [hHsB, hlog, hY0, hkC0, hkm0, hl6]



private theorem retainedMin_holds_nh4 : RetainedMinHoldsNh4Statement := by
  classical
  intro κ c' Cb θ₀ hc' Ca b m c₃ c C Dg a₀ cc Cl hCl1 α Mpad L₄ hMpad0 hL₄0 k B p hk3 hS2 η₀ A bf
    Y hV Mp P τ₃ hτ0 hPup hP1 hMpup fp hexpd kD δ x6 hδdef Nl W hWdef hNlF'
  have! hsqδ : Real.sqrt δ = Real.exp (-kD / 2) := by
    have! e : Real.exp (-kD) = Real.exp (-kD / 2) * Real.exp (-kD / 2) := by
      rw [hexpd]; ring_nf
    rw [hδdef, e, Real.sqrt_mul_self (Real.exp_pos _).le]
  have! hS16 : max 2 A.S ^ 4 = (16 : ℝ) := by
    rw [show A.S = 2 from hS2]; norm_num
  have hτ00 : 0 ≤ τ₃ := hτ0.le
  have! hP0' : (0 : ℝ) ≤ P := by linarith only [hP1]
  have! hMp0 : (0 : ℝ) ≤ Mp := Nat.cast_nonneg _
  have! hNl0 : (0 : ℝ) ≤ Nl := Nat.cast_nonneg _
  have! e1 : (Nl : ℝ) * (Cl * (kD * P) ^ Cl * Real.exp ((1 + Real.log (2 * (k : ℝ))) ^ 2) ^ Cl *
      (((P : ℝ) + 1) ^ 2 * τ₃ + Real.exp (Cl * (k : ℝ) ^ cc) * (Real.sqrt δ + Real.exp (-kD))) +
        Cl * Real.exp (-(k : ℝ))) + Mp * W =
      (Nl : ℝ) * (Cl * kD ^ Cl * (P : ℝ) ^ Cl * Real.exp ((1 + Real.log (2 * (k : ℝ))) ^ 2) ^ Cl *
        (((P : ℝ) + 1) ^ 2 * τ₃ + Real.exp (Cl * (k : ℝ) ^ cc) *
          (Real.exp (-kD / 2) + Real.exp (-kD))) + Cl * Real.exp (-(k : ℝ))) +
      Mp * (Nl * (9 * ((A.famVtxBound : ℝ) + 1) * τ₃ * 16)) := by
    rw [hWdef, hsqδ, hS16, mul_pow]; ring
  rw [e1]
  have hPL : (P : ℝ) ≤ Real.exp (2 * α * (k : ℝ) ^ θ₀) + 1 := hPup
  calc _ ≤ 4 * (6000 ^ 30 * Y ^ 30 + 1) * (Cl * kD ^ Cl *
          (Real.exp (2 * α * (k : ℝ) ^ θ₀) + 1) ^ Cl *
          Real.exp ((1 + Real.log (2 * (k : ℝ))) ^ 2) ^ Cl *
          ((Real.exp (2 * α * (k : ℝ) ^ θ₀) + 1 + 1) ^ 2 * τ₃ +
            Real.exp (Cl * (k : ℝ) ^ cc) * (Real.exp (-kD / 2) + Real.exp (-kD))) +
          Cl * Real.exp (-(k : ℝ))) +
        (Real.exp (Ca * (k : ℝ) ^ m) + 1) * (4 * (6000 ^ 30 * Y ^ 30 + 1) *
          (9 * (Real.exp (Y + 3) + 1) * τ₃ * 16)) := by
        have! hN4 : (0 : ℝ) ≤ 4 * (6000 ^ 30 * Y ^ 30 + 1) := by positivity
        refine add_le_add (mul_le_mul hNlF' (add_le_add (mul_le_mul
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hP0' hPL Cl)
            (by positivity)) (by positivity))
          (add_le_add (mul_le_mul_of_nonneg_right
            (pow_le_pow_left₀ (by positivity) (show (P : ℝ) + 1 ≤
              Real.exp (2 * α * (k : ℝ) ^ θ₀) + 1 + 1 by linarith only [hPL]) 2) hτ00) le_rfl)
          (by positivity) (by positivity)) le_rfl) (by positivity) hN4) ?_
        exact mul_le_mul hMpup (mul_le_mul hNlF' (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith only [hV])
            (by norm_num)) hτ00) (by norm_num)) (by positivity) hN4) (by positivity)
          (by positivity)
    _ = 4 * (6000 ^ 30 * Y ^ 30 + 1) * (Cl * kD ^ Cl *
          (Real.exp (2 * α * (k : ℝ) ^ θ₀) + 1) ^ Cl *
          Real.exp ((1 + Real.log (2 * (k : ℝ))) ^ 2) ^ Cl *
          ((Real.exp (2 * α * (k : ℝ) ^ θ₀) + 2) ^ 2 * τ₃ +
            Real.exp (Cl * (k : ℝ) ^ cc) * (Real.exp (-kD / 2) + Real.exp (-kD))) +
          Cl * Real.exp (-(k : ℝ))) +
        (Real.exp (Ca * (k : ℝ) ^ m) + 1) * (4 * (6000 ^ 30 * Y ^ 30 + 1) *
          (9 * (Real.exp (Y + 3) + 1) * τ₃ * 16)) := by
        rw [add_assoc (Real.exp (2 * α * (k : ℝ) ^ θ₀)) 1 1, one_add_one_eq_two]
    _ ≤ _ := x6



private theorem retainedMin_holds_stage_4 : RetainedMinHoldsStage4Statement := by
  classical
  intro κ c' Cb θ₀ hc' Dst hst Ca b m hmult c₃ c C k₀ Dg a₀ cc hccdef Cl K₀ hCl1 hleaf q hq2 hq3
    hq α cs hcs Cq hCq0 Cfin Mpad hMpad L₄ lW cH hMpad0 hL₄0 K k N d₀ B hwin p hk3 hK₀k hanc hS2
    hcol η₀ hpairs hη hη₀0 δa hR0 hL0 A bf hsubA hne d hk1 Y p13 p14 p15 x5 hV hmaxB hHsB Tc hTc
    hTcA Mp hMp1 hMpA hmultTc P τ₃ hτ0 hτ1 hPlo hPup hP1 hMpup fp cat Kt n Tmax hfpP hLc hmH hMc
    hHed hcolr hKh hn0 hgrow hcapH hcats hloc hexpd nHedV nHedτ₂ nHedτ' hHedge AD kD x3 x4 δ x6
    hδdef ρ hρdef hkcc0 hkDk nδ8 ndδ nδN nρ0 h2F nρ1 nkD nB6 nB7 nB8 nB9 nB10 nB11 nB12
  have! nB13 : Real.log A.Hsrc ≤ (k : ℝ) ^ cc := hHsB.trans p14
  have! nB14 : Real.log (max A.H ActiveSetup.padW) ≤ (k : ℝ) ^ cc := by
    linarith only [hmaxB, p13]
  have! nδk : δ⁻¹ ≤ Real.exp kD := by rw [hδdef, Real.exp_neg, inv_inv]
  have! nE : (k : ℝ) ^ Cb ≤ (k : ℝ) ^ cc := by
    refine pow_le_pow_right₀ hk1 ?_
    rw [hccdef]; nlinarith only [show Cb < a₀ by omega, Nat.zero_le Dg]
  have! nρk : ρ⁻¹ ≤ (k : ℝ) ^ cc := by
    rw [hρdef, one_div, inv_inv]
    linarith only [h2F, p15]
  have! hLE := fun s => hleaf bf k hanc hpairs hsubA hS2 hη hη₀0 hne hq2 hq3 ⟨d₀, hwin⟩ p AD d s
    (Real.exp_pos _) nδ8 ndδ nδN nρ0 nρ1 hK₀k nkD nB6 nB7 nB8 nB9 nB10 nB11 nB12 nB13 nB14 nδk
    nE nρk
  choose Fl hFlsub hFllen hFlb using hLE
  -- the failure roots, the leaf count and the union of the cuts
  obtain ⟨hFRsub, -, hFRlen, -⟩ := fp.failure_cut hcolr
  have! hFR :
      ∑ c ∈ fp.failRoots, dyadicGridLength A.G c.1 ≤ 1 / 8 * dyadicGridLength A.G A.R.1 := by
    have! hcardL : 1 ≤ Fintype.card B.L := Nat.one_le_iff_ne_zero.mpr hL0
    have! h1 := B.le_colBudget_padDc hMpad0 hcardL
    have! h2 : 8 * A.colBudget < (A.famVtxBound : ℝ) := by
      unfold ActiveSetup.famVtxBound; push_cast; exact Nat.lt_floor_add_one _
    have! h3 : (100 * 2001 ^ 7 : ℝ) / A.famVtxBound ≤ 1 / 8 := by
      rw [div_le_iff₀ (by linarith only [h1, h2, hMpad0])]
      have h4 : A.colBudget = (B.padDc Mpad hMpad0).colBudget := rfl
      linarith only [h1, h2, h4, hMpad]
    exact hFRlen.trans (mul_le_mul_of_nonneg_right h3 hR0.le)
  set! Nl := (searchList A.famFuel fp.Lc (A.basicSlot p)).length with hNl
  rewrite [← hNl] at hloc
  have! hNlF : (Nl : ℝ) ≤ 2 ^ A.famFuel := by
    have! this := searchLeaves_length_le A.famFuel 1 fp.Lc (A.basicSlot p) none (fun _ => [])
    exact_mod_cast this
  have! hNlρ : (Nl : ℝ) * (6 * (2 * ρ)) ≤ 1 / 8 := by
    rw [hρdef]
    have! h2 : (0 : ℝ) < 2 ^ A.famFuel := by positivity
    rw [show (Nl : ℝ) * (6 * (2 * (1 / (96 * 2 ^ A.famFuel)))) = Nl / (8 * 2 ^ A.famFuel) by
      field_simp; ring]
    rw [div_le_iff₀ (by positivity)]
    linarith only [hNlF]
  set! W : ℝ := Nl * (9 * ((A.famVtxBound : ℝ) + 1) * τ₃ * max 2 A.S ^ 4) with hWdef
  rewrite [← hWdef] at hloc
  have! hW0 : 0 ≤ W := by rw [hWdef]; positivity
  have hηA : A.η = 4 * η₀ := hη
  have! hη0' : 0 ≤ A.η := by rw [hηA]; positivity
  obtain ⟨X, hXR, hXd, hXl, hXsum⟩ := ActiveSetup.root_assembly A p (δa := δa) Tc fp.failRoots rfl
    Nl Fl (fun s I => min A.η ‖∑ G ∈ fp.groupsAt I
      (leafAt A.famFuel fp.Lc (A.basicSlot p) s).k,
        fp.Λc I (fun l => fp.ballFilt l (cat l) I G
          ((leafAt A.famFuel fp.Lc (A.basicSlot p) s).role l)
          (fp.inputL cat I (bf.patIn fp.Mc p I)
            (leafAt A.famFuel fp.Lc (A.basicSlot p) s).layers l))‖)
    (ρ := ρ) (Bnd := leafBnd Cl kD fp.P k cc A.η η₀ τ₃ δ (finiteDepthConstant κ q N) Cq q
      (dyadicGridLength A.G A.R.1)) (Mp := Mp) (W := W)
    hFRsub hFR (fun s _ => hFlsub s) (fun s _ => hFllen s) hNlρ
    (fun cs hcs hno => hloc cs hcs hno hη0') (fun s _ cs hcs hno hnoF => hFlb s cs hcs hno hnoF)
    hMpA hW0
  refine ⟨X, hXR, hXd, hXl, hXsum.trans ?_⟩
  -- the final absorption
  have! nη1 : η₀ ≤ 1 := Real.exp_le_one_iff.mpr (by
    have! this : (0 : ℝ) ≤ (k : ℝ) ^ θ₀ := Real.rpow_nonneg (by linarith only [hk1]) _
    linarith only [this])
  have! nCN : 0 ≤ finiteDepthConstant κ q N := by
    have! this := (finiteDepthConstant_bounds κ hq2.le N).1; linarith only [this]
  have! nkD0 : 0 ≤ kD := by linarith only [hkDk, hkcc0]
  have! hNlF' : (Nl : ℝ) ≤ 4 * (6000 ^ 30 * Y ^ 30 + 1) := hNlF.trans h2F
  have! hG0 : 0 ≤ Real.exp ((1 + Real.log (2 * (k : ℝ))) ^ 2) ^ Cl := by positivity
  have! hkDCl0 : 0 ≤ kD ^ Cl := pow_nonneg nkD0 _
  have! nh1 : (Nl : ℝ) * Cl * kD ^ Cl * Real.exp ((1 + Real.log (2 * (k : ℝ))) ^ 2) ^ Cl ≤ P := by
    calc (Nl : ℝ) * Cl * kD ^ Cl * Real.exp ((1 + Real.log (2 * (k : ℝ))) ^ 2) ^ Cl
        ≤ 4 * (6000 ^ 30 * Y ^ 30 + 1) * Cl * kD ^ Cl *
            Real.exp ((1 + Real.log (2 * (k : ℝ))) ^ 2) ^ Cl := by gcongr
      _ ≤ _ := x3
      _ ≤ _ := hPlo
  have! nh2 : (Cl : ℝ) * kD ^ Cl + 2 ≤ P := x4.trans hPlo
  have! nh3 : (Nl : ℝ) * Cl * (2 + ((Cl : ℝ) + 1) * Real.log P) ^ 6 *
      Real.exp ((1 + Real.log (2 * (k : ℝ))) ^ 2) ^ Cl ≤ (P : ℝ) ^ (1 / 8 : ℝ) := by
    expose_names
    exact @retainedMin_holds_nh3 κ c' Cb θ₀ Cl hCl1 Mpad hMpad0 hL₄0 k B p hk3 bf x5 hPlo hPup hP1
      fp hexpd hNlF'
  have! nh4 : (Nl : ℝ) * (Cl * (kD * P) ^ Cl * Real.exp ((1 + Real.log (2 * (k : ℝ))) ^ 2) ^ Cl *
      (((P : ℝ) + 1) ^ 2 * τ₃ + Real.exp (Cl * (k : ℝ) ^ cc) * (Real.sqrt δ + Real.exp (-kD))) +
        Cl * Real.exp (-(k : ℝ))) + Mp * W ≤
      η₀ ^ min ((1 / 1200 : ℝ) / 2) ((1 / 1200 : ℝ) / (4 * (((Cl : ℝ) + 1) + 1)) / 4) := by
    expose_names
    exact @retainedMin_holds_nh4 κ c' Cb θ₀ hc' Ca C Cl hCl1 Mpad hMpad0 hL₄0 k B p hk3 hS2 bf hV
      hτ0 hPup hP1 hMpup fp hexpd x6 hδdef hWdef hNlF'
  have! hfin := retained_arith (Cl := Cl) (P := P) (k := k) (cc := cc) (kD := kD) (η₀ := η₀)
    (τ₃ := τ₃) (δ := δ) (CN := finiteDepthConstant κ q N) (Cq := Cq) (q := q)
    (R := dyadicGridLength A.G A.R.1) (Nlv := Nl) (Er := Mp * W) hη₀0 nη1 nCN hCq0 hR0.le
    (Nat.cast_nonneg _) nkD0 rfl hq2 hq3 hq.le nh1 nh2 nh3 nh4
  rw [hfpP, hηA]
  calc (Nl : ℝ) * leafBnd Cl kD P k cc (4 * η₀) η₀ τ₃ δ (finiteDepthConstant κ q N) Cq q
        (dyadicGridLength A.G A.R.1) + Mp * dyadicGridLength A.G A.R.1 * W
      = Nl * leafBnd Cl kD P k cc (4 * η₀) η₀ τ₃ δ (finiteDepthConstant κ q N) Cq q
        (dyadicGridLength A.G A.R.1) + Mp * W * dyadicGridLength A.G A.R.1 := by ring
    _ ≤ _ := hfin



private theorem retainedMin_holds_stage_3 : RetainedMinHoldsStage3Statement := by
  classical
  intro κ c' Cb θ₀ hc' Dst hst Ca b m hmult c₃ c C k₀ Dg a₀ cc hccdef hcc1 Cl K₀ hCl1 hleaf q hq2
    hq3 hq α cs hcs Cq hCq0 Cfin Mpad hMpad L₄ lW cH hMpad0 hL₄0 K k N d₀ B hwin p hk3 hK₀k hanc
    hS2 hcol η₀ hpairs hη hη₀0 δa hR0 hL0 A bf hsubA hne d hk1 Y p11 p12 p13 p14 p15 x5 hcbY hV
    hLcB hmaxB hHsB hcb2 Tc hTc hTcA Mp hMp1 hMpA hmultTc P τ₃ hτ₃def hτ0 hτ1 hPlo hPup hP1 nA4
    hMpup fp cat Kt n Tmax hfpP hLc hmH hHmax hMc hHed hcolr hKh hn0 hgrow hcapH hcats hloc hnpos
    hn4 hnle T p10 hkC0 hkm0 hY0 hexpd hHs2 hbase hl6 nHedV nHedτ₂ nHedτ' hHedge AD kD x3 x4 δ x6
    hδdef ρ hρdef hkcc1 hkcc0 hkDk nδ8 hdB ndδ nδN nρ0 h2F
  have! nρ1 : ρ < 1 := by
    rw [hρdef, div_lt_one (by positivity)]
    have! this := one_le_pow₀ (M₀ := ℝ) (n := A.famFuel) (by norm_num : (1 : ℝ) ≤ 2)
    linarith only [this]
  have! nkD : (k : ℝ) ^ cc ≤ kD := hkcc1.trans hkDk
  have! hLcfp : (fp.Lc : ℝ) = A.famLc := by rw [hLc]
  have! nB6 : Real.log (2 * (8 * A.colBudget + (1 + AD.Mp) * AD.n (AD.fp.Lc + 5))) ≤
      (k : ℝ) ^ cc := by
    expose_names
    exact @retainedMin_holds_nB6 κ c' Cb hc' Dst hst Ca C Mpad hMpad0 k B p bf hcbY hcb2 hTcA hMp1
      hmultTc hτ0 hτ1 hMpup fp cat Kt n Tmax hLc hmH hMc hHed hcolr hKh hn0 hgrow hcapH hcats
      hnpos hnle p10 hkC0 hkm0 hY0 hexpd nHedV nHedτ₂ nHedτ' hHedge
  have! nB7 : Real.log (2 * A.colBudget) ≤ (k : ℝ) ^ cc := by
    have! h1 := Real.log_le_log (by linarith only [hcb2]) (show 2 * A.colBudget ≤ 2 * Real.exp Y by
      linarith only [hcbY])
    rw [Real.log_mul (by norm_num) (Real.exp_pos _).ne', Real.log_exp] at h1
    exact h1.trans p11
  have! hccc : (c : ℝ) ≤ cc := by
    have! this : c ≤ cc := by
      rw [hccdef]; nlinarith only [show c < a₀ by omega, Nat.zero_le Dg]
    exact_mod_cast this
  have! hlogk0 : 0 ≤ Real.log k + 1 := by
    have! this := Real.log_nonneg hk1; linarith only [this]
  have! nB8 : ((2 * A.famFuel + 2 : ℕ) : ℝ) ≤ cc * (Real.log k + 1) :=
    nA4.trans (mul_le_mul_of_nonneg_right hccc hlogk0)
  have! nB9 : (AD.fp.Lc : ℝ) + 6 ≤ (k : ℝ) ^ cc := by
    have! this : (fp.Lc : ℝ) + 6 ≤ (k : ℝ) ^ cc := by
      rw [hLcfp]
      have! h0 : 0 ≤ 6000 ^ 30 * Y ^ 30 + 1 := by positivity
      linarith only [hLcB, p12, h0]
    exact this
  have! nB10 : (AD.fp.Hmax : ℝ) + 1 ≤ ((k : ℝ) * AD.fp.P) ^ cc := by
    have! this : (fp.Hmax : ℝ) + 1 ≤ ((k : ℝ) * fp.P) ^ cc := by
      rw [hHmax, hfpP, mul_pow]
      unfold ActiveSetup.famHmax
      push_cast
      have! hP0' : (0 : ℝ) ≤ P := by linarith only [hP1]
      have! h1 : 20 * (P : ℝ) * (A.famLc + 1) + 40 * P + 1 ≤ P * (k : ℝ) ^ cc := by
        have! h2 : (20 : ℝ) * A.famLc + 61 ≤ (k : ℝ) ^ cc := by
          have! h0 : 0 ≤ 6000 ^ 30 * Y ^ 30 + 1 := by positivity
          linarith only [hLcB, p12, h0]
        nlinarith only [h2, hP1, hP0']
      have! h3 : (P : ℝ) ≤ (P : ℝ) ^ cc := le_self_pow₀ hP1 (by omega)
      have! h4 : (0 : ℝ) ≤ (k : ℝ) ^ cc := by positivity
      calc _ ≤ P * (k : ℝ) ^ cc := h1
        _ ≤ (P : ℝ) ^ cc * (k : ℝ) ^ cc := mul_le_mul_of_nonneg_right h3 h4
        _ = _ := by ring
    exact this
  have! nB11 : (A.dBnd : ℝ) ≤ (k : ℝ) ^ cc := by linarith only [hdB, p13]
  have! nB12 : Real.log AD.fp.Hed ≤ (k : ℝ) ^ cc := by
    expose_names
    exact @retainedMin_holds_nB12 κ c' Cb θ₀ hc' Dst hst Ca C k₀ Cl K₀ Mpad hMpad0 K k B p hk3 bf
      hk1 hV hHsB hTcA hMp1 hmultTc hτ₃def hτ0 hτ1 fp cat Kt n Tmax hLc hmH hMc hHed hcolr hKh hn0
      hgrow hcapH hcats hn4 hnle hkC0 hkm0 hY0 hHs2 hbase hl6 nHedV nHedτ₂ nHedτ' hHedge
  expose_names
  exact @retainedMin_holds_stage_4 κ c' Cb θ₀ hc' Dst hst Ca hmult C k₀ hccdef Cl K₀ hCl1 hleaf q
    hq2 hq3 hq hcs hCq0 Mpad hMpad hMpad0 hL₄0 K k N d₀ B hwin p hk3 hK₀k hanc hS2 hcol hpairs hη
    hη₀0 hR0 hL0 bf hsubA hne d hk1 p13 p14 p15 x5 hV hmaxB hHsB hTc hTcA hMp1 hMpA hmultTc hτ0
    hτ1 hPlo hPup hP1 hMpup fp cat Kt n Tmax hfpP hLc hmH hMc hHed hcolr hKh hn0 hgrow hcapH hcats
    hloc hexpd nHedV nHedτ₂ nHedτ' hHedge x3 x4 x6 hδdef hρdef hkcc0 hkDk nδ8 ndδ nδN nρ0 h2F nρ1
    nkD nB6 nB7 nB8 nB9 nB10 nB11 nB12



private theorem retainedMin_holds_stage_2 : RetainedMinHoldsStage2Statement := by
  classical
  intro κ c' Cb θ₀ hc' Dst hst Ca hCa b m hmult c₃ c C k₀ Dg a₀ cc hccdef hcc1 Cl K₀ hCl1 hleaf q
    hq2 hq3 hq α cs hcs Cq hCq0 Cfin Mpad hMpad L₄ lW cH hMpad0 hL₄0 hW1 K k N d₀ B hwin p hk3 x4
    hK₀k hanc hH1 hS2 hcol η₀ hpairs hη hη₀0 δa hR0 hL0 A bf hsubA hne d hk1 Y p7 p8 p9 p10 p11
    p12 p13 p14 p15 x2 x3 x5 hY1 hcbY hV hLcB hfuelB hmaxB hHsB hcb2 Tc hTc hTcA Mp hMp1 hMpA
    hmultTc P τ₃ x6 hτ₃def hτ0 hτ1 hPlo hPup hP1 nA4 hMpup fp cat Kt n Tmax hfpP hLc hmH hHmax hMc
    hHed hcolr hKh hn0 hgrow hcapH hcats hloc hnpos hn4 hnle hsqle
  set! T : ℝ := Y + (k : ℝ) ^ C + Ca * (k : ℝ) ^ m + 2 with hTdef
  rewrite [← hTdef] at p8 p10
  have! hkC0 : (0 : ℝ) ≤ (k : ℝ) ^ C := by positivity
  have! hkm0 : (0 : ℝ) ≤ Ca * (k : ℝ) ^ m := by positivity
  have! hY0 : 0 ≤ Y := by linarith only [hY1]
  have! hexpd : ∀ x y : ℝ, Real.exp x * Real.exp y = Real.exp (x + y) := fun x y =>
    (Real.exp_add x y).symm
  have! hHs2 : 2 ≤ Real.log A.Hsrc := by
    have! this := Real.log_le_log (Real.exp_pos 2) A.exp_two_le_Hsrc; rwa [Real.log_exp] at this
  have hDgA : (A.Dg : ℝ) = Dg := rfl
  have! hDg0 : (0 : ℝ) ≤ Dg := Nat.cast_nonneg _
  have! hbase : ∀ w : ℝ, 0 ≤ w → w ≤ 1 + (cH + 2 * (lW + Y)) + Real.log 6 +
      3 * (Y + (k : ℝ) ^ C + Ca * (k : ℝ) ^ m + 2) + (k : ℝ) ^ c₃ + 2 * (Y + 3) →
      (A.Dg : ℝ) * w ^ A.Dg ≤ (k : ℝ) ^ cc := fun w hw0 hw => by
    rw [hDgA]
    exact (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hw0 hw Dg) hDg0).trans p8
  have! hl6 : 0 ≤ Real.log 6 := Real.log_nonneg (by norm_num)
  -- the attempt data
  have! hmax0 : 0 < max A.H ActiveSetup.padW :=
    lt_of_lt_of_le one_pos (hW1.trans (le_max_right _ _))
  have! nHedV : 18 * max A.H ActiveSetup.padW ^ 2 ≤ Real.exp ((k : ℝ) ^ cc) := by
    have! h1 : Real.log (18 * max A.H ActiveSetup.padW ^ 2) ≤ (k : ℝ) ^ cc := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      push_cast
      linarith only [hmaxB, p7]
    calc 18 * max A.H ActiveSetup.padW ^ 2 =
          Real.exp (Real.log (18 * max A.H ActiveSetup.padW ^ 2)) :=
        (Real.exp_log (by positivity)).symm
      _ ≤ _ := Real.exp_le_exp.mpr h1
  have! nHedτ₂ : Real.exp (A.Dg * (1 + Real.log A.Hsrc +
      Real.log (τ₃ / (1 + A.colBudget * Real.sqrt (n (fp.Lc + 4)) *
        (A.colBudget * Real.sqrt (2 * A.colBudget + (1 + Mp) * n (fp.Lc + 5)))))⁻¹) ^ A.Dg) ≤
      Real.exp ((k : ℝ) ^ cc) := by
    expose_names
    exact @retainedMin_holds_nHedτ₂ κ c' Cb Ca b rfl m rfl c₃ rfl C cc Mpad L₄ rfl lW rfl cH rfl k
      hk3 A bf Y rfl hcbY hHsB hcb2 Mp rfl τ₃ hτ₃def hτ0 hMpup fp n hnpos hn4 hnle hsqle T hTdef
      hkC0 hkm0 hY0 hexpd hHs2 hbase
  have! nHedτ' : Real.exp (A.Dg * (1 + Real.log A.Hsrc +
      Real.log (1 + (⌈8 * A.colBudget + n (fp.Lc + 5)⌉₊ : ℝ) * A.colBudget ^ 2)) ^ A.Dg) ≤
      Real.exp ((k : ℝ) ^ cc) := by
    expose_names
    exact @retainedMin_holds_nHedτ_ κ c' Cb Ca b rfl m rfl c₃ rfl C cc Mpad L₄ rfl lW rfl cH rfl k
      hk3 A bf Y rfl hcbY hHsB hcb2 fp n hnpos hnle hkC0 hkm0 hY0 hexpd hHs2 hbase
  have! hHedge : Real.exp ((k : ℝ) ^ cc) ≤ fp.Hed := by rw [hHed]; exact le_max_left _ _
  let AD : bf.AttemptData p :=
    { fp := fp, cat := cat, Tc := Tc, hTc := hTcA, Mp := Mp, hMp1 := hMp1, hmult := hmultTc,
      Dst := Dst, hst := hst, τ₃ := τ₃, hτ₃ := hτ0, hτ₃1 := hτ1, Kt := Kt, n := n, Tmax := Tmax,
      hLc := hLc, hmH := hmH, hMc := hMc, hcol := hcolr, hKh := hKh, hn0 := hn0, hgrow := hgrow,
      hcapH := hcapH, hpassM := fun l => (hcats l).1, hT := fun l => (hcats l).2.1,
      htag := fun l => (hcats l).2.2.1, hlab := fun l => (hcats l).2.2.2.1,
      hlen := fun l => (hcats l).2.2.2.2, hHedV := nHedV.trans hHedge,
      hHed2 := by rw [hHed]; exact le_max_of_le_right (le_max_left _ _),
      hHedτ₂ := nHedτ₂.trans hHedge, hHedτ' := nHedτ'.trans hHedge }
  -- the parameters of the leaf estimates
  set! kD : ℝ := (2 * Cl + 2) * (k : ℝ) ^ (cc + 1) with hkDdef
  rewrite [← hkDdef] at x4 x2 x3 x6
  set! δ : ℝ := Real.exp (-kD) with hδdef
  rewrite [← hδdef] at x6
  set! ρ : ℝ := 1 / (96 * 2 ^ A.famFuel) with hρdef
  have! hkcc1 : (k : ℝ) ^ cc ≤ (k : ℝ) ^ (cc + 1) := pow_le_pow_right₀ hk1 (by omega)
  have! hkcc0 : (0 : ℝ) ≤ (k : ℝ) ^ (cc + 1) := by positivity
  have! hClr : (0 : ℝ) ≤ Cl := Nat.cast_nonneg _
  have! hkDk : (k : ℝ) ^ (cc + 1) ≤ kD := by
    rw [hkDdef]; nlinarith only [hkcc0, hClr]
  have! hk2 : (9 : ℝ) ≤ (k : ℝ) ^ (cc + 1) := by
    have! h3 : (3 : ℝ) ≤ k := by exact_mod_cast hk3
    have! this : (k : ℝ) ^ 2 ≤ (k : ℝ) ^ (cc + 1) := pow_le_pow_right₀ hk1 (by omega)
    nlinarith only [this, h3]
  have! hδexp : δ * Real.exp kD = 1 := by
    rw [hδdef, ← Real.exp_add]; simp
  have! nδ8 : δ ≤ 1 / 8 := by
    have! h1 := Real.add_one_le_exp kD
    have! h2 : 0 < δ := Real.exp_pos _
    nlinarith only [h1, hδexp, h2, hkDk, hk2]
  have! hdB : (A.dBnd : ℝ) ≤ lW + Y + 1 := by
    unfold ActiveSetup.dBnd
    have! h0 : 0 ≤ Real.log (max A.H ActiveSetup.padW) :=
      Real.log_nonneg (hW1.trans (le_max_right _ _))
    have! this := (Nat.ceil_lt_add_one h0).le
    linarith only [this, hmaxB]
  have! ndδ : 8 * A.dBnd * δ ≤ 1 := by
    have! h2 : 0 < δ := Real.exp_pos _
    have! h3 : 8 * (A.dBnd : ℝ) ≤ Real.exp kD := le_trans (by linarith only [hdB]) x2
    nlinarith only [h3, hδexp, h2]
  have! nδN : δ ^ 2 * AD.n (AD.fp.Lc + 5) * A.colBudget ^ 2 ≤ 1 := by
    have! h2 : 0 < δ := Real.exp_pos _
    have! hn5' : n (fp.Lc + 5) ≤ Real.exp ((k : ℝ) ^ C) := hnle _ le_rfl
    have! hcb0 : 0 ≤ A.colBudget := by linarith only [hcb2]
    have! h3 : A.colBudget ^ 2 ≤ Real.exp (2 * Y) := by
      rw [show 2 * Y = Y + Y by ring, ← hexpd, sq]
      exact mul_le_mul hcbY hcbY hcb0 (Real.exp_pos _).le
    have! h4 : n (fp.Lc + 5) * A.colBudget ^ 2 ≤ Real.exp ((k : ℝ) ^ C + 2 * Y) := by
      rw [← hexpd]; exact mul_le_mul hn5' h3 (by positivity) (Real.exp_pos _).le
    have! h5 : Real.exp ((k : ℝ) ^ C + 2 * Y) ≤ Real.exp kD * Real.exp kD := by
      rw [hexpd]; exact Real.exp_le_exp.mpr (by linarith only [p9, hkDk, hkcc0])
    have! h6 : δ ^ 2 * (Real.exp kD * Real.exp kD) = 1 := by
      calc δ ^ 2 * (Real.exp kD * Real.exp kD) = (δ * Real.exp kD) * (δ * Real.exp kD) := by
            ring
        _ = 1 := by rw [hδexp]; ring
    have! h7 : 0 ≤ δ ^ 2 := sq_nonneg _
    calc δ ^ 2 * AD.n (AD.fp.Lc + 5) * A.colBudget ^ 2 =
          δ ^ 2 * (n (fp.Lc + 5) * A.colBudget ^ 2) := by ring
      _ ≤ δ ^ 2 * (Real.exp kD * Real.exp kD) :=
          mul_le_mul_of_nonneg_left (h4.trans h5) h7
      _ = 1 := h6
  have! nρ0 : 0 < ρ := by rw [hρdef]; positivity
  have! h2F : (2 : ℝ) ^ A.famFuel ≤ 4 * (6000 ^ 30 * Y ^ 30 + 1) :=
    hfuelB.trans (by linarith only [hLcB])
  expose_names
  exact @retainedMin_holds_stage_3 κ c' Cb θ₀ hc' Dst hst Ca hmult C k₀ hccdef hcc1 Cl K₀ hCl1
    hleaf q hq2 hq3 hq hcs hCq0 Mpad hMpad hMpad0 hL₄0 K k N d₀ B hwin p hk3 hK₀k hanc hS2 hcol
    hpairs hη hη₀0 hR0 hL0 bf hsubA hne d hk1 p11 p12 p13 p14 p15 x5 hcbY hV hLcB hmaxB hHsB hcb2
    hTc hTcA hMp1 hMpA hmultTc hτ₃def hτ0 hτ1 hPlo hPup hP1 nA4 hMpup fp cat Kt n Tmax hfpP hLc
    hmH hHmax hMc hHed hcolr hKh hn0 hgrow hcapH hcats hloc hnpos hn4 hnle p10 hkC0 hkm0 hY0 hexpd
    hHs2 hbase hl6 nHedV nHedτ₂ nHedτ' hHedge x3 x4 x6 hδdef hρdef hkcc1 hkcc0 hkDk nδ8 hdB ndδ
    nδN nρ0 h2F



private theorem retainedMin_holds_stage_1 : RetainedMinHoldsStage1Statement := by
  classical
  intro κ c' Cb θ₀ hc' Dst hst Ca hCa b m hmult c₃ c C k₀ hatt Dg a₀ cc hccdef hcc1 Cl K₀ hCl1
    hleaf q hq2 hq3 hq α cs hcs Cq hCq0 Cfin Mpad hMpad L₄ hL₄ lW cH hMpad0 hL₄0 hW1 K k N d₀ B
    hwin p hk3 p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 x1 x2 x3 x4 x5 hk₀k hK₀k hanc
    hH1 hHk hDck hLk hS2 hcol η₀ hpairs hη x6 hη₀def hη₀0 δa hmB hR0 hL0 A bf hsubA hne hV
  obtain ⟨d⟩ := hV
  -- the bounds of the padded setup in terms of `Y = L₄ + 2 k^b`
  have! hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (show 1 ≤ k by omega)
  have! hkCb : (k : ℝ) ^ Cb ≤ (k : ℝ) ^ b := pow_le_pow_right₀ hk1 (by omega)
  have! hkb1 : (1 : ℝ) ≤ (k : ℝ) ^ b := one_le_pow₀ hk1
  set Y : ℝ := L₄ + 2 * (k : ℝ) ^ b with hYdef
  have! hY1 : 1 ≤ Y := by rw [hYdef]; linarith only [hL₄0, hkb1]
  have! hHY : A.H ≤ Real.exp Y :=
    hHk.trans (Real.exp_le_exp.mpr (by rw [hYdef]; linarith only [hkCb, hL₄0, hkb1]))
  have! hcbY : A.colBudget ≤ Real.exp Y := by
    expose_names
    exact @retainedMin_holds_hcbY κ c' Cb b rfl Mpad hMpad L₄ rfl hL₄ hMpad0 k B hk3 hDck hLk A
      rfl hkCb Y hYdef
  obtain ⟨hV, -, hLcB, hfuelB, hmaxB, hHsB⟩ := A.attempt_param_bounds hY1 hHY hcbY
  have! hLc0 : (0 : ℝ) ≤ A.famLc := Nat.cast_nonneg _
  have hcb2 : (2 : ℝ) ≤ A.colBudget := A.two_le_colBudget
  -- the fuel: `fuel ≤ log₂ (4 (6000^{30} Y^{30} + 1))`
  have! hfuelL : (A.famFuel : ℝ) ≤ Real.log (4 * (6000 ^ 30 * Y ^ 30 + 1)) / Real.log 2 := by
    rw [le_div_iff₀ (Real.log_pos one_lt_two)]
    have! h1 : (2 : ℝ) ^ A.famFuel ≤ 4 * (6000 ^ 30 * Y ^ 30 + 1) :=
      hfuelB.trans (by linarith only [hLcB])
    have! h2 := Real.log_le_log (by positivity) h1
    rw [Real.log_pow] at h2
    linarith only [h2]
  -- the active test cells and their multiplicity
  set! Tc := A.cells.filter (A.active δa) with hTc
  have! hTcA : Tc ⊆ A.cells := Finset.filter_subset _ _
  set! Mp : ℕ := ⌈Real.exp (Ca * (k : ℝ) ^ (3 * Cb + 2))⌉₊ with hMpdef
  have! hMp1 : 1 ≤ Mp := Nat.one_le_ceil_iff.mpr (Real.exp_pos _)
  have! hMpA : ∀ y : ℝ, ((A.cells.filter fun I => y ∈ dyadicGridCell A.G I.1 I.2 ∧
      A.active δa I).card : ℝ) ≤ Mp := fun y => (hmB y).trans (Nat.le_ceil _)
  have! hmultTc : ∀ I : ℤ × ℤ, (Tc.filter fun I' : ℤ × ℤ =>
      dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G I'.1 I'.2).card ≤ Mp := fun I => by
    have! h1 := A.active_anc_card_le Tc (fun I' hI' => Finset.mem_filter.mp hI') I
    have! h2 := hMpA (dyadicGridLeft A.G I.1 I.2)
    exact h1.trans (by exact_mod_cast h2)
  -- the pads, the closure accuracy and the attempt
  set! P : ℕ := ⌈η₀ ^ (-α)⌉₊ with hPdef
  have! hP0 : 0 < P := by
    rw [hPdef]
    exact Nat.ceil_pos.mpr (Real.rpow_pos_of_pos hη₀0 _)
  set! τ₃ : ℝ := Real.exp (-(k : ℝ) ^ c₃) with hτ₃def
  rewrite [← hτ₃def] at x6
  have! hτ0 : 0 < τ₃ := Real.exp_pos _
  have! hτ1 : τ₃ ≤ 1 := Real.exp_le_one_iff.mpr (by
    have! this := pow_nonneg (Nat.cast_nonneg (α := ℝ) k) c₃; linarith only [this])
  have! hηα : η₀ ^ (-α) = Real.exp (2 * α * (k : ℝ) ^ θ₀) := by
    rw [hη₀def, ← Real.exp_mul]; ring_nf
  have! hPlo : Real.exp (2 * α * (k : ℝ) ^ θ₀) ≤ P := by rw [← hηα]; exact Nat.le_ceil _
  have! hPup : (P : ℝ) ≤ Real.exp (2 * α * (k : ℝ) ^ θ₀) + 1 := by
    rw [← hηα]; exact (Nat.ceil_lt_add_one (Real.rpow_nonneg hη₀0.le _)).le
  have! hP1 : (1 : ℝ) ≤ P := le_trans (Real.one_le_exp (by positivity)) hPlo
  have! nA1 : (A.famLc + 6 : ℝ) ≤ (k : ℝ) ^ c := by linarith only [hLcB, p1]
  have! nA2 : (A.famVtxBound : ℝ) ≤ Real.exp ((k : ℝ) ^ c) :=
    hV.trans (Real.exp_le_exp.mpr p2)
  have! nA3 : (A.famHmax P + 1 : ℝ) ≤ Real.exp ((k : ℝ) ^ c) := by
    unfold ActiveSetup.famHmax
    push_cast
    have! h0 : (20 : ℝ) * (A.famLc + 1) + 40 ≤ 20 * (6000 ^ 30 * Y ^ 30 + 1) + 60 := by
      linarith only [hLcB]
    have! hP0' : (0 : ℝ) ≤ P := by linarith only [hP1]
    calc 20 * (P : ℝ) * (A.famLc + 1) + 40 * P + 1 = P * (20 * (A.famLc + 1) + 40) + 1 := by ring
      _ ≤ (Real.exp (2 * α * (k : ℝ) ^ θ₀) + 1) * (20 * (6000 ^ 30 * Y ^ 30 + 1) + 60) + 1 := by
          gcongr
      _ ≤ _ := x1
  have! nA4 : ((2 * A.famFuel + 2 : ℕ) : ℝ) ≤ c * (Real.log k + 1) := by
    push_cast; linarith only [hfuelL, p3]
  have! nA5 : Real.log A.Hsrc ≤ (k : ℝ) ^ c := hHsB.trans p4
  have! nτ : τ₃⁻¹ ≤ Real.exp ((k : ℝ) ^ c) := by
    rw [hτ₃def, Real.exp_neg, inv_inv]
    exact Real.exp_le_exp.mpr (pow_le_pow_right₀ hk1 (by omega))
  have! hMpup : (Mp : ℝ) ≤ Real.exp (Ca * (k : ℝ) ^ m) + 1 :=
    (Nat.ceil_lt_add_one (Real.exp_pos _).le).le
  have! nMp : (Mp : ℝ) ≤ Real.exp ((k : ℝ) ^ c) := hMpup.trans p5
  have! ncb : 2 * A.colBudget ≤ Real.exp ((k : ℝ) ^ c) := le_trans (by linarith only [hcbY]) p6
  have! nBh : (Fintype.card (Fin A.famVtxBound) : ℝ) ≤ Real.exp ((k : ℝ) ^ c) := by
    rw [Fintype.card_fin]; exact nA2
  obtain ⟨fp, cat, Kt, n, Tmax, hfpP, hLc, hmH, hHmax, hMc, hHed, hcolr, hKtT, hKh, hlogKt, hn0,
    hgrow, hn5, hcapH, hlogn, hlogT, hcats, hloc⟩ := hatt bf (k := (k : ℝ)) hk₀k hst p Tc hTcA d P
    hP0 (τ₃ := τ₃) (Mp := Mp) (Fin A.famVtxBound) (fun _ _ _ => Real.exp ((k : ℝ) ^ cc))
    (fun _ _ Tmax => Tc.card * Tmax) nA1 nA2 nA3 nA4 nA5 hτ0 hτ1 nτ hMp1 nMp ncb nBh hmultTc
  -- the closure counts are increasing, at least `4`, and at most `e^{k^C}` up to `L + 5`
  have! hR0c := closureRatio_nonneg A.famVtxBound Kt fp.mH Tmax
    (Real.exp (Dst * (1 + Real.log A.Hsrc) ^ Dst)) τ₃
  have! hfac : (1 : ℝ) ≤ 1 + (fp.Lc + 6) * Mp * closureRatio A.famVtxBound Kt fp.mH Tmax
      (Real.exp (Dst * (1 + Real.log A.Hsrc) ^ Dst)) τ₃ := by
    have! this : (0 : ℝ) ≤ (fp.Lc + 6) * Mp * closureRatio A.famVtxBound Kt fp.mH Tmax
      (Real.exp (Dst * (1 + Real.log A.Hsrc) ^ Dst)) τ₃ := by positivity
    linarith only [this]
  have! hnpos : ∀ r, 0 ≤ n r := by
    intro r
    induction r with
    | zero => linarith only [hn0, hcb2]
    | succ r ih =>
      have! h1 := hgrow r
      have! this : (0 : ℝ) ≤ (1 + (fp.Lc + 6) * Mp * closureRatio A.famVtxBound Kt fp.mH Tmax
        (Real.exp (Dst * (1 + Real.log A.Hsrc) ^ Dst)) τ₃) * n r :=
        mul_nonneg (by linarith only [hfac]) ih
      linarith only [h1, this]
  have! hn_mono : Monotone n :=
    monotone_nat_of_le_succ fun r => (le_mul_of_one_le_left (hnpos r) hfac).trans (hgrow r)
  have! hn4 : ∀ r, 4 ≤ n r := fun r =>
    le_trans (by linarith only [hn0, hcb2]) (hn0.trans (hn_mono (Nat.zero_le r)))
  have! hTmax : (Tmax : ℝ) ≤ Real.exp ((k : ℝ) ^ C) := by
    have! hT0 : (0 : ℝ) < Tmax := lt_of_lt_of_le (by linarith only [hn4 (fp.Lc + 5)]) hn5
    rw [← Real.exp_log hT0]; exact Real.exp_le_exp.mpr hlogT
  have! hnle : ∀ r ≤ fp.Lc + 5, n r ≤ Real.exp ((k : ℝ) ^ C) := fun r hr =>
    (hn_mono hr).trans (hn5.trans hTmax)
  have! hsqle : ∀ x : ℝ, 1 ≤ x → Real.sqrt x ≤ x := fun x hx =>
    Real.sqrt_le_iff.mpr ⟨by linarith only [hx], by nlinarith only [hx]⟩
  -- the exponent `T` of the counts
  expose_names
  exact @retainedMin_holds_stage_2 κ c' Cb θ₀ hc' Dst hst Ca hCa hmult C k₀ hccdef hcc1 Cl K₀ hCl1
    hleaf q hq2 hq3 hq hcs hCq0 Mpad hMpad hMpad0 hL₄0 hW1 K k N d₀ B hwin p hk3 x4 hK₀k hanc hH1
    hS2 hcol hpairs hη hη₀0 hR0 hL0 bf hsubA hne d hk1 p7 p8 p9 p10 p11 p12 p13 p14 p15 x2 x3 x5
    hY1 hcbY hV hLcB hfuelB hmaxB hHsB hcb2 hTc hTcA hMp1 hMpA hmultTc x6 hτ₃def hτ0 hτ1 hPlo hPup
    hP1 nA4 hMpup fp cat Kt n Tmax hfpP hLc hmH hHmax hMc hHed hcolr hKh hn0 hgrow hcapH hcats
    hloc hnpos hn4 hnle hsqle


open Classical in
/-- Blueprint lines 2838-2888 on one root (prop:normalized, `eq:before-absorption` and the choice
of `q, α, P`): the retained-attempt estimate `RetainedMin`. The setup is padded so that the
vertex bound of the attempt makes the failure roots at most `|R|/8`; the attempt localizes the
active minima to the leaves of the guarded search, each leaf has the explicit bound of
`leaf_estimate` outside six cut families, the cuts and failure roots are united at most `|R|/4`
(`root_assembly`), and the parameters `P = ⌈η₀^{-α}⌉`, `k_D`, `δ`, `τ₃`, `ρ` absorb all costs
(`retained_arith`) for every large `k`. -/
theorem retainedMin_holds (κ : LocalKernelClass) : RetainedMin κ := by
  intro c' Cb θ₀ hc' hθ₀ hθ₁
  -- the constants of the class of setups
  obtain ⟨Dst, -, hst⟩ := sameTagBound_exists κ (max c' (2 * tagKρ)) (le_max_of_le_left hc')
  obtain ⟨Ca, hCa, hmult⟩ := active_mult_bound κ c' hc' Cb
  set b : ℕ := Cb + 1 with hb
  set m : ℕ := 3 * Cb + 2 with hm
  set c₃ : ℕ := 3 * Cb + 3 with hc₃
  set c : ℕ := 90 * b + c₃ + 100 with hcdef
  obtain ⟨C, k₀, hk₀, hatt⟩ := ActiveSetup.BasicFamilies.exists_attempt c Dst
  set! Dg : ℕ := Classical.choose (curvatureGraph κ (max c' (2 * tagKρ) + 1) (by omega)) with hDg
  set! a₀ : ℕ := C + c + 1 with ha₀
  set! cc : ℕ := (a₀ + 1) * (Dg + 2) with hccdef
  have! hcc1 : 1 ≤ cc := by rw [hccdef]; exact Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)
  obtain ⟨Cl, K₀, hCl1, hK₀, hleaf⟩ := ActiveSetup.BasicFamilies.leaf_estimate κ c' cc hcc1
  obtain ⟨q, hq2, hq3, hq⟩ := exists_exponent_near_two ((Cl : ℝ) + 1) (by positivity)
  set! α : ℝ := (1 / 1200 : ℝ) / (4 * (((Cl : ℝ) + 1) + 1)) with hα
  set! cs : ℝ := min ((1 / 1200 : ℝ) / 2) (α / 4) with hcs
  set! Cq : ℝ := nbCM κ hq2 hq3 + nbCUM κ hq2 hq3 with hCq
  have! hCq0 : 0 ≤ Cq := by
    have! h1 := nbCM_nonneg κ hq2 hq3
    have! h2 := (Classical.choose_spec (near_band_critical_UM κ hq2 hq3)).1
    change 0 ≤ nbCUM κ hq2 hq3 at h2
    rw [hCq]; linarith only [h1, h2]
  set! Cfin : ℝ := (3 + Cq) * (2 ^ ((Cl : ℝ) + 1) + 1) + 1 with hCfin
  -- the eventual numeric facts
  obtain ⟨Mpad, hMpad⟩ : ∃ x : ℝ, x = 800 * 2001 ^ 7 := ⟨_, rfl⟩
  set! L₄ : ℝ := Real.log (4 + Mpad) with hL₄
  set! lW : ℝ := Real.log ActiveSetup.padW with hlW
  set! cH : ℝ := Real.log ((tagKρ : ℝ) ^ (2 * tagKρ) + 20) with hcH
  have! hMpad0 : (0 : ℝ) ≤ Mpad := by rw [hMpad]; norm_num
  have! hL₄0 : 0 ≤ L₄ := Real.log_nonneg (by linarith only [hMpad0])
  have! hW1 : (1 : ℝ) ≤ ActiveSetup.padW :=
    le_trans (by linarith only [Real.add_one_le_exp (2 : ℝ)]) (le_max_left _ _)
  have! hlW0 : 0 ≤ lW := Real.log_nonneg hW1
  have! hcH0 : 0 ≤ cH := Real.log_nonneg (by
    have! this : (0 : ℝ) ≤ (tagKρ : ℝ) ^ (2 * tagKρ) := by positivity
    linarith only [this])
  have! hα0 : 0 < α := by rw [hα]; positivity
  have! hα8 : α ≤ 1 / 9600 := by
    rw [hα, div_le_iff₀ (by positivity)]
    have! this : (0 : ℝ) ≤ Cl := Nat.cast_nonneg _
    linarith only [this]
  have! hcc_a : a₀ * Dg < cc := by
    rw [hccdef]; nlinarith only [Nat.zero_le a₀, Nat.zero_le Dg]
  have! hcc_b : a₀ < cc := by
    rw [hccdef]; nlinarith only [Nat.zero_le a₀, Nat.zero_le Dg]
  have! hev := ((Filter.eventually_ge_atTop ⌈k₀⌉₊).and ((Filter.eventually_ge_atTop ⌈K₀⌉₊).and
    (Filter.eventually_ge_atTop 3))).and
    ((retained_numeric_poly (Dg := Dg) (a₀ := a₀) (cc := cc) (C := C) (c₃ := c₃) hL₄0 hlW0 hcH0
      hCa (show 1 ≤ b by omega) (show 30 * b < c by omega) (show m < c by omega)
      (show c₃ < a₀ by omega) (show 90 * b + 100 ≤ c by omega) (show c < a₀ by omega)
      (show C < a₀ by omega) hcc_a hcc_b).and
    (retained_numeric_exp (lW := lW) (c := c) (cc := cc) (Cl := Cl) hL₄0 hlW0 hα0 hα8 hθ₀ hθ₁
      hCa (show 1 ≤ b by omega) (show 30 * b < c by omega) (show m < c₃ by omega)
      (show b < c₃ by omega) (show 1 ≤ m by omega) hcc1))
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp hev
  refine ⟨q, hq2, hq3, cs, Cfin, by positivity, by positivity, K,
    fun k hk N d₀ B hwin hprops p => ?_⟩
  obtain ⟨⟨hk₀c, hK₀c, hk3⟩, ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14,
    p15⟩, ⟨x1, x2, x3, x4, x5, x6⟩⟩ := hK k hk
  have! hk₀k : k₀ ≤ (k : ℝ) := Nat.ceil_le.mp hk₀c
  have! hK₀k : K₀ ≤ (k : ℝ) := Nat.ceil_le.mp hK₀c
  have! hmB := hmult k (by omega) B _ hprops
  obtain ⟨hanc, hH1, hHk, hDck, hLk, hS2, hη, hpairs, -, -, -, hcol, hsub⟩ := hprops
  set! η₀ : ℝ := Real.exp (-2 * (k : ℝ) ^ θ₀) with hη₀def
  rewrite [← hη₀def] at x6 hη hpairs hsub ⊢
  have! hη₀0 : 0 < η₀ := Real.exp_pos _
  set! δa : ℝ := Real.exp (-(k : ℝ) ^ (Cb + 2)) with hδa
  rewrite [← hδa] at hmB ⊢
  have! hR0 := dyadicGridLength_pos B.G B.R.1
  have! hRHS0 : 0 ≤ Cfin * η₀ ^ cs * (1 + finiteDepthConstant κ q N) *
      dyadicGridLength B.G B.R.1 := by
    have! this := (finiteDepthConstant_bounds κ hq2.le N).1
    have! this : 0 ≤ η₀ ^ cs := Real.rpow_nonneg hη₀0.le _
    have! this : 0 ≤ Cfin := by rw [hCfin]; positivity
    positivity
  -- without labels or cells no cell is active
  by_cases hL0 : Fintype.card B.L = 0
  · refine ⟨∅, by simp, by simp, by
      simp only [Finset.sum_empty, one_div, inv_pos, Nat.ofNat_pos, mul_nonneg_iff_of_pos_left]
      positivity, ?_⟩
    rw [Finset.filter_false_of_mem (fun I _ => B.not_active_of_card_eq_zero hL0 _ I),
      Finset.sum_empty]
    exact hRHS0
  -- the padded setup and its basic families
  set! A := B.padDc Mpad hMpad0 with hA
  have! hcolA : A.HasColumnRep 1 := ActiveSetup.HasColumnRep.padDc hMpad0 hcol
  obtain ⟨bf⟩ := ActiveSetup.HasColumnRep.families hcolA
  have! hsubA : A.SubRootProps η₀ ((k : ℝ) ^ Cb) := ActiveSetup.SubRootProps.padDc hMpad0 hsub
  by_cases hne : B.cells.Nonempty
  swap
  · refine ⟨∅, by simp, by simp, by
      simp only [Finset.sum_empty, one_div, inv_pos, Nat.ofNat_pos, mul_nonneg_iff_of_pos_left]
      positivity, ?_⟩
    rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    simpa using hRHS0
  by_cases hV : Nonempty bf.Vtx
  swap
  · -- without basic columns all pattern forms vanish
    refine ⟨∅, by simp, by simp, by
      simp only [Finset.sum_empty, one_div, inv_pos, Nat.ofNat_pos, mul_nonneg_iff_of_pos_left]
      positivity, ?_⟩
    calc ∑ I ∈ (B.cells.filter (fun I => ¬ ∃ c ∈ (∅ : Finset (ℤ × ℤ)),
          dyadicGridCell B.G I.1 I.2 ⊆ dyadicGridCell B.G c.1 c.2)).filter (B.active δa),
          dyadicGridLength B.G I.1 * min B.η ‖B.Hf I (B.z (Fin.castSucc p) I)‖ = 0 := by
          refine Finset.sum_eq_zero fun I hI => ?_
          have! hIc : I ∈ A.cells := (Finset.mem_filter.mp (Finset.mem_filter.mp hI).1).1
          have! h0 : A.Hf I (A.z (Fin.castSucc p) I) = 0 :=
            A.Hf_z_eq_zero_of_isEmpty_vtx bf hV p hIc
          change dyadicGridLength A.G I.1 * min A.η ‖A.Hf I (A.z (Fin.castSucc p) I)‖ = 0
          rw [h0, norm_zero]
          have! hη0 : 0 ≤ A.η := by
            change 0 ≤ B.η; rw [hη]; positivity
          rw [min_eq_right hη0, mul_zero]
      _ ≤ _ := hRHS0
  expose_names
  exact @retainedMin_holds_stage_1 κ c' Cb θ₀ hc' Dst hst Ca hCa hmult C k₀ hatt hccdef hcc1 Cl K₀
    hCl1 hleaf q hq2 hq3 hq hcs hCq0 Mpad hMpad hL₄ hMpad0 hL₄0 hW1 K k N d₀ B hwin p hk3 p1 p2 p3
    p4 p5 p6 p7 p8 p9 p10 p11 p12 p13 p14 p15 x1 x2 x3 x4 x5 hk₀k hK₀k hanc hH1 hHk hDck hLk hS2
    hcol hpairs hη x6 hη₀def hη₀0 hmB hR0 hL0 bf hsubA hne hV

/-- Blueprint `eq:active-final` (prop:normalized, lines 2838-2888) for every admissible class:
`RetainedMin` (`retainedMin_holds`), the restarts at the exceptional roots
(`activeMin_of_retainedMin`) and the two-`U` term (`activeFinal_of_activeMin`). -/
theorem activeFinal_holds (κ : LocalKernelClass) : ActiveFinal κ :=
  activeFinal_of_activeMin (activeMin_of_retainedMin (retainedMin_holds κ))

/-- Blueprint thm:main (lines 2934-2940): the trilinear Hilbert transform principal value exists
pointwise on Schwartz functions, is bounded `L³ × L³ × L³ → L¹` there, and extends uniquely to a
bounded trilinear operator on `L³`. -/
theorem tht_main :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ f₁ f₂ f₃ : SchwartzMap ℝ ℂ,
        (∀ x, Filter.Tendsto (TrilinearHT.truncatedTransform ![⇑f₁, ⇑f₂, ⇑f₃] x)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds (TrilinearHT.T ![⇑f₁, ⇑f₂, ⇑f₃] x))) ∧
        MemLp (TrilinearHT.T ![⇑f₁, ⇑f₂, ⇑f₃]) 1 volume ∧
        ∫⁻ x, ‖TrilinearHT.T ![⇑f₁, ⇑f₂, ⇑f₃] x‖ₑ ≤
          ENNReal.ofReal C * (eLpNorm f₁ 3 volume * eLpNorm f₂ 3 volume * eLpNorm f₃ 3 volume)) ∧
      ∃ T' : Lp ℂ 3 (volume : Measure ℝ) →L[ℂ] Lp ℂ 3 (volume : Measure ℝ) →L[ℂ]
          Lp ℂ 3 (volume : Measure ℝ) →L[ℂ] Lp ℂ 1 (volume : Measure ℝ),
        (∀ f₁ f₂ f₃ : SchwartzMap ℝ ℂ, ⇑(T' (f₁.toLp 3 (volume : Measure ℝ))
          (f₂.toLp 3 (volume : Measure ℝ)) (f₃.toLp 3 (volume : Measure ℝ))) =ᵐ[volume]
            TrilinearHT.T ![⇑f₁, ⇑f₂, ⇑f₃]) ∧
        (∀ x y z, ‖T' x y z‖ ≤ C * ‖x‖ * ‖y‖ * ‖z‖) ∧
        ∀ S : Lp ℂ 3 (volume : Measure ℝ) →L[ℂ] Lp ℂ 3 (volume : Measure ℝ) →L[ℂ]
            Lp ℂ 3 (volume : Measure ℝ) →L[ℂ] Lp ℂ 1 (volume : Measure ℝ),
          (∀ f₁ f₂ f₃ : SchwartzMap ℝ ℂ, ⇑(S (f₁.toLp 3 (volume : Measure ℝ))
            (f₂.toLp 3 (volume : Measure ℝ)) (f₃.toLp 3 (volume : Measure ℝ))) =ᵐ[volume]
              TrilinearHT.T ![⇑f₁, ⇑f₂, ⇑f₃]) → S = T' :=
  tht_main_of_activeFinal activeFinal_holds

open scoped SchwartzMap in
/-- Blueprint thm:main in the form of `TrilinearHT.trilinear_ht_bound`
(`TrilinearHT/Theorems.lean`): the trilinear Hilbert transform `TrilinearHT.T` is bounded
`L³ × L³ × L³ → L¹` on Schwartz functions. -/
theorem trilinear_ht_bound :
    ∃ C : ℝ, ∀ f : Fin 3 → 𝓢(ℝ, ℂ),
      eLpNorm (TrilinearHT.T (fun i ↦ f i)) 1 ≤ (ENNReal.ofReal C) * ∏ i, eLpNorm (f i) 3 := by
  obtain ⟨C, -, hC, -⟩ := tht_main
  refine ⟨C, fun f => ?_⟩
  rw [schwartz_triple_eq_vecCons, eLpNorm_one_eq_lintegral_enorm
    (T_measurable (f 0) (f 1) (f 2)).aestronglyMeasurable, Fin.prod_univ_three]
  exact (hC (f 0) (f 1) (f 2)).2.2

end TrilinearHT.Auto

end
