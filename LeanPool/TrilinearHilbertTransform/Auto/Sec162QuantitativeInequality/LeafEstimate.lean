/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

/- Adapted for Lean Pool from roos-j/lean-trilinearht at
7b4209609e6a7fb9d9935973ee8541495f943660. Imports, names, proof organization and
Mathlib interfaces have been updated; original authorship is retained above. -/

public import LeanPool.TrilinearHilbertTransform.Auto.Sec162QuantitativeInequality.LeafFinal

/-!
# Trilinear Hilbert transform: leaf_estimate
-/

@[expose] public section

section
namespace TrilinearHT.Auto
open MeasureTheory Metric
open scoped FourierTransform ComplexConjugate ENNReal
namespace ActiveSetup.BasicFamilies
variable {κ : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ c₀} (bf : A.BasicFamilies)

open scoped Classical in
private def LeafEstimateHstabStatement : Prop :=
  ∀ (κ : LocalKernelClass)
    (c₀ : ℕ)
    (_ : ℕ)
    (Dm0 : ℕ)
    (_ : ℝ)
    (_ : ℕ)
    (_ : ℕ)
    (_ : ℝ)
    (_ : ℝ)
    (_ : ℝ)
    (_ : ℝ)
    (_ : ℕ)
    (_ : ℕ)
    (_ : ℕ)
    (_ : ℕ)
    (_ : ℕ)
    (_ : ℕ)
    (A : ActiveSetup κ c₀)
    (bf : A.BasicFamilies)
    (p : Fin (3 : ℕ))
    (AD : bf.AttemptData p)
    (d : bf.Vtx)
    (s : ℕ)
    (δ : ℝ)
    (kD : ℝ),
  let fp : bf.FamParams :=
    AD.fp
  let dB : ℕ :=
    A.dBnd
  let Nl : ℝ :=
    AD.n (fp.Lc + (5 : ℕ))
  ∀ (hNl0 : (0 : ℝ) ≤ Nl),
  let Hm : ℝ :=
    max (max A.Hsrc (Real.exp (↑dB : ℝ))) (max ((5832 : ℝ) * max A.H padW ^ (4 : ℕ))
      ((↑dB : ℝ) * (bumpConst * (8 : ℝ) ^ (32 : ℕ) * ((2 : ℝ) / δ))))
  ∀ (S : ModeSchedule)
    (_ : S.dmax = (2 : ℕ) * dB + (2 : ℕ))
    (_ : S.Valid (340 : ℕ) (5 : ℕ) (4 : ℕ) (600 : ℕ) (1 / 1024 : ℝ) (packetW S.dmax S.H))
    (_ : (2 : ℕ) ≤ S.dmax)
    (_ : (2 : ℝ) ≤ S.Dstar)
    (_ : (2 : ℝ) ≤ S.Bstar)
    (_ : (1 : ℕ) ≤ S.Q0)
    (hK1 : (1 : ℕ) ≤ S.K),
  let Lf : SearchLeaf :=
    leafAt A.famFuel fp.Lc (A.basicSlot p) s
  let ks : ℕ :=
    Lf.k
  let S0 : Finset (ℤ × ℤ) :=
    {I ∈ AD.Tc | ¬∃ c ∈ fp.failRoots, dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G
      c.1 c.2}
  let gs : ℤ × ℤ → Finset bf.Grp :=
    fun (I : ℤ × ℤ) => fp.groupsAt I ks
  let gset : Finset bf.Grp :=
    S0.biUnion gs
  ∀ (hlenMc : ∀ (l : Fin (4 : ℕ)), (AD.cat l).length ≤ fp.Mc),
  let mbs : (l : Fin (4 : ℕ)) → bf.MainBudget (AD.cat l) :=
    fun l => MainBudget.ofCounts bf fp.Mc (AD.cat l) (hlenMc l) l (fun e he => AD.hTc
      (AD.hT l e he).1) (fun e he => (AD.hT l e he).2.1) hNl0 (fun I _ => AD.hlab l I _
      le_rfl)
  ∀ (Ms : Fin (4 : ℕ) → bf.Grp → ModeSystem A.G (Fintype.card (bf.Lab ⊕ Fin fp.Mc)))
    (_ : ∀ (l : Fin (4 : ℕ)), ∀ G ∉ gset, (∀ (p : (Ms l G).Key), (Ms l G).dvOf p + (Ms l
      G).zc.dim ≤ (2 : ℕ) * dB + (2 : ℕ)) ∧ (Ms l G).Bσ = (1 : ℝ) ∧ ∀ (V : ℤ × ℤ), (Ms l
      G).alive V = ∅)
    (_ : ∀ (l : Fin (4 : ℕ)), ∀ G ∈ gset, (∀ (q : (Ms l G).Key), (Ms l G).dvOf q + (Ms l
      G).zc.dim ≤ (2 : ℕ) * dB + (2 : ℕ)) ∧ (Ms l G).Λ ≤ S.Dstar ∧ gaugeSqNorm (Ms l
      G).zc.dim (Ms l G).δc ≤ S.Dstar ∧ (2 : ℝ) * gaugeTail (Ms l G).zc.dim (Ms l G).δc
      / (2 : ℝ) ^ fp.Kstar Dm0 dB Hm δ Nl kD δ * S.Dstar ^ (300 : ℕ) ≤ (1 : ℝ) ∧ (∀ (m :
      (Ms l G).Md), S.Dstar⁻¹ ≤ (Ms l G).L.εM m) ∧ (∀ (V : ℤ × ℤ), (↑((Ms l G).alive
      V).card : ℝ) ≤ S.Dstar) ∧ ∀ (V : ℤ × ℤ), (↑(Finset.image (Ms l G).keyOf ((Ms l
      G).alive V)).card : ℝ) ≤ Nl)
    (hA6 : (6 : ℝ) ≤ S.A0),
  let qG : bf.Grp → ℕ :=
    fun (G : bf.Grp) => clearInt (bf.vtag (bf.grpCenter d G)).C
  ∀ (_ : ∀ (G : bf.Grp), (1 : ℕ) ≤ qG G ∧ qG G ≤ S.Q0)
    (_ : (0 : ℝ) < S.Dstar),
  let BN : ℕ :=
    ⌈(8 : ℝ) * A.colBudget + Nl⌉₊
  ∀ (_ : ∀ (l : Fin (4 : ℕ)), fp.bbase (Lf.role l) + fp.P ≤ fp.Hmax)
    (_ : ∀ (l : Fin (4 : ℕ)) (y : ℝ), (Finset.card ({q : ↥gset × (bf.Lab ⊕ Fin fp.Mc) | ∃ I ∈
      A.cells, (∃ (k' : ℕ), fp.Cert k' (↑q.1 : bf.Grp) I) ∧ ∃ (p_1 : Fin fp.P), y ∈
      dyadicGridCell A.G I.1 I.2 ∧ q.2 ∈ mainLabelsM A.G fp.Mc (bf.origCols l) (AD.cat
      l) I (fp.brank (Lf.role l)) (fp.bmask I (↑q.1 : bf.Grp) (Lf.role l) ((↑p_1 : ℕ) +
      (1 : ℕ))) d})) ≤ BN)
    (_ : ∀ (l : Fin (4 : ℕ)) (G : ↥gset), (2 : ℝ) * ((↑S.Q0 : ℝ) * ((3 : ℝ) * ((Ms l (↑G :
      bf.Grp)).Bσ * (Ms l (↑G : bf.Grp)).Bσ) ^ (2 : ℕ))) ^ (2 : ℕ) ≤ (↑⌊S.Dstar⌋₊ : ℝ))
    (c : (l : Fin (4 : ℕ)) → (G : ↥gset) → ℤ → ℤ × ℤ → (Ms l (↑G : bf.Grp)).Md → ℂ),
  let cf : (l : Fin (4 : ℕ)) → (G : bf.Grp) → ℤ → ℤ × ℤ → (Ms l G).Md → ℂ :=
    fun (l : Fin (4 : ℕ)) (G : bf.Grp) => if hG : G ∈ gset then c l ⟨G, hG⟩ else fun _ _
      _ => (0 : ℂ)
  let D₀ : fp.SideInput :=
    { cat := AD.cat, mbs := mbs, Lf := Lf, u := A.uslot p, S := S, hA := hA6,
      SP := S.sideParams (1 / 1024 : ℝ), hK := hK1,
      n := Fintype.card (bf.Lab ⊕ Fin fp.Mc), Ms := Ms, c := cf }
  ∀ (hcat : Fin (4 : ℕ) → List (CatCol bf.Vtx))
    (_ : ∀ (l : Fin (4 : ℕ)), ∀ d ∈ hcat l, d.birth ∈ AD.Tc ∧ d.rank = fp.Lc + (5 : ℕ) ∧ (∃
      (M : fp.MaskName d.birth), fp.maskOf d.birth M d.tag) ∧ ∃ R ∈ residueBox (bf.vtag
      d.tag).dim (9 : ℕ), ∃ (γ : ℝ), d = templateCol (bf.vtag d.tag) l R γ d.birth
      d.rank d.tag)
    (hmbb : ∀ (l : Fin (4 : ℕ)), ∀ e ∈ AD.cat l ++ hcat l, e.birth ∈ A.cells)
    (hmbT : ∀ (l : Fin (4 : ℕ)) (y : ℝ), (8 : ℝ) * A.colBudget + (↑(bf.tmplPath (AD.cat l ++
      hcat l) y) : ℝ) ≤ (8 : ℝ) * A.colBudget + ((1 : ℝ) + (↑AD.Mp : ℝ)) * Nl),
  let mb' : (l : Fin (4 : ℕ)) → bf.MainBudget (AD.cat l ++ hcat l) :=
    fun l =>
        { hb := hmbb l, B := 8 * A.colBudget + (1 + AD.Mp) * Nl, hTp := hmbT l }
  let D : fp.SideInput :=
    D₀.appendCat hcat mb'
  ∀ (_ : ∀ (l : Fin (4 : ℕ)), ∀ e ∈ hcat l, bf.occAvail (↑e.tag.2 : ℤ × ℤ) e.tag.1)
    (_ : ∀ (l : Fin (4 : ℕ)) (G : bf.Grp), (1 : ℝ) ≤ (Ms l G).Bσ),
  ∀ G ∈ gset, (D.withQ0 (qG G)).Stab


open scoped Classical in
private def LeafEstimateConclusion88Statement : Prop :=
  ∀ (κ : LocalKernelClass)
    (c₀ : ℕ)
    (cc : ℕ)
    (Cl : ℕ)
    (A : ActiveSetup κ c₀)
    (bf : A.BasicFamilies)
    (k : ℕ)
    (η₀ : ℝ)
    (E : ℝ)
    (_ : A.SubRootProps η₀ E)
    (q : ℝ)
    (hq2 : (2 : ℝ) < q)
    (hq3 : q < (3 : ℝ))
    (Nd : ℕ)
    (p : Fin (3 : ℕ))
    (AD : bf.AttemptData p)
    (d : bf.Vtx)
    (s : ℕ)
    (δ : ℝ)
    (ρ : ℝ)
    (kD : ℝ)
    (_ : ρ < (1 : ℝ)),
  let fp : bf.FamParams :=
    AD.fp
  let Nl : ℝ :=
    AD.n (fp.Lc + (5 : ℕ))
  ∀ (hNl0 : (0 : ℝ) ≤ Nl)
    (S : ModeSchedule)
    (hK1 : (1 : ℕ) ≤ S.K),
  let Lf : SearchLeaf :=
    leafAt A.famFuel fp.Lc (A.basicSlot p) s
  let ks : ℕ :=
    Lf.k
  let S0 : Finset (ℤ × ℤ) :=
    {I ∈ AD.Tc | ¬∃ c ∈ fp.failRoots, dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G
      c.1 c.2}
  let gs : ℤ × ℤ → Finset bf.Grp :=
    fun (I : ℤ × ℤ) => fp.groupsAt I ks
  let gset : Finset bf.Grp :=
    S0.biUnion gs
  ∀ (hlenMc : ∀ (l : Fin (4 : ℕ)), (AD.cat l).length ≤ fp.Mc),
  let mbs : (l : Fin (4 : ℕ)) → bf.MainBudget (AD.cat l) :=
    fun l => MainBudget.ofCounts bf fp.Mc (AD.cat l) (hlenMc l) l (fun e he => AD.hTc
      (AD.hT l e he).1) (fun e he => (AD.hT l e he).2.1) hNl0 (fun I _ => AD.hlab l I _
      le_rfl)
  ∀ (Ms : Fin (4 : ℕ) → bf.Grp → ModeSystem A.G (Fintype.card (bf.Lab ⊕ Fin fp.Mc)))
    (hA6 : (6 : ℝ) ≤ S.A0),
  let qG : bf.Grp → ℕ :=
    fun (G : bf.Grp) => clearInt (bf.vtag (bf.grpCenter d G)).C
  ∀ (c : (l : Fin (4 : ℕ)) → (G : ↥gset) → ℤ → ℤ × ℤ → (Ms l (↑G : bf.Grp)).Md → ℂ)
    (Cut : Fin (4 : ℕ) → Finset (ℤ × ℤ))
    (_ : ∀ (l : Fin (4 : ℕ)), dyadicRootLength A.G (Cut l) ≤ ρ * dyadicGridLength A.G A.R.1),
  let cf : (l : Fin (4 : ℕ)) → (G : bf.Grp) → ℤ → ℤ × ℤ → (Ms l G).Md → ℂ :=
    fun (l : Fin (4 : ℕ)) (G : bf.Grp) => if hG : G ∈ gset then c l ⟨G, hG⟩ else fun _ _
      _ => (0 : ℂ)
  let D₀ : fp.SideInput :=
    { cat := AD.cat, mbs := mbs, Lf := Lf, u := A.uslot p, S := S, hA := hA6,
      SP := S.sideParams (1 / 1024 : ℝ), hK := hK1,
      n := Fintype.card (bf.Lab ⊕ Fin fp.Mc), Ms := Ms, c := cf }
  ∀ (hcat : Fin (4 : ℕ) → List (CatCol bf.Vtx))
    (hmbb : ∀ (l : Fin (4 : ℕ)), ∀ e ∈ AD.cat l ++ hcat l, e.birth ∈ A.cells)
    (hmbT : ∀ (l : Fin (4 : ℕ)) (y : ℝ), (8 : ℝ) * A.colBudget + (↑(bf.tmplPath (AD.cat l ++
      hcat l) y) : ℝ) ≤ (8 : ℝ) * A.colBudget + ((1 : ℝ) + (↑AD.Mp : ℝ)) * Nl),
  let mb' : (l : Fin (4 : ℕ)) → bf.MainBudget (AD.cat l ++ hcat l) :=
    fun l =>
        { hb := hmbb l, B := 8 * A.colBudget + (1 + AD.Mp) * Nl, hTp := hmbT l }
  let D : fp.SideInput :=
    D₀.appendCat hcat mb'
  ∀ (_ : ∀ (l : Fin (4 : ℕ)), ∀ e ∈ hcat l, fp.hrank ≤ e.rank)
    (_ : ∀ (l : Fin (4 : ℕ)), D₀.Lf.role l ≤ (4 : ℕ)),
  let S1 : Finset (ℤ × ℤ) :=
    {I ∈ S0 | ∀ (j : Fin (4 : ℕ)), ∀ e ∈ Cut j, ¬dyadicGridCell A.G I.1 I.2 ⊆
      dyadicGridCell A.G e.1 e.2}
  ∀ (_ : (0 : ℝ) < dyadicGridLength A.G A.R.1)
    (C : Finset (ℤ × ℤ))
    (C₂ : Finset (ℤ × ℤ)),
  let S₂ : Finset (ℤ × ℤ) :=
    {I ∈ {I ∈ S1 | ¬∃ e ∈ C, dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G e.1 e.2} |
      ¬∃ e ∈ C₂, dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G e.1 e.2}
  ∀ (_ : (0 : ℝ) ≤ A.η)
    (_ : ∑ I ∈ S₂, dyadicGridLength A.G I.1 * min A.η ‖∑ G ∈ gs I, (fp.Λc I : (Fin (4 : ℕ) →
      ↥(ColumnL2 (bf.Lab ⊕ Fin fp.Mc))) → ℂ) fun (l : Fin (4 : ℕ)) => (D.toLeafQ qG).out
      l G I‖ ≤ leafBnd Cl kD fp.P k cc A.η η₀ AD.τ₃ δ (finiteDepthConstant κ q Nd) (nbCM
      κ hq2 hq3 + nbCUM κ hq2 hq3) q (dyadicGridLength A.G A.R.1)),
  ∀ cs ⊆ AD.Tc, (∀ I ∈ cs, ¬∃ c ∈ fp.failRoots, dyadicGridCell A.G I.1 I.2 ⊆
    dyadicGridCell A.G c.1 c.2) → (∀ I ∈ cs, ∀ (i : Fin (6 : ℕ)), ∀ e ∈
    ![maximalDyadicCells A.G C, C₂, {e ∈ Cut (0 : Fin (4 : ℕ)) | dyadicGridCell A.G
    e.1 e.2 ⊆ dyadicGridCell A.G A.R.1 A.R.2}, {e ∈ Cut (1 : Fin (4 : ℕ)) |
    dyadicGridCell A.G e.1 e.2 ⊆ dyadicGridCell A.G A.R.1 A.R.2}, {e ∈ Cut (2 : Fin (4
    : ℕ)) | dyadicGridCell A.G e.1 e.2 ⊆ dyadicGridCell A.G A.R.1 A.R.2}, {e ∈ Cut (3
    : Fin (4 : ℕ)) | dyadicGridCell A.G e.1 e.2 ⊆ dyadicGridCell A.G A.R.1 A.R.2}] i,
    ¬dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G e.1 e.2) → ∑ I ∈ cs,
    dyadicGridLength A.G I.1 * min A.η ‖∑ G ∈ fp.groupsAt I ks, (fp.Λc I : (Fin (4 :
    ℕ) → ↥(ColumnL2 (bf.Lab ⊕ Fin fp.Mc))) → ℂ) fun (l : Fin (4 : ℕ)) => (fp.ballFilt
    l (AD.cat l) I G (Lf.role l) : ↥(ColumnL2 (bf.Lab ⊕ Fin fp.Mc)) → ↥(ColumnL2
    (bf.Lab ⊕ Fin fp.Mc))) (fp.inputL AD.cat I (bf.patIn fp.Mc p I) Lf.layers l)‖ ≤
    leafBnd Cl kD fp.P k cc A.η η₀ AD.τ₃ δ (finiteDepthConstant κ q Nd) (nbCM κ hq2
    hq3 + nbCUM κ hq2 hq3) q (dyadicGridLength A.G A.R.1)


open scoped Classical in
private def LeafEstimateStage8Statement : Prop :=
  ∀ (κ : LocalKernelClass)
    (c₀ : ℕ)
    (cc : ℕ)
    (_ : (1 : ℕ) ≤ cc)
    (Dm0 : ℕ)
    (Msch : ℝ)
    (_ : (0 : ℝ) < Msch)
    (Cg : ℕ)
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
    (eΛ : ℕ)
    (CM1 : ℕ)
    (t3 : ℕ)
    (Cb : ℕ)
    (Cl : ℕ)
    (_ : g = (8192 : ℕ) * (cc + (1 : ℕ)) * ((1024 : ℕ) * (cc + (1 : ℕ)) + cc + (7 : ℕ)) + cc
      ^ (2 : ℕ) + (8 : ℕ) ∧ cT = (10 : ℝ) ^ (22 : ℕ) * ((1 : ℝ) +
      localFormUniformConstant κ) ^ (2 : ℕ) ∧ cL = (159 : ℝ) + (32 : ℝ) * (↑g : ℝ) + (8
      : ℝ) * Real.log cT ∧ cK = ((1 : ℝ) + (7 : ℝ) * (10 : ℝ) ^ (9 : ℕ) + cT) * (cL + (2
      : ℝ)) ∧ cMc = (C4c κ + (4 : ℝ) * C3c κ) * cL ^ (4 : ℕ) * cK ^ (2 : ℕ) ∧ cm =
      (196608 : ℝ) * cT + (83 : ℝ) * ((1 : ℝ) + (81 : ℝ) * localFormUniformConstant κ *
      ((30000 : ℝ) + √cT)) * ((1 : ℝ) + cT) ^ (3 : ℕ) + cMc ∧ ce = (6642 : ℝ) *
      localFormUniformConstant κ * ((60000 : ℝ) + √cT) ^ (3 : ℕ) * (288 : ℝ) + (9 : ℝ) *
      ((16 : ℝ) * fourErrC κ (3 : ℕ) + (648 : ℝ) * threeErrC κ (3 : ℕ) (1 : ℕ) + (324 :
      ℝ) * threeErrC κ (3 : ℕ) (1 : ℕ) * √cT) ∧ ce2 = K1c * ((2 : ℝ) * fourKC κ (3 : ℕ)
      * (12 : ℝ) ^ (4 : ℕ)) + (4 : ℝ) * (K1c * ((8 : ℝ) * entryCU κ (3 : ℕ) (1 : ℕ) * (2
      : ℝ) ^ ((1 : ℕ) + (4 : ℕ)) * (12 : ℝ) ^ (3 : ℕ))) * (501 : ℝ) ∧ cQ = (65536 : ℝ) *
      ((8 : ℝ) + (80 : ℝ) * (9 : ℝ) ^ cc * (↑cc : ℝ)) * ((80 : ℝ) * (9 : ℝ) ^ cc * (↑cc
      : ℝ)) * ((4 : ℝ) * (↑cc : ℝ) ^ (2 : ℕ)) * ((17 : ℝ) * (10 : ℝ) ^ (7 : ℕ)) ∧ CΛ =
      (2 : ℕ) * Cg + (12 : ℕ) ∧ eΛ = Cg + (3 : ℕ) * cc ∧ CM1 = (⌈Msch⌉₊ + (1 : ℕ)) * CΛ
      ^ (16 : ℕ) ∧ t3 = (3 : ℕ) ^ cc ∧ Cb = CM1 + (501 : ℕ) * Cg + t3 + (2 : ℕ) * cc +
      (20 : ℕ) + (16 : ℕ) * eΛ ∧ Cl = ⌈cm * (↑Cb : ℝ) ^ (59 : ℕ) + ce * (↑Cb : ℝ) ^ (18
      : ℕ) + ce2 + (3 : ℝ) * (10 : ℝ) ^ (11 : ℕ) * cQ⌉₊ + (59 : ℕ) * Cb + (4 : ℕ) * g +
      (8 : ℕ) * cc + (8 : ℕ))
    (A : ActiveSetup κ c₀)
    (bf : A.BasicFamilies)
    (k : ℕ)
    (η₀ : ℝ)
    (E : ℝ)
    (_ : A.SubRootProps η₀ E)
    (_ : A.S = (2 : ℝ))
    (_ : A.η = (4 : ℝ) * η₀)
    (_ : (0 : ℝ) < η₀)
    (q : ℝ)
    (hq2 : (2 : ℝ) < q)
    (hq3 : q < (3 : ℝ))
    (Nd : ℕ)
    (p : Fin (3 : ℕ))
    (AD : bf.AttemptData p)
    (d : bf.Vtx)
    (s : ℕ)
    (δ : ℝ)
    (ρ : ℝ)
    (kD : ℝ)
    (_ : (0 : ℝ) < δ)
    (_ : δ ≤ (1 / 8 : ℝ))
    (_ : (0 : ℝ) < ρ)
    (_ : ρ < (1 : ℝ))
    (_ : Real.log ((2 : ℝ) * A.colBudget) ≤ (↑k : ℝ) ^ cc)
    (_ : (↑((2 : ℕ) * A.famFuel + (2 : ℕ)) : ℝ) ≤ (↑cc : ℝ) * (Real.log (↑k : ℝ) + (1 : ℝ))),
  let fp : bf.FamParams :=
    AD.fp
  let dB : ℕ :=
    A.dBnd
  let Nl : ℝ :=
    AD.n (fp.Lc + (5 : ℕ))
  ∀ (_ : Real.log ((2 : ℝ) * ((8 : ℝ) * A.colBudget + ((1 : ℝ) + (↑AD.Mp : ℝ)) * Nl)) ≤ (↑k :
      ℝ) ^ cc)
    (_ : (2 : ℝ) ≤ A.colBudget)
    (hNl0 : (0 : ℝ) ≤ Nl),
  let Hm : ℝ :=
    max (max A.Hsrc (Real.exp (↑dB : ℝ))) (max ((5832 : ℝ) * max A.H padW ^ (4 : ℕ))
      ((↑dB : ℝ) * (bumpConst * (8 : ℝ) ^ (32 : ℕ) * ((2 : ℝ) / δ))))
  ∀ (S : ModeSchedule)
    (_ : S.dmax = (2 : ℕ) * dB + (2 : ℕ))
    (_ : S.Dm = max (2 : ℝ) Nl)
    (_ : S.Valid (340 : ℕ) (5 : ℕ) (4 : ℕ) (600 : ℕ) (1 / 1024 : ℝ) (packetW S.dmax S.H))
    (_ : (2 : ℕ) ≤ S.dmax)
    (_ : (2 : ℝ) ≤ S.Dstar)
    (_ : (2 : ℝ) ≤ S.Bstar)
    (_ : (1 : ℕ) ≤ S.Q0)
    (hK1 : (1 : ℕ) ≤ S.K),
  let Lf : SearchLeaf :=
    leafAt A.famFuel fp.Lc (A.basicSlot p) s
  let ks : ℕ :=
    Lf.k
  let S0 : Finset (ℤ × ℤ) :=
    {I ∈ AD.Tc | ¬∃ c ∈ fp.failRoots, dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G
      c.1 c.2}
  let gs : ℤ × ℤ → Finset bf.Grp :=
    fun (I : ℤ × ℤ) => fp.groupsAt I ks
  let gset : Finset bf.Grp :=
    S0.biUnion gs
  ∀ (hlenMc : ∀ (l : Fin (4 : ℕ)), (AD.cat l).length ≤ fp.Mc),
  let mbs : (l : Fin (4 : ℕ)) → bf.MainBudget (AD.cat l) :=
    fun l => MainBudget.ofCounts bf fp.Mc (AD.cat l) (hlenMc l) l (fun e he => AD.hTc
      (AD.hT l e he).1) (fun e he => (AD.hT l e he).2.1) hNl0 (fun I _ => AD.hlab l I _
      le_rfl)
  ∀ (Ms : Fin (4 : ℕ) → bf.Grp → ModeSystem A.G (Fintype.card (bf.Lab ⊕ Fin fp.Mc)))
    (L : (l : Fin (4 : ℕ)) → (G : bf.Grp) → LiftData (bf.Lab ⊕ Fin fp.Mc) (Ms l G).Md)
    (hA6 : (6 : ℝ) ≤ S.A0),
  let qG : bf.Grp → ℕ :=
    fun (G : bf.Grp) => clearInt (bf.vtag (bf.grpCenter d G)).C
  ∀ (Vl0 : ℝ)
    (U : ℝ)
    (MV : ℝ)
    (_ : MV = (↑AD.Mp : ℝ) * (↑A.famVtxBound : ℝ))
    (ε : ℝ)
    (_ : ε = (U ^ (3 : ℕ) * S.Dstar ^ (5 : ℕ) * Real.exp (↑k : ℝ) * ((1 : ℝ) + MV))⁻¹),
  let Ts : Finset (ℕ × ℕ) :=
    Finset.range (Nat.log (2 : ℕ) ⌊S.Dstar⌋₊ + (1 : ℕ)) ×ˢ Finset.range (Nat.log (2 : ℕ)
      ⌊S.Dstar⌋₊ + (1 : ℕ))
  ∀ (_ : (4 : ℝ) ≤ Nl)
    (c : (l : Fin (4 : ℕ)) → (G : ↥gset) → ℤ → ℤ × ℤ → (Ms l (↑G : bf.Grp)).Md → ℂ)
    (Cut : Fin (4 : ℕ) → Finset (ℤ × ℤ))
    (_ : ∀ (l : Fin (4 : ℕ)), dyadicRootLength A.G (Cut l) ≤ ρ * dyadicGridLength A.G A.R.1),
  let cf : (l : Fin (4 : ℕ)) → (G : bf.Grp) → ℤ → ℤ × ℤ → (Ms l G).Md → ℂ :=
    fun (l : Fin (4 : ℕ)) (G : bf.Grp) => if hG : G ∈ gset then c l ⟨G, hG⟩ else fun _ _
      _ => (0 : ℂ)
  let D₀ : fp.SideInput :=
    { cat := AD.cat, mbs := mbs, Lf := Lf, u := A.uslot p, S := S, hA := hA6,
      SP := S.sideParams (1 / 1024 : ℝ), hK := hK1,
      n := Fintype.card (bf.Lab ⊕ Fin fp.Mc), Ms := Ms, c := cf }
  ∀ (hcat : Fin (4 : ℕ) → List (CatCol bf.Vtx))
    (hmbb : ∀ (l : Fin (4 : ℕ)), ∀ e ∈ AD.cat l ++ hcat l, e.birth ∈ A.cells)
    (hmbT : ∀ (l : Fin (4 : ℕ)) (y : ℝ), (8 : ℝ) * A.colBudget + (↑(bf.tmplPath (AD.cat l ++
      hcat l) y) : ℝ) ≤ (8 : ℝ) * A.colBudget + ((1 : ℝ) + (↑AD.Mp : ℝ)) * Nl),
  let mb' : (l : Fin (4 : ℕ)) → bf.MainBudget (AD.cat l ++ hcat l) :=
    fun l =>
        { hb := hmbb l, B := 8 * A.colBudget + (1 + AD.Mp) * Nl, hTp := hmbT l }
  let D : fp.SideInput :=
    D₀.appendCat hcat mb'
  ∀ (_ : ∀ (l : Fin (4 : ℕ)), ∀ e ∈ hcat l, fp.hrank ≤ e.rank)
    (_ : ∀ (l : Fin (4 : ℕ)), D₀.Lf.role l ≤ (4 : ℕ)),
  let S1 : Finset (ℤ × ℤ) :=
    {I ∈ S0 | ∀ (j : Fin (4 : ℕ)), ∀ e ∈ Cut j, ¬dyadicGridCell A.G I.1 I.2 ⊆
      dyadicGridCell A.G e.1 e.2}
  ∀ (_ : S1 ⊆ A.cells),
  let Nb : ℕ :=
    Nat.log (2 : ℕ) S.K + (1 : ℕ)
  ∀ (_ : Nb = Nat.log (2 : ℕ) S.K + (1 : ℕ))
    (_ : (0 : ℝ) < dyadicGridLength A.G A.R.1)
    (_ : (0 : ℝ) ≤ Vl0),
  let Os : Finset (Fin (4 : ℕ) × Fin (4 : ℕ) × ℕ × ℕ × ℕ × ℕ) :=
    FamParams.SideLeafM.nOs ((2 : ℕ) ^ A.famFuel) ((2 : ℕ) * A.famFuel + (2 : ℕ))
  ∀ (_ : Os = FamParams.SideLeafM.nOs ((2 : ℕ) ^ A.famFuel) ((2 : ℕ) * A.famFuel + (2 : ℕ))),
  let Cjg : ℝ :=
    ((↑((2 : ℕ) * A.famFuel + (2 : ℕ)) : ℝ) + (1 : ℝ)) ^ (2 : ℕ) * Real.exp ((2 : ℝ) *
      ((1024 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) * ((1024 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) + (↑cc :
      ℝ) + (7 : ℝ)) * ((1 : ℝ) + Real.log ((2 : ℝ) * (↑k : ℝ))) ^ (2 : ℕ)))
  ∀ (_ : Cjg = ((↑((2 : ℕ) * A.famFuel + (2 : ℕ)) : ℝ) + (1 : ℝ)) ^ (2 : ℕ) * Real.exp ((2 :
      ℝ) * ((1024 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) * ((1024 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) +
      (↑cc : ℝ) + (7 : ℝ)) * ((1 : ℝ) + Real.log ((2 : ℝ) * (↑k : ℝ))) ^ (2 : ℕ)))),
  let Γa : Fin (4 : ℕ) → ℝ :=
    fun (_ : Fin (4 : ℕ)) => (↑Os.card : ℝ) * ((↑Nb : ℝ) * ((2 : ℝ) * FamParams.capV A
      cc (↑k : ℝ) + (16 : ℝ) * (Cjg * FamParams.SideInput.sideB0 A cc (↑k : ℝ) Vl0) +
      (16 : ℝ) * ((↑Nb : ℝ) * (Cjg * ((↑Nb : ℝ) * FamParams.capV A cc (↑k : ℝ))))) +
      FamParams.SideInput.sideB0 A cc (↑k : ℝ) Vl0) / dyadicGridLength A.G A.R.1
  ∀ (_ : Γa = fun (_ : Fin (4 : ℕ)) => (↑Os.card : ℝ) * ((↑Nb : ℝ) * ((2 : ℝ) *
      FamParams.capV A cc (↑k : ℝ) + (16 : ℝ) * (Cjg * FamParams.SideInput.sideB0 A cc
      (↑k : ℝ) Vl0) + (16 : ℝ) * ((↑Nb : ℝ) * (Cjg * ((↑Nb : ℝ) * FamParams.capV A cc
      (↑k : ℝ))))) + FamParams.SideInput.sideB0 A cc (↑k : ℝ) Vl0) / dyadicGridLength
      A.G A.R.1),
  let Γb : Fin (4 : ℕ) → ℝ :=
    fun (_ : Fin (4 : ℕ)) => (↑Os.card : ℝ) * ((↑Nb : ℝ) * FamParams.capV A cc (↑k : ℝ)
      + FamParams.SideInput.sideB0 A cc (↑k : ℝ) Vl0) / dyadicGridLength A.G A.R.1
  ∀ (_ : Γb = fun (_ : Fin (4 : ℕ)) => (↑Os.card : ℝ) * ((↑Nb : ℝ) * FamParams.capV A cc (↑k
      : ℝ) + FamParams.SideInput.sideB0 A cc (↑k : ℝ) Vl0) / dyadicGridLength A.G A.R.1),
  let ΓU : ℝ :=
    (↑Os.card : ℝ) * ((2 : ℝ) * ((4 : ℝ) * E * dyadicGridLength A.G A.R.1)) /
      dyadicGridLength A.G A.R.1
  ∀ (_ : ΓU = (↑Os.card : ℝ) * ((2 : ℝ) * ((4 : ℝ) * E * dyadicGridLength A.G A.R.1)) /
      dyadicGridLength A.G A.R.1)
    (Ee : ℝ)
    (_ : ∑ I ∈ S1, ∑ G ∈ gs I, ∑ l : Fin (4 : ℕ), ‖(D₀.withQ0 (qG G)).errAt L l G I‖ ^ (2 :
      ℕ) ≤ Ee)
    (_ : Ee ≤ ((8 : ℝ) * (↑dB : ℝ) * δ + (2 : ℝ) * δ ^ (2 : ℕ)) * ((4 : ℝ) * Nl * A.colBudget
      ^ (2 : ℕ) * (1 : ℝ)) * (↑((4 : ℕ) * (AD.Mp * A.famVtxBound)) : ℝ) *
      dyadicGridLength A.G A.R.1)
    (_ : (1 : ℕ) ≤ dB),
  let Gq : ℝ :=
    Real.exp (((6144 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) * ((1024 : ℝ) * ((↑cc : ℝ) + (1 : ℝ))
      + (↑cc : ℝ) + (7 : ℝ)) + (4 : ℝ)) * ((1 : ℝ) + Real.log ((2 : ℝ) * (↑k : ℝ))) ^ (2
      : ℕ))
  ∀ (_ : Vl0 = (24 : ℝ) * ((↑⌊(180 : ℝ) * (↑S.dmax : ℝ) * Real.log ((2 : ℝ) * S.Dm) / (1 /
      1024 : ℝ)⌋₊ : ℝ) + (1 : ℝ)) * (Gq + (2 : ℝ) * (1 : ℝ) / S.Dstar ^ (394 : ℕ))),
  let Mt : ℝ :=
    (24 : ℝ) * ((2 : ℝ) * Gq + (2 : ℝ) * (↑S.K : ℝ) * Vl0) * (↑(Finset.range (S.Jstar +
      (1 : ℕ)) ×ˢ Ts ×ˢ dyThr ε U S.Dstar).card : ℝ) / ρ
  ∀ (_ : Mt = (24 : ℝ) * ((2 : ℝ) * Gq + (2 : ℝ) * (↑S.K : ℝ) * Vl0) * (↑(Finset.range
      (S.Jstar + (1 : ℕ)) ×ˢ Ts ×ˢ dyThr ε U S.Dstar).card : ℝ) / ρ),
  let Iw : ℕ :=
    ⌊Real.logb (2 : ℝ) (S.Dstar ^ (250 : ℕ))⌋₊
  ∀ (C : Finset (ℤ × ℤ))
    (C₂ : Finset (ℤ × ℤ))
    (_ : C ⊆ A.cells)
    (_ : dyadicRootLength A.G (maximalDyadicCells A.G C) ≤ (2 : ℝ) * ρ * dyadicGridLength A.G
      A.R.1)
    (_ : C₂ ⊆ S1)
    (_ : dyadicRootLength A.G C₂ ≤ ρ * dyadicGridLength A.G A.R.1)
    (_ : (↑dB : ℝ) ≤ (↑k : ℝ) ^ cc)
    (_ : E ≤ (↑k : ℝ) ^ cc)
    (_ : ρ⁻¹ ≤ (↑k : ℝ) ^ cc)
    (_ : (↑k : ℝ) ^ cc ≤ kD)
    (_ : (2 : ℝ) ≤ (↑k : ℝ))
    (u : ℝ)
    (_ : u = kD * (↑fp.P : ℝ))
    (_ : (↑A.famVtxBound : ℝ) ≤ (8 : ℝ) * A.colBudget + (1 : ℝ))
    (_ : Real.log S.Dstar ≤ (↑Cg : ℝ) * u ^ Cg),
  let Λ : ℝ :=
    (↑((2 : ℕ) * dB + (2 : ℕ)) : ℝ) + Real.log (fp.modeStarG Dm0 dB Hm δ Nl kD δ) +
      Real.log (fp.Bst Dm0 dB Hm δ Nl kD δ) + Real.log (max (2 : ℝ) Nl) + Real.log
      (↑(fp.Q0bd dB) : ℝ) + (1 : ℝ)
  ∀ (_ : (↑S.K : ℝ) ≤ Msch * Λ ^ (16 : ℕ))
    (_ : Real.log S.H ≤ Msch * Λ ^ (12 : ℕ))
    (_ : (0 : ℝ) ≤ Λ)
    (_ : Λ ≤ (↑CΛ : ℝ) * u ^ eΛ)
    (_ : (0 : ℝ) ≤ E)
    (_ : ∀ (l : Fin (4 : ℕ)), (0 : ℝ) ≤ (fun (_ : Fin (4 : ℕ)) => Vl0) l ∧ (fun (_ : Fin (4 :
      ℕ)) => Vl0) l ≤ Vl0),
  let TT : ℝ :=
    TsideF A fp.P S.K (A.uslot p) ((2 : ℕ) ^ A.famFuel) ((2 : ℕ) * A.famFuel + (2 : ℕ))
      (1 : ℝ) E cc (↑k : ℝ) (fun (_ : Fin (4 : ℕ)) => Vl0) ρ
  ∀ (_ : U = max ((2 : ℝ) * (A.colBudget + (2 : ℝ)) * S.Dstar ^ (2 : ℕ)) √TT)
    (_ : (0 : ℝ) ≤ TT),
  let T2v : ℝ :=
    D.T2 cc (↑k : ℝ) (fun (_ : Fin (4 : ℕ)) => Vl0) ρ
  let S₂ : Finset (ℤ × ℤ) :=
    {I ∈ {I ∈ S1 | ¬∃ e ∈ C, dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G e.1 e.2} |
      ¬∃ e ∈ C₂, dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G e.1 e.2}
  ∀ (_ : ∑ I ∈ S₂, dyadicGridLength A.G I.1 * min A.η ‖∑ G ∈ gs I, (fp.Λc I : (Fin (4 : ℕ) →
      ↥(ColumnL2 (bf.Lab ⊕ Fin fp.Mc))) → ℂ) fun (l : Fin (4 : ℕ)) => (D.toLeafQ qG).out
      l G I‖ ≤ (6 : ℝ) * (256 : ℝ) * ((2 : ℝ) ^ A.famFuel) ^ (2 : ℕ) * ((2 : ℝ) * η₀ +
      fp.farC A.famFuel AD.τ₃ (2 : ℝ)) * D.Tside qG ((2 : ℕ) ^ A.famFuel) ((2 : ℕ) *
      A.famFuel + (2 : ℕ)) (1 : ℝ) E cc (↑k : ℝ) (fun (_ : Fin (4 : ℕ)) => Vl0) ρ *
      dyadicGridLength A.G A.R.1 + (6 : ℝ) * ∑ a : Fin (4 : ℕ), ∑ b : Fin (4 : ℕ), ∑ e :
      Fin (4 : ℕ), (D.toLeafQ qG).nearBnd hq2 hq3 Nd Nb ((2 : ℕ) ^ A.famFuel) ((2 : ℕ) *
      A.famFuel + (2 : ℕ)) (↑AD.Mp : ℝ) ((2 : ℝ) * √(1 : ℝ)) (ρ / (64 : ℝ)) Γa Γb ΓU a b
      e + A.η ^ ((1 : ℝ) - ((1 : ℝ) - (1 / 1200 : ℝ))) * (D.Tside qG ((2 : ℕ) ^
      A.famFuel) ((2 : ℕ) * A.famFuel + (2 : ℕ)) (1 : ℝ) E cc (↑k : ℝ) (fun (_ : Fin (4
      : ℕ)) => Vl0) ρ ^ (((1 : ℝ) - (1 / 1200 : ℝ)) / (2 : ℝ)) * D.Tside qG ((2 : ℕ) ^
      A.famFuel) ((2 : ℕ) * A.famFuel + (2 : ℕ)) (1 : ℝ) E cc (↑k : ℝ) (fun (_ : Fin (4
      : ℕ)) => Vl0) ρ ^ (((1 : ℝ) - (1 / 1200 : ℝ)) / (2 : ℝ)) * D.Tside qG ((2 : ℕ) ^
      A.famFuel) ((2 : ℕ) * A.famFuel + (2 : ℕ)) (1 : ℝ) E cc (↑k : ℝ) (fun (_ : Fin (4
      : ℕ)) => Vl0) ρ ^ (((1 : ℝ) - (1 / 1200 : ℝ)) / (2 : ℝ)) * dyadicGridLength A.G
      A.R.1) + (82 : ℝ) * ((81 : ℝ) * (localFormUniformConstant κ * (coreBd (max ((2 :
      ℝ) * √(1 : ℝ)) A.S) T2v + errBd (max ((2 : ℝ) * √(1 : ℝ)) A.S) T2v + √(D.Tside qG
      ((2 : ℕ) ^ A.famFuel) ((2 : ℕ) * A.famFuel + (2 : ℕ)) (1 : ℝ) E cc (↑k : ℝ) (fun
      (_ : Fin (4 : ℕ)) => Vl0) ρ)) ^ (3 : ℕ)) * (√((4 : ℝ) * ((↑(AD.Mp * A.famVtxBound)
      : ℝ) * dyadicGridLength A.G A.R.1)) * √Ee)) + (82 : ℝ) * (A.η ^ ((1 : ℝ) - ((1 :
      ℝ) - (1 / 1200 : ℝ))) * ((81 : ℝ) * localFormUniformConstant κ * max (coreBd (max
      ((2 : ℝ) * √(1 : ℝ)) A.S) T2v) √(D.Tside qG ((2 : ℕ) ^ A.famFuel) ((2 : ℕ) *
      A.famFuel + (2 : ℕ)) (1 : ℝ) E cc (↑k : ℝ) (fun (_ : Fin (4 : ℕ)) => Vl0) ρ)) ^
      ((1 : ℝ) - (1 / 1200 : ℝ)) * (D.Tside qG ((2 : ℕ) ^ A.famFuel) ((2 : ℕ) *
      A.famFuel + (2 : ℕ)) (1 : ℝ) E cc (↑k : ℝ) (fun (_ : Fin (4 : ℕ)) => Vl0) ρ ^ (((1
      : ℝ) - (1 / 1200 : ℝ)) / (2 : ℝ)) * D.Tside qG ((2 : ℕ) ^ A.famFuel) ((2 : ℕ) *
      A.famFuel + (2 : ℕ)) (1 : ℝ) E cc (↑k : ℝ) (fun (_ : Fin (4 : ℕ)) => Vl0) ρ ^ (((1
      : ℝ) - (1 / 1200 : ℝ)) / (2 : ℝ)) * D.Tside qG ((2 : ℕ) ^ A.famFuel) ((2 : ℕ) *
      A.famFuel + (2 : ℕ)) (1 : ℝ) E cc (↑k : ℝ) (fun (_ : Fin (4 : ℕ)) => Vl0) ρ ^ (((1
      : ℝ) - (1 / 1200 : ℝ)) / (2 : ℝ)) * dyadicGridLength A.G A.R.1)) + (A.η ^ (1 /
      1200 : ℝ) * (dyadicGridLength A.G A.R.1 * (D.coreM4 (3 : ℕ) U ε (max (max (1 : ℝ)
      Mt) (D.Tside qG ((2 : ℕ) ^ A.famFuel) ((2 : ℕ) * A.famFuel + (2 : ℕ)) (1 : ℝ) E cc
      (↑k : ℝ) (fun (_ : Fin (4 : ℕ)) => Vl0) ρ)) + ∑ l : Fin (4 : ℕ), D.coreM3 (3 : ℕ)
      (1 : ℕ) Iw U ε (max (max (1 : ℝ) Mt) (D.Tside qG ((2 : ℕ) ^ A.famFuel) ((2 : ℕ) *
      A.famFuel + (2 : ℕ)) (1 : ℝ) E cc (↑k : ℝ) (fun (_ : Fin (4 : ℕ)) => Vl0) ρ)) l))
      + ∑ I ∈ S₂, dyadicGridLength A.G I.1 * D.coreE qG gs (3 : ℕ) (1 : ℕ) Iw U ε I))
    (_ : Real.exp kD ≤ S.Dstar),
  let ι : ℝ :=
    (S.Dstar ^ (100 : ℕ))⁻¹ * S.Dstar ^ (10 : ℕ)
  let Qe : ℝ :=
    (16 : ℝ) * fourErrC κ (3 : ℕ) * ι + K1c * ((2 : ℝ) * fourKC κ (3 : ℕ) * (12 : ℝ) ^
      (4 : ℕ) * ε * U ^ (3 : ℕ) * S.Dstar ^ (4 : ℕ)) + (4 : ℝ) * ((81 : ℝ) * threeErrC κ
      (3 : ℕ) (1 : ℕ) * ι * U + K1c * ((8 : ℝ) * entryCU κ (3 : ℕ) (1 : ℕ) * (2 : ℝ) ^
      ((1 : ℕ) + (4 : ℕ)) * (12 : ℝ) ^ (3 : ℕ) * ε * U ^ (3 : ℕ) * (S.Dstar ^ (3 : ℕ) *
      ((↑Iw : ℝ) + (1 : ℝ)))))
  ∀ (_ : ∑ I ∈ S₂, dyadicGridLength A.G I.1 * D.coreE qG gs (3 : ℕ) (1 : ℕ) Iw U ε I ≤ Qe *
      ((↑(AD.Mp * A.famVtxBound) : ℝ) * dyadicGridLength A.G A.R.1)),
  ∃ (F : Fin (6 : ℕ) → Finset (ℤ × ℤ)), (∀ (i : Fin (6 : ℕ)), ∀ c ∈ F i,
    dyadicGridCell A.G c.1 c.2 ⊆ dyadicGridCell A.G A.R.1 A.R.2) ∧ (∀ (i : Fin (6 :
    ℕ)), dyadicRootLength A.G (F i) ≤ (2 : ℝ) * ρ * dyadicGridLength A.G A.R.1) ∧ ∀ cs
    ⊆ AD.Tc, (∀ I ∈ cs, ¬∃ c ∈ fp.failRoots, dyadicGridCell A.G I.1 I.2 ⊆
    dyadicGridCell A.G c.1 c.2) → (∀ I ∈ cs, ∀ (i : Fin (6 : ℕ)), ∀ e ∈ F i,
    ¬dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G e.1 e.2) → ∑ I ∈ cs,
    dyadicGridLength A.G I.1 * min A.η ‖∑ G ∈ fp.groupsAt I ks, (fp.Λc I : (Fin (4 :
    ℕ) → ↥(ColumnL2 (bf.Lab ⊕ Fin fp.Mc))) → ℂ) fun (l : Fin (4 : ℕ)) => (fp.ballFilt
    l (AD.cat l) I G (Lf.role l) : ↥(ColumnL2 (bf.Lab ⊕ Fin fp.Mc)) → ↥(ColumnL2
    (bf.Lab ⊕ Fin fp.Mc))) (fp.inputL AD.cat I (bf.patIn fp.Mc p I) Lf.layers l)‖ ≤
    leafBnd Cl kD fp.P k cc A.η η₀ AD.τ₃ δ (finiteDepthConstant κ q Nd) (nbCM κ hq2
    hq3 + nbCUM κ hq2 hq3) q (dyadicGridLength A.G A.R.1)


open scoped Classical in
private def LeafEstimateStage7Statement : Prop :=
  ∀ (κ : LocalKernelClass)
    (c₀ : ℕ)
    (cc : ℕ)
    (_ : (1 : ℕ) ≤ cc)
    (Dm0 : ℕ)
    (Msch : ℝ)
    (_ : (0 : ℝ) < Msch)
    (Cg : ℕ)
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
    (eΛ : ℕ)
    (CM1 : ℕ)
    (t3 : ℕ)
    (Cb : ℕ)
    (Cl : ℕ)
    (_ : g = (8192 : ℕ) * (cc + (1 : ℕ)) * ((1024 : ℕ) * (cc + (1 : ℕ)) + cc + (7 : ℕ)) + cc
      ^ (2 : ℕ) + (8 : ℕ) ∧ cT = (10 : ℝ) ^ (22 : ℕ) * ((1 : ℝ) +
      localFormUniformConstant κ) ^ (2 : ℕ) ∧ cL = (159 : ℝ) + (32 : ℝ) * (↑g : ℝ) + (8
      : ℝ) * Real.log cT ∧ cK = ((1 : ℝ) + (7 : ℝ) * (10 : ℝ) ^ (9 : ℕ) + cT) * (cL + (2
      : ℝ)) ∧ cMc = (C4c κ + (4 : ℝ) * C3c κ) * cL ^ (4 : ℕ) * cK ^ (2 : ℕ) ∧ cm =
      (196608 : ℝ) * cT + (83 : ℝ) * ((1 : ℝ) + (81 : ℝ) * localFormUniformConstant κ *
      ((30000 : ℝ) + √cT)) * ((1 : ℝ) + cT) ^ (3 : ℕ) + cMc ∧ ce = (6642 : ℝ) *
      localFormUniformConstant κ * ((60000 : ℝ) + √cT) ^ (3 : ℕ) * (288 : ℝ) + (9 : ℝ) *
      ((16 : ℝ) * fourErrC κ (3 : ℕ) + (648 : ℝ) * threeErrC κ (3 : ℕ) (1 : ℕ) + (324 :
      ℝ) * threeErrC κ (3 : ℕ) (1 : ℕ) * √cT) ∧ ce2 = K1c * ((2 : ℝ) * fourKC κ (3 : ℕ)
      * (12 : ℝ) ^ (4 : ℕ)) + (4 : ℝ) * (K1c * ((8 : ℝ) * entryCU κ (3 : ℕ) (1 : ℕ) * (2
      : ℝ) ^ ((1 : ℕ) + (4 : ℕ)) * (12 : ℝ) ^ (3 : ℕ))) * (501 : ℝ) ∧ cQ = (65536 : ℝ) *
      ((8 : ℝ) + (80 : ℝ) * (9 : ℝ) ^ cc * (↑cc : ℝ)) * ((80 : ℝ) * (9 : ℝ) ^ cc * (↑cc
      : ℝ)) * ((4 : ℝ) * (↑cc : ℝ) ^ (2 : ℕ)) * ((17 : ℝ) * (10 : ℝ) ^ (7 : ℕ)) ∧ CΛ =
      (2 : ℕ) * Cg + (12 : ℕ) ∧ eΛ = Cg + (3 : ℕ) * cc ∧ CM1 = (⌈Msch⌉₊ + (1 : ℕ)) * CΛ
      ^ (16 : ℕ) ∧ t3 = (3 : ℕ) ^ cc ∧ Cb = CM1 + (501 : ℕ) * Cg + t3 + (2 : ℕ) * cc +
      (20 : ℕ) + (16 : ℕ) * eΛ ∧ Cl = ⌈cm * (↑Cb : ℝ) ^ (59 : ℕ) + ce * (↑Cb : ℝ) ^ (18
      : ℕ) + ce2 + (3 : ℝ) * (10 : ℝ) ^ (11 : ℕ) * cQ⌉₊ + (59 : ℕ) * Cb + (4 : ℕ) * g +
      (8 : ℕ) * cc + (8 : ℕ))
    (A : ActiveSetup κ c₀)
    (bf : A.BasicFamilies)
    (k : ℕ)
    (η₀ : ℝ)
    (E : ℝ)
    (_ : A.SubRootProps η₀ E)
    (_ : A.S = (2 : ℝ))
    (_ : A.η = (4 : ℝ) * η₀)
    (_ : (0 : ℝ) < η₀)
    (_ : A.cells.Nonempty)
    (q : ℝ)
    (hq2 : (2 : ℝ) < q)
    (hq3 : q < (3 : ℝ))
    (Nd : ℕ)
    (p : Fin (3 : ℕ))
    (AD : bf.AttemptData p)
    (d : bf.Vtx)
    (s : ℕ)
    (δ : ℝ)
    (ρ : ℝ)
    (kD : ℝ)
    (_ : (0 : ℝ) < δ)
    (_ : δ ≤ (1 / 8 : ℝ))
    (_ : (0 : ℝ) < ρ)
    (_ : ρ < (1 : ℝ))
    (_ : Real.log ((2 : ℝ) * A.colBudget) ≤ (↑k : ℝ) ^ cc)
    (_ : (↑((2 : ℕ) * A.famFuel + (2 : ℕ)) : ℝ) ≤ (↑cc : ℝ) * (Real.log (↑k : ℝ) + (1 : ℝ)))
    (_ : (1 : ℝ) ≤ (↑k : ℝ)),
  let fp : bf.FamParams :=
    AD.fp
  let dB : ℕ :=
    A.dBnd
  let Nl : ℝ :=
    AD.n (fp.Lc + (5 : ℕ))
  ∀ (_ : Real.log ((2 : ℝ) * ((8 : ℝ) * A.colBudget + ((1 : ℝ) + (↑AD.Mp : ℝ)) * Nl)) ≤ (↑k :
      ℝ) ^ cc)
    (_ : (2 : ℝ) ≤ A.colBudget)
    (hNl0 : (0 : ℝ) ≤ Nl),
  let Hm : ℝ :=
    max (max A.Hsrc (Real.exp (↑dB : ℝ))) (max ((5832 : ℝ) * max A.H padW ^ (4 : ℕ))
      ((↑dB : ℝ) * (bumpConst * (8 : ℝ) ^ (32 : ℕ) * ((2 : ℝ) / δ))))
  ∀ (_ : (1 : ℝ) ≤ Hm)
    (S : ModeSchedule)
    (_ : S.dmax = (2 : ℕ) * dB + (2 : ℕ))
    (_ : S.Dm = max (2 : ℝ) Nl)
    (_ : S.Valid (340 : ℕ) (5 : ℕ) (4 : ℕ) (600 : ℕ) (1 / 1024 : ℝ) (packetW S.dmax S.H))
    (_ : (2 : ℕ) ≤ S.dmax)
    (_ : (2 : ℝ) ≤ S.Dstar)
    (_ : (2 : ℝ) ≤ S.Bstar)
    (_ : (1 : ℕ) ≤ S.Q0)
    (_ : Real.log S.H ≤ Msch * ((↑((2 : ℕ) * dB + (2 : ℕ)) : ℝ) + Real.log (fp.modeStarG Dm0
      dB Hm δ Nl kD δ) + Real.log (fp.Bst Dm0 dB Hm δ Nl kD δ) + Real.log (max (2 : ℝ)
      Nl) + Real.log (↑(fp.Q0bd dB) : ℝ) + (1 : ℝ)) ^ (12 : ℕ))
    (_ : (↑S.K : ℝ) ≤ Msch * ((↑((2 : ℕ) * dB + (2 : ℕ)) : ℝ) + Real.log (fp.modeStarG Dm0 dB
      Hm δ Nl kD δ) + Real.log (fp.Bst Dm0 dB Hm δ Nl kD δ) + Real.log (max (2 : ℝ) Nl)
      + Real.log (↑(fp.Q0bd dB) : ℝ) + (1 : ℝ)) ^ (16 : ℕ))
    (hK1 : (1 : ℕ) ≤ S.K),
  let Lf : SearchLeaf :=
    leafAt A.famFuel fp.Lc (A.basicSlot p) s
  let ks : ℕ :=
    Lf.k
  let S0 : Finset (ℤ × ℤ) :=
    {I ∈ AD.Tc | ¬∃ c ∈ fp.failRoots, dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G
      c.1 c.2}
  let gs : ℤ × ℤ → Finset bf.Grp :=
    fun (I : ℤ × ℤ) => fp.groupsAt I ks
  let gset : Finset bf.Grp :=
    S0.biUnion gs
  ∀ (hlenMc : ∀ (l : Fin (4 : ℕ)), (AD.cat l).length ≤ fp.Mc),
  let mbs : (l : Fin (4 : ℕ)) → bf.MainBudget (AD.cat l) :=
    fun l => MainBudget.ofCounts bf fp.Mc (AD.cat l) (hlenMc l) l (fun e he => AD.hTc
      (AD.hT l e he).1) (fun e he => (AD.hT l e he).2.1) hNl0 (fun I _ => AD.hlab l I _
      le_rfl)
  ∀ (Ms : Fin (4 : ℕ) → bf.Grp → ModeSystem A.G (Fintype.card (bf.Lab ⊕ Fin fp.Mc)))
    (L : (l : Fin (4 : ℕ)) → (G : bf.Grp) → LiftData (bf.Lab ⊕ Fin fp.Mc) (Ms l G).Md)
    (_ : S.Dstar = fp.modeStarG Dm0 dB Hm δ Nl kD δ)
    (_ : ∀ (l : Fin (4 : ℕ)), ∀ G ∈ gset, (∀ (q : (Ms l G).Key), (Ms l G).dvOf q + (Ms l
      G).zc.dim ≤ (2 : ℕ) * dB + (2 : ℕ)) ∧ (Ms l G).Λ ≤ S.Dstar ∧ gaugeSqNorm (Ms l
      G).zc.dim (Ms l G).δc ≤ S.Dstar ∧ (2 : ℝ) * gaugeTail (Ms l G).zc.dim (Ms l G).δc
      / (2 : ℝ) ^ fp.Kstar Dm0 dB Hm δ Nl kD δ * S.Dstar ^ (300 : ℕ) ≤ (1 : ℝ) ∧ (∀ (m :
      (Ms l G).Md), S.Dstar⁻¹ ≤ (Ms l G).L.εM m) ∧ (∀ (V : ℤ × ℤ), (↑((Ms l G).alive
      V).card : ℝ) ≤ S.Dstar) ∧ ∀ (V : ℤ × ℤ), (↑(Finset.image (Ms l G).keyOf ((Ms l
      G).alive V)).card : ℝ) ≤ Nl)
    (hA6 : (6 : ℝ) ≤ S.A0),
  let qG : bf.Grp → ℕ :=
    fun (G : bf.Grp) => clearInt (bf.vtag (bf.grpCenter d G)).C
  ∀ (Vl0 : ℝ)
    (U : ℝ)
    (_ : U = max ((2 : ℝ) * (A.colBudget + (2 : ℝ)) * S.Dstar ^ (2 : ℕ)) √(TsideF A fp.P S.K
      (A.uslot p) ((2 : ℕ) ^ A.famFuel) ((2 : ℕ) * A.famFuel + (2 : ℕ)) (1 : ℝ) E cc (↑k
      : ℝ) (fun (_ : Fin (4 : ℕ)) => Vl0) ρ))
    (_ : (0 : ℝ) < S.Dstar)
    (_ : (1 : ℝ) ≤ S.Dstar)
    (_ : (16 : ℝ) ≤ U)
    (MV : ℝ)
    (_ : MV = (↑AD.Mp : ℝ) * (↑A.famVtxBound : ℝ))
    (ε : ℝ)
    (_ : ε = (U ^ (3 : ℕ) * S.Dstar ^ (5 : ℕ) * Real.exp (↑k : ℝ) * ((1 : ℝ) + MV))⁻¹)
    (_ : (0 : ℝ) < ε),
  let Ts : Finset (ℕ × ℕ) :=
    Finset.range (Nat.log (2 : ℕ) ⌊S.Dstar⌋₊ + (1 : ℕ)) ×ˢ Finset.range (Nat.log (2 : ℕ)
      ⌊S.Dstar⌋₊ + (1 : ℕ))
  ∀ (_ : (4 : ℝ) ≤ Nl)
    (_ : fp.modeStar Dm0 dB Hm δ Nl kD ≤ S.Dstar)
    (c : (l : Fin (4 : ℕ)) → (G : ↥gset) → ℤ → ℤ × ℤ → (Ms l (↑G : bf.Grp)).Md → ℂ)
    (_ : ∀ (l : Fin (4 : ℕ)) (G : ↥gset), ∀ b ∈ Finset.image (fun (β : ℕ) => A.R.1 + (↑(S.K *
      β) : ℤ)) (Finset.range (A.treeDepth + (1 : ℕ))), ∀ J ∈ fp.retainedV (↑G : bf.Grp)
      b S.K, ∑ m ∈ (Ms l (↑G : bf.Grp)).alive (ancAt A.G J (b - (4 : ℤ) * (↑S.K : ℤ))),
      ‖c l G b J m‖ ^ (2 : ℕ) ≤ (4 : ℝ) * S.Dstar ^ (2 : ℕ) * (1 : ℝ))
    (Cut : Fin (4 : ℕ) → Finset (ℤ × ℤ))
    (_ : ∀ (l : Fin (4 : ℕ)), dyadicRootLength A.G (Cut l) ≤ ρ * dyadicGridLength A.G A.R.1),
  let cf : (l : Fin (4 : ℕ)) → (G : bf.Grp) → ℤ → ℤ × ℤ → (Ms l G).Md → ℂ :=
    fun (l : Fin (4 : ℕ)) (G : bf.Grp) => if hG : G ∈ gset then c l ⟨G, hG⟩ else fun _ _
      _ => (0 : ℂ)
  let D₀ : fp.SideInput :=
    { cat := AD.cat, mbs := mbs, Lf := Lf, u := A.uslot p, S := S, hA := hA6,
      SP := S.sideParams (1 / 1024 : ℝ), hK := hK1,
      n := Fintype.card (bf.Lab ⊕ Fin fp.Mc), Ms := Ms, c := cf }
  ∀ (hcat : Fin (4 : ℕ) → List (CatCol bf.Vtx))
    (hmbb : ∀ (l : Fin (4 : ℕ)), ∀ e ∈ AD.cat l ++ hcat l, e.birth ∈ A.cells)
    (hmbT : ∀ (l : Fin (4 : ℕ)) (y : ℝ), (8 : ℝ) * A.colBudget + (↑(bf.tmplPath (AD.cat l ++
      hcat l) y) : ℝ) ≤ (8 : ℝ) * A.colBudget + ((1 : ℝ) + (↑AD.Mp : ℝ)) * Nl),
  let mb' : (l : Fin (4 : ℕ)) → bf.MainBudget (AD.cat l ++ hcat l) :=
    fun l =>
        { hb := hmbb l, B := 8 * A.colBudget + (1 + AD.Mp) * Nl, hTp := hmbT l }
  let D : fp.SideInput :=
    D₀.appendCat hcat mb'
  ∀ (_ : ∀ (l : Fin (4 : ℕ)), ∀ e ∈ hcat l, fp.hrank ≤ e.rank)
    (_ : ∀ (l : Fin (4 : ℕ)), D₀.Lf.role l ≤ (4 : ℕ)),
  let S1 : Finset (ℤ × ℤ) :=
    {I ∈ S0 | ∀ (j : Fin (4 : ℕ)), ∀ e ∈ Cut j, ¬dyadicGridCell A.G I.1 I.2 ⊆
      dyadicGridCell A.G e.1 e.2}
  ∀ (_ : S1 ⊆ S0)
    (_ : S1 ⊆ A.cells)
    (_ : ∀ I ∈ A.cells, A.blkStart S.K I.1 ∈ Finset.image (fun (β : ℕ) => A.R.1 + (↑(S.K * β)
      : ℤ)) (Finset.range (A.treeDepth + (1 : ℕ)))),
  let Nb : ℕ :=
    Nat.log (2 : ℕ) S.K + (1 : ℕ)
  ∀ (_ : Nb = Nat.log (2 : ℕ) S.K + (1 : ℕ))
    (_ : (0 : ℝ) < dyadicGridLength A.G A.R.1)
    (_ : (0 : ℝ) ≤ Vl0),
  let Os : Finset (Fin (4 : ℕ) × Fin (4 : ℕ) × ℕ × ℕ × ℕ × ℕ) :=
    FamParams.SideLeafM.nOs ((2 : ℕ) ^ A.famFuel) ((2 : ℕ) * A.famFuel + (2 : ℕ))
  ∀ (_ : Os = FamParams.SideLeafM.nOs ((2 : ℕ) ^ A.famFuel) ((2 : ℕ) * A.famFuel + (2 : ℕ))),
  let Cjg : ℝ :=
    ((↑((2 : ℕ) * A.famFuel + (2 : ℕ)) : ℝ) + (1 : ℝ)) ^ (2 : ℕ) * Real.exp ((2 : ℝ) *
      ((1024 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) * ((1024 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) + (↑cc :
      ℝ) + (7 : ℝ)) * ((1 : ℝ) + Real.log ((2 : ℝ) * (↑k : ℝ))) ^ (2 : ℕ)))
  ∀ (_ : Cjg = ((↑((2 : ℕ) * A.famFuel + (2 : ℕ)) : ℝ) + (1 : ℝ)) ^ (2 : ℕ) * Real.exp ((2 :
      ℝ) * ((1024 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) * ((1024 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) +
      (↑cc : ℝ) + (7 : ℝ)) * ((1 : ℝ) + Real.log ((2 : ℝ) * (↑k : ℝ))) ^ (2 : ℕ)))),
  let Γa : Fin (4 : ℕ) → ℝ :=
    fun (_ : Fin (4 : ℕ)) => (↑Os.card : ℝ) * ((↑Nb : ℝ) * ((2 : ℝ) * FamParams.capV A
      cc (↑k : ℝ) + (16 : ℝ) * (Cjg * FamParams.SideInput.sideB0 A cc (↑k : ℝ) Vl0) +
      (16 : ℝ) * ((↑Nb : ℝ) * (Cjg * ((↑Nb : ℝ) * FamParams.capV A cc (↑k : ℝ))))) +
      FamParams.SideInput.sideB0 A cc (↑k : ℝ) Vl0) / dyadicGridLength A.G A.R.1
  ∀ (_ : Γa = fun (_ : Fin (4 : ℕ)) => (↑Os.card : ℝ) * ((↑Nb : ℝ) * ((2 : ℝ) *
      FamParams.capV A cc (↑k : ℝ) + (16 : ℝ) * (Cjg * FamParams.SideInput.sideB0 A cc
      (↑k : ℝ) Vl0) + (16 : ℝ) * ((↑Nb : ℝ) * (Cjg * ((↑Nb : ℝ) * FamParams.capV A cc
      (↑k : ℝ))))) + FamParams.SideInput.sideB0 A cc (↑k : ℝ) Vl0) / dyadicGridLength
      A.G A.R.1),
  let Γb : Fin (4 : ℕ) → ℝ :=
    fun (_ : Fin (4 : ℕ)) => (↑Os.card : ℝ) * ((↑Nb : ℝ) * FamParams.capV A cc (↑k : ℝ)
      + FamParams.SideInput.sideB0 A cc (↑k : ℝ) Vl0) / dyadicGridLength A.G A.R.1
  ∀ (_ : Γb = fun (_ : Fin (4 : ℕ)) => (↑Os.card : ℝ) * ((↑Nb : ℝ) * FamParams.capV A cc (↑k
      : ℝ) + FamParams.SideInput.sideB0 A cc (↑k : ℝ) Vl0) / dyadicGridLength A.G A.R.1),
  let ΓU : ℝ :=
    (↑Os.card : ℝ) * ((2 : ℝ) * ((4 : ℝ) * E * dyadicGridLength A.G A.R.1)) /
      dyadicGridLength A.G A.R.1
  ∀ (_ : ΓU = (↑Os.card : ℝ) * ((2 : ℝ) * ((4 : ℝ) * E * dyadicGridLength A.G A.R.1)) /
      dyadicGridLength A.G A.R.1)
    (Ee : ℝ)
    (_ : ∑ I ∈ S1, ∑ G ∈ gs I, ∑ l : Fin (4 : ℕ), ‖(D₀.withQ0 (qG G)).errAt L l G I‖ ^ (2 :
      ℕ) ≤ Ee)
    (_ : Ee ≤ ((8 : ℝ) * (↑dB : ℝ) * δ + (2 : ℝ) * δ ^ (2 : ℕ)) * ((4 : ℝ) * Nl * A.colBudget
      ^ (2 : ℕ) * (1 : ℝ)) * (↑((4 : ℕ) * (AD.Mp * A.famVtxBound)) : ℝ) *
      dyadicGridLength A.G A.R.1)
    (_ : ∑ I ∈ S1, dyadicGridLength A.G I.1 * (↑(gs I).card : ℝ) ≤ (↑(AD.Mp * A.famVtxBound)
      : ℝ) * dyadicGridLength A.G A.R.1)
    (_ : (1 : ℕ) ≤ dB)
    (_ : ∀ (j : Fin (4 : ℕ)) (G : ↥gset), D.c j (↑G : bf.Grp) = c j G),
  let Gq : ℝ :=
    Real.exp (((6144 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) * ((1024 : ℝ) * ((↑cc : ℝ) + (1 : ℝ))
      + (↑cc : ℝ) + (7 : ℝ)) + (4 : ℝ)) * ((1 : ℝ) + Real.log ((2 : ℝ) * (↑k : ℝ))) ^ (2
      : ℕ))
  ∀ (_ : Vl0 = (24 : ℝ) * ((↑⌊(180 : ℝ) * (↑S.dmax : ℝ) * Real.log ((2 : ℝ) * S.Dm) / (1 /
      1024 : ℝ)⌋₊ : ℝ) + (1 : ℝ)) * (Gq + (2 : ℝ) * (1 : ℝ) / S.Dstar ^ (394 : ℕ))),
  let Mt : ℝ :=
    (24 : ℝ) * ((2 : ℝ) * Gq + (2 : ℝ) * (↑S.K : ℝ) * Vl0) * (↑(Finset.range (S.Jstar +
      (1 : ℕ)) ×ˢ Ts ×ˢ dyThr ε U S.Dstar).card : ℝ) / ρ
  ∀ (_ : Mt = (24 : ℝ) * ((2 : ℝ) * Gq + (2 : ℝ) * (↑S.K : ℝ) * Vl0) * (↑(Finset.range
      (S.Jstar + (1 : ℕ)) ×ˢ Ts ×ˢ dyThr ε U S.Dstar).card : ℝ) / ρ),
  let Iw : ℕ :=
    ⌊Real.logb (2 : ℝ) (S.Dstar ^ (250 : ℕ))⌋₊
  ∀ (C : Finset (ℤ × ℤ))
    (C₂ : Finset (ℤ × ℤ))
    (_ : C ⊆ A.cells)
    (_ : dyadicRootLength A.G (maximalDyadicCells A.G C) ≤ (2 : ℝ) * ρ * dyadicGridLength A.G
      A.R.1)
    (_ : C₂ ⊆ S1)
    (_ : dyadicRootLength A.G C₂ ≤ ρ * dyadicGridLength A.G A.R.1)
    (_ : ∀ (l : Fin (4 : ℕ)), ∀ I ∈ {I ∈ {I ∈ S1 | ¬∃ e ∈ C, dyadicGridCell A.G I.1 I.2 ⊆
      dyadicGridCell A.G e.1 e.2} | ¬∃ e ∈ C₂, dyadicGridCell A.G I.1 I.2 ⊆
      dyadicGridCell A.G e.1 e.2}, ∀ G ∈ gs I, √((dyadicGridLength A.G I.1)⁻¹ * ∫ (y :
      ℝ) in dyadicGridLeft A.G I.1 I.2..dyadicGridLeft A.G I.1 I.2 + dyadicGridLength
      A.G I.1, ‖augPhys ((D.withQ0 (qG G)).toLeaf.sv l G I) y‖ ^ (2 : ℕ)) ≤ U)
    (_ : ∑ I ∈ {I ∈ S1 | ¬∃ e ∈ C, dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G e.1 e.2}
      with ¬∃ e ∈ C₂, dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G e.1 e.2,
      dyadicGridLength A.G I.1 * min A.η ‖∑ G ∈ gs I, (fp.Λc I : (Fin (4 : ℕ) →
      ↥(ColumnL2 (bf.Lab ⊕ Fin fp.Mc))) → ℂ) fun (l : Fin (4 : ℕ)) => (D.toLeafQ qG).out
      l G I‖ ≤ (6 : ℝ) * (256 : ℝ) * ((2 : ℝ) ^ A.famFuel) ^ (2 : ℕ) * ((2 : ℝ) * η₀ +
      fp.farC A.famFuel AD.τ₃ (2 : ℝ)) * D.Tside qG ((2 : ℕ) ^ A.famFuel) ((2 : ℕ) *
      A.famFuel + (2 : ℕ)) (1 : ℝ) E cc (↑k : ℝ) (fun (_ : Fin (4 : ℕ)) => Vl0) ρ *
      dyadicGridLength A.G A.R.1 + (6 : ℝ) * ∑ a : Fin (4 : ℕ), ∑ b : Fin (4 : ℕ), ∑ e :
      Fin (4 : ℕ), (D.toLeafQ qG).nearBnd hq2 hq3 Nd Nb ((2 : ℕ) ^ A.famFuel) ((2 : ℕ) *
      A.famFuel + (2 : ℕ)) (↑AD.Mp : ℝ) ((2 : ℝ) * √(1 : ℝ)) (ρ / (64 : ℝ)) Γa Γb ΓU a b
      e + A.η ^ ((1 : ℝ) - ((1 : ℝ) - (1 / 1200 : ℝ))) * (D.Tside qG ((2 : ℕ) ^
      A.famFuel) ((2 : ℕ) * A.famFuel + (2 : ℕ)) (1 : ℝ) E cc (↑k : ℝ) (fun (_ : Fin (4
      : ℕ)) => Vl0) ρ ^ (((1 : ℝ) - (1 / 1200 : ℝ)) / (2 : ℝ)) * D.Tside qG ((2 : ℕ) ^
      A.famFuel) ((2 : ℕ) * A.famFuel + (2 : ℕ)) (1 : ℝ) E cc (↑k : ℝ) (fun (_ : Fin (4
      : ℕ)) => Vl0) ρ ^ (((1 : ℝ) - (1 / 1200 : ℝ)) / (2 : ℝ)) * D.Tside qG ((2 : ℕ) ^
      A.famFuel) ((2 : ℕ) * A.famFuel + (2 : ℕ)) (1 : ℝ) E cc (↑k : ℝ) (fun (_ : Fin (4
      : ℕ)) => Vl0) ρ ^ (((1 : ℝ) - (1 / 1200 : ℝ)) / (2 : ℝ)) * dyadicGridLength A.G
      A.R.1) + (82 : ℝ) * ((81 : ℝ) * (localFormUniformConstant κ * (coreBd (max ((2 :
      ℝ) * √(1 : ℝ)) A.S) (D.T2 cc (↑k : ℝ) (fun (_ : Fin (4 : ℕ)) => Vl0) ρ) + errBd
      (max ((2 : ℝ) * √(1 : ℝ)) A.S) (D.T2 cc (↑k : ℝ) (fun (_ : Fin (4 : ℕ)) => Vl0) ρ)
      + √(D.Tside qG ((2 : ℕ) ^ A.famFuel) ((2 : ℕ) * A.famFuel + (2 : ℕ)) (1 : ℝ) E cc
      (↑k : ℝ) (fun (_ : Fin (4 : ℕ)) => Vl0) ρ)) ^ (3 : ℕ)) * (√((4 : ℝ) * ((↑(AD.Mp *
      A.famVtxBound) : ℝ) * dyadicGridLength A.G A.R.1)) * √Ee)) + (82 : ℝ) * (A.η ^ ((1
      : ℝ) - ((1 : ℝ) - (1 / 1200 : ℝ))) * ((81 : ℝ) * localFormUniformConstant κ * max
      (coreBd (max ((2 : ℝ) * √(1 : ℝ)) A.S) (D.T2 cc (↑k : ℝ) (fun (_ : Fin (4 : ℕ)) =>
      Vl0) ρ)) √(D.Tside qG ((2 : ℕ) ^ A.famFuel) ((2 : ℕ) * A.famFuel + (2 : ℕ)) (1 :
      ℝ) E cc (↑k : ℝ) (fun (_ : Fin (4 : ℕ)) => Vl0) ρ)) ^ ((1 : ℝ) - (1 / 1200 : ℝ)) *
      (D.Tside qG ((2 : ℕ) ^ A.famFuel) ((2 : ℕ) * A.famFuel + (2 : ℕ)) (1 : ℝ) E cc (↑k
      : ℝ) (fun (_ : Fin (4 : ℕ)) => Vl0) ρ ^ (((1 : ℝ) - (1 / 1200 : ℝ)) / (2 : ℝ)) *
      D.Tside qG ((2 : ℕ) ^ A.famFuel) ((2 : ℕ) * A.famFuel + (2 : ℕ)) (1 : ℝ) E cc (↑k
      : ℝ) (fun (_ : Fin (4 : ℕ)) => Vl0) ρ ^ (((1 : ℝ) - (1 / 1200 : ℝ)) / (2 : ℝ)) *
      D.Tside qG ((2 : ℕ) ^ A.famFuel) ((2 : ℕ) * A.famFuel + (2 : ℕ)) (1 : ℝ) E cc (↑k
      : ℝ) (fun (_ : Fin (4 : ℕ)) => Vl0) ρ ^ (((1 : ℝ) - (1 / 1200 : ℝ)) / (2 : ℝ)) *
      dyadicGridLength A.G A.R.1)) + (A.η ^ (1 / 1200 : ℝ) * (dyadicGridLength A.G A.R.1
      * (D.coreM4 (3 : ℕ) U ε (max (max (1 : ℝ) Mt) (D.Tside qG ((2 : ℕ) ^ A.famFuel)
      ((2 : ℕ) * A.famFuel + (2 : ℕ)) (1 : ℝ) E cc (↑k : ℝ) (fun (_ : Fin (4 : ℕ)) =>
      Vl0) ρ)) + ∑ l : Fin (4 : ℕ), D.coreM3 (3 : ℕ) (1 : ℕ) Iw U ε (max (max (1 : ℝ)
      Mt) (D.Tside qG ((2 : ℕ) ^ A.famFuel) ((2 : ℕ) * A.famFuel + (2 : ℕ)) (1 : ℝ) E cc
      (↑k : ℝ) (fun (_ : Fin (4 : ℕ)) => Vl0) ρ)) l)) + ∑ I ∈ {I ∈ S1 | ¬∃ e ∈ C,
      dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G e.1 e.2} with ¬∃ e ∈ C₂,
      dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G e.1 e.2, dyadicGridLength A.G I.1
      * D.coreE qG gs (3 : ℕ) (1 : ℕ) Iw U ε I))
    (_ : (↑dB : ℝ) ≤ (↑k : ℝ) ^ cc)
    (_ : Real.log fp.Hed ≤ (↑k : ℝ) ^ cc)
    (_ : E ≤ (↑k : ℝ) ^ cc)
    (_ : ρ⁻¹ ≤ (↑k : ℝ) ^ cc)
    (_ : (↑k : ℝ) ^ cc ≤ kD)
    (_ : (2 : ℝ) ≤ (↑k : ℝ))
    (_ : CΛ = (2 : ℕ) * Cg + (12 : ℕ))
    (_ : eΛ = Cg + (3 : ℕ) * cc)
    (_ : (1 : ℝ) ≤ (↑fp.P : ℝ))
    (u : ℝ)
    (_ : u = kD * (↑fp.P : ℝ))
    (_ : (1 : ℝ) ≤ u)
    (_ : (↑k : ℝ) ≤ u)
    (_ : Nl ≤ Real.exp ((↑k : ℝ) ^ cc))
    (_ : (↑A.famVtxBound : ℝ) ≤ (8 : ℝ) * A.colBudget + (1 : ℝ))
    (_ : Real.log (fp.modeStarG Dm0 dB Hm δ Nl kD δ) ≤ (↑Cg : ℝ) * (kD * (↑fp.P : ℝ)) ^ Cg ∧
      Real.log ((2 : ℝ) ^ (fp.Kstar Dm0 dB Hm δ Nl kD δ + (1 : ℕ))) ≤ (↑Cg : ℝ) * (kD *
      (↑fp.P : ℝ)) ^ Cg),
  ∃ (F : Fin (6 : ℕ) → Finset (ℤ × ℤ)), (∀ (i : Fin (6 : ℕ)), ∀ c ∈ F i,
    dyadicGridCell A.G c.1 c.2 ⊆ dyadicGridCell A.G A.R.1 A.R.2) ∧ (∀ (i : Fin (6 :
    ℕ)), dyadicRootLength A.G (F i) ≤ (2 : ℝ) * ρ * dyadicGridLength A.G A.R.1) ∧ ∀ cs
    ⊆ AD.Tc, (∀ I ∈ cs, ¬∃ c ∈ fp.failRoots, dyadicGridCell A.G I.1 I.2 ⊆
    dyadicGridCell A.G c.1 c.2) → (∀ I ∈ cs, ∀ (i : Fin (6 : ℕ)), ∀ e ∈ F i,
    ¬dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G e.1 e.2) → ∑ I ∈ cs,
    dyadicGridLength A.G I.1 * min A.η ‖∑ G ∈ fp.groupsAt I ks, (fp.Λc I : (Fin (4 :
    ℕ) → ↥(ColumnL2 (bf.Lab ⊕ Fin fp.Mc))) → ℂ) fun (l : Fin (4 : ℕ)) => (fp.ballFilt
    l (AD.cat l) I G (Lf.role l) : ↥(ColumnL2 (bf.Lab ⊕ Fin fp.Mc)) → ↥(ColumnL2
    (bf.Lab ⊕ Fin fp.Mc))) (fp.inputL AD.cat I (bf.patIn fp.Mc p I) Lf.layers l)‖ ≤
    leafBnd Cl kD fp.P k cc A.η η₀ AD.τ₃ δ (finiteDepthConstant κ q Nd) (nbCM κ hq2
    hq3 + nbCUM κ hq2 hq3) q (dyadicGridLength A.G A.R.1)


open scoped Classical in
private def LeafEstimateStage6Statement : Prop :=
  ∀ (κ : LocalKernelClass)
    (c₀ : ℕ)
    (cc : ℕ)
    (_ : (1 : ℕ) ≤ cc)
    (Dm0 : ℕ)
    (Msch : ℝ)
    (_ : (0 : ℝ) < Msch)
    (Cg : ℕ)
    (_ : ∀ {κ : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ c₀} {bf : A.BasicFamilies} (fp
      : bf.FamParams) (dB : ℕ) {H δc N k δ : ℝ}, (1 : ℝ) ≤ k → (↑fp.Lc : ℝ) + (6 : ℝ) ≤
      k ^ (cc + (6 : ℕ)) → (↑fp.Hmax : ℝ) + (1 : ℝ) ≤ (k * (↑fp.P : ℝ)) ^ (cc + (6 : ℕ))
      → (↑dB : ℝ) ≤ k ^ (cc + (6 : ℕ)) → (2 : ℝ) ≤ fp.Hed → Real.log fp.Hed ≤ k ^ (cc +
      (6 : ℕ)) → (1 : ℝ) ≤ H → Real.log H ≤ k ^ (cc + (6 : ℕ)) → (0 : ℝ) < δc → δc⁻¹ ≤
      Real.exp (k ^ (cc + (6 : ℕ))) → (0 : ℝ) ≤ N → N ≤ Real.exp (k ^ (cc + (6 : ℕ))) →
      A.colBudget ≤ Real.exp (k ^ (cc + (6 : ℕ))) → (0 : ℝ) < δ → δ⁻¹ ≤ Real.exp (k ^
      (cc + (6 : ℕ))) → Real.log (fp.modeStarG Dm0 dB H δc N k δ) ≤ (↑Cg : ℝ) * (k *
      (↑fp.P : ℝ)) ^ Cg ∧ Real.log ((2 : ℝ) ^ (fp.Kstar Dm0 dB H δc N k δ + (1 : ℕ))) ≤
      (↑Cg : ℝ) * (k * (↑fp.P : ℝ)) ^ Cg)
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
    (eΛ : ℕ)
    (CM1 : ℕ)
    (t3 : ℕ)
    (Cb : ℕ)
    (Cl : ℕ)
    (_ : g = (8192 : ℕ) * (cc + (1 : ℕ)) * ((1024 : ℕ) * (cc + (1 : ℕ)) + cc + (7 : ℕ)) + cc
      ^ (2 : ℕ) + (8 : ℕ) ∧ cT = (10 : ℝ) ^ (22 : ℕ) * ((1 : ℝ) +
      localFormUniformConstant κ) ^ (2 : ℕ) ∧ cL = (159 : ℝ) + (32 : ℝ) * (↑g : ℝ) + (8
      : ℝ) * Real.log cT ∧ cK = ((1 : ℝ) + (7 : ℝ) * (10 : ℝ) ^ (9 : ℕ) + cT) * (cL + (2
      : ℝ)) ∧ cMc = (C4c κ + (4 : ℝ) * C3c κ) * cL ^ (4 : ℕ) * cK ^ (2 : ℕ) ∧ cm =
      (196608 : ℝ) * cT + (83 : ℝ) * ((1 : ℝ) + (81 : ℝ) * localFormUniformConstant κ *
      ((30000 : ℝ) + √cT)) * ((1 : ℝ) + cT) ^ (3 : ℕ) + cMc ∧ ce = (6642 : ℝ) *
      localFormUniformConstant κ * ((60000 : ℝ) + √cT) ^ (3 : ℕ) * (288 : ℝ) + (9 : ℝ) *
      ((16 : ℝ) * fourErrC κ (3 : ℕ) + (648 : ℝ) * threeErrC κ (3 : ℕ) (1 : ℕ) + (324 :
      ℝ) * threeErrC κ (3 : ℕ) (1 : ℕ) * √cT) ∧ ce2 = K1c * ((2 : ℝ) * fourKC κ (3 : ℕ)
      * (12 : ℝ) ^ (4 : ℕ)) + (4 : ℝ) * (K1c * ((8 : ℝ) * entryCU κ (3 : ℕ) (1 : ℕ) * (2
      : ℝ) ^ ((1 : ℕ) + (4 : ℕ)) * (12 : ℝ) ^ (3 : ℕ))) * (501 : ℝ) ∧ cQ = (65536 : ℝ) *
      ((8 : ℝ) + (80 : ℝ) * (9 : ℝ) ^ cc * (↑cc : ℝ)) * ((80 : ℝ) * (9 : ℝ) ^ cc * (↑cc
      : ℝ)) * ((4 : ℝ) * (↑cc : ℝ) ^ (2 : ℕ)) * ((17 : ℝ) * (10 : ℝ) ^ (7 : ℕ)) ∧ CΛ =
      (2 : ℕ) * Cg + (12 : ℕ) ∧ eΛ = Cg + (3 : ℕ) * cc ∧ CM1 = (⌈Msch⌉₊ + (1 : ℕ)) * CΛ
      ^ (16 : ℕ) ∧ t3 = (3 : ℕ) ^ cc ∧ Cb = CM1 + (501 : ℕ) * Cg + t3 + (2 : ℕ) * cc +
      (20 : ℕ) + (16 : ℕ) * eΛ ∧ Cl = ⌈cm * (↑Cb : ℝ) ^ (59 : ℕ) + ce * (↑Cb : ℝ) ^ (18
      : ℕ) + ce2 + (3 : ℝ) * (10 : ℝ) ^ (11 : ℕ) * cQ⌉₊ + (59 : ℕ) * Cb + (4 : ℕ) * g +
      (8 : ℕ) * cc + (8 : ℕ))
    (A : ActiveSetup κ c₀)
    (bf : A.BasicFamilies)
    (k : ℕ)
    (η₀ : ℝ)
    (E : ℝ)
    (_ : A.AncClosed)
    (_ : ∀ I ∈ A.cells, ∀ (s s' : Fin (4 : ℕ)), s ≠ s' → PairSmall (dyadicGridLeft A.G I.1
      I.2) (dyadicGridLength A.G I.1) (A.w I) s s' (A.Y I s) (A.Y I s') ((2 : ℝ) * η₀))
    (_ : A.SubRootProps η₀ E)
    (_ : A.S = (2 : ℝ))
    (_ : A.η = (4 : ℝ) * η₀)
    (_ : (0 : ℝ) < η₀)
    (_ : A.cells.Nonempty)
    (q : ℝ)
    (hq2 : (2 : ℝ) < q)
    (hq3 : q < (3 : ℝ))
    (Nd : ℕ)
    (_ : A.DepthWin Nd)
    (p : Fin (3 : ℕ))
    (AD : bf.AttemptData p)
    (d : bf.Vtx)
    (s : ℕ)
    (δ : ℝ)
    (ρ : ℝ)
    (kD : ℝ)
    (_ : (0 : ℝ) < δ)
    (_ : δ ≤ (1 / 8 : ℝ))
    (_ : (0 : ℝ) < ρ)
    (_ : ρ < (1 : ℝ))
    (_ : Real.log ((2 : ℝ) * A.colBudget) ≤ (↑k : ℝ) ^ cc)
    (_ : (↑((2 : ℕ) * A.famFuel + (2 : ℕ)) : ℝ) ≤ (↑cc : ℝ) * (Real.log (↑k : ℝ) + (1 : ℝ)))
    (_ : (1 : ℝ) ≤ (↑k : ℝ)),
  let fp : bf.FamParams :=
    AD.fp
  let dB : ℕ :=
    A.dBnd
  ∀ (_ : (↑fp.Lc : ℝ) + (6 : ℝ) ≤ (↑k : ℝ) ^ cc ∧ (↑fp.Hmax : ℝ) + (1 : ℝ) ≤ ((↑k : ℝ) *
      (↑fp.P : ℝ)) ^ cc ∧ (↑dB : ℝ) ≤ (↑k : ℝ) ^ cc ∧ Real.log fp.Hed ≤ (↑k : ℝ) ^ cc ∧
      Real.log A.Hsrc ≤ (↑k : ℝ) ^ cc ∧ Real.log (max A.H padW) ≤ (↑k : ℝ) ^ cc ∧ δ⁻¹ ≤
      Real.exp kD ∧ E ≤ (↑k : ℝ) ^ cc ∧ ρ⁻¹ ≤ (↑k : ℝ) ^ cc ∧ (2 : ℝ) + Real.log
      bumpConst + (100 : ℝ) ≤ (↑k : ℝ) ∧ (↑k : ℝ) ^ cc ≤ kD ∧ (2 : ℝ) ≤ (↑k : ℝ) ∧ (0 :
      ℝ) ≤ Real.log bumpConst),
  let Nl : ℝ :=
    AD.n (fp.Lc + (5 : ℕ))
  ∀ (_ : Real.log ((2 : ℝ) * ((8 : ℝ) * A.colBudget + ((1 : ℝ) + (↑AD.Mp : ℝ)) * Nl)) ≤ (↑k :
      ℝ) ^ cc)
    (_ : (2 : ℝ) ≤ A.colBudget)
    (_ : Monotone AD.n)
    (hNl0 : (0 : ℝ) ≤ Nl),
  let Hm : ℝ :=
    max (max A.Hsrc (Real.exp (↑dB : ℝ))) (max ((5832 : ℝ) * max A.H padW ^ (4 : ℕ))
      ((↑dB : ℝ) * (bumpConst * (8 : ℝ) ^ (32 : ℕ) * ((2 : ℝ) / δ))))
  ∀ (_ : (1 : ℝ) ≤ Hm)
    (_ : ∀ (w : bf.Vtx) (a c : Fin (bf.vtag w).dim), (↑(rationalHeight ((bf.vtag w).C a c)) :
      ℝ) ≤ fp.Hed)
    (S : ModeSchedule)
    (_ : S.dmax = (2 : ℕ) * dB + (2 : ℕ))
    (_ : S.Dm = max (2 : ℝ) Nl)
    (_ : S.Valid (340 : ℕ) (5 : ℕ) (4 : ℕ) (600 : ℕ) (1 / 1024 : ℝ) (packetW S.dmax S.H))
    (_ : (2 : ℕ) ≤ S.dmax)
    (_ : (↑S.dmax : ℝ) ≤ S.Dstar)
    (_ : (2 : ℝ) ≤ S.Dstar)
    (_ : (2 : ℝ) ≤ S.Bstar)
    (_ : (1 : ℕ) ≤ S.Q0)
    (_ : Real.log S.H ≤ Msch * ((↑((2 : ℕ) * dB + (2 : ℕ)) : ℝ) + Real.log (fp.modeStarG Dm0
      dB Hm δ Nl kD δ) + Real.log (fp.Bst Dm0 dB Hm δ Nl kD δ) + Real.log (max (2 : ℝ)
      Nl) + Real.log (↑(fp.Q0bd dB) : ℝ) + (1 : ℝ)) ^ (12 : ℕ))
    (_ : (↑S.K : ℝ) ≤ Msch * ((↑((2 : ℕ) * dB + (2 : ℕ)) : ℝ) + Real.log (fp.modeStarG Dm0 dB
      Hm δ Nl kD δ) + Real.log (fp.Bst Dm0 dB Hm δ Nl kD δ) + Real.log (max (2 : ℝ) Nl)
      + Real.log (↑(fp.Q0bd dB) : ℝ) + (1 : ℝ)) ^ (16 : ℕ))
    (hK1 : (1 : ℕ) ≤ S.K),
  let Lf : SearchLeaf :=
    leafAt A.famFuel fp.Lc (A.basicSlot p) s
  let ks : ℕ :=
    Lf.k
  let S0 : Finset (ℤ × ℤ) :=
    {I ∈ AD.Tc | ¬∃ c ∈ fp.failRoots, dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G
      c.1 c.2}
  ∀ (_ : S0 ⊆ AD.Tc),
  let gs : ℤ × ℤ → Finset bf.Grp :=
    fun (I : ℤ × ℤ) => fp.groupsAt I ks
  let gset : Finset bf.Grp :=
    S0.biUnion gs
  ∀ (_ : ∀ I ∈ S0, ∀ G ∈ gs I, fp.Cert ks G I ∧ fp.ActualUse G I)
    (hlenMc : ∀ (l : Fin (4 : ℕ)), (AD.cat l).length ≤ fp.Mc),
  let mbs : (l : Fin (4 : ℕ)) → bf.MainBudget (AD.cat l) :=
    fun l => MainBudget.ofCounts bf fp.Mc (AD.cat l) (hlenMc l) l (fun e he => AD.hTc
      (AD.hT l e he).1) (fun e he => (AD.hT l e he).2.1) hNl0 (fun I _ => AD.hlab l I _
      le_rfl)
  ∀ (Ms : Fin (4 : ℕ) → bf.Grp → ModeSystem A.G (Fintype.card (bf.Lab ⊕ Fin fp.Mc)))
    (L : (l : Fin (4 : ℕ)) → (G : bf.Grp) → LiftData (bf.Lab ⊕ Fin fp.Mc) (Ms l G).Md)
    (_ : S.Dstar = fp.modeStarG Dm0 dB Hm δ Nl kD δ)
    (_ : ∀ (l : Fin (4 : ℕ)), ∀ G ∈ gset, (∀ (q : (Ms l G).Key), (Ms l G).dvOf q + (Ms l
      G).zc.dim ≤ (2 : ℕ) * dB + (2 : ℕ)) ∧ (Ms l G).Λ ≤ S.Dstar ∧ gaugeSqNorm (Ms l
      G).zc.dim (Ms l G).δc ≤ S.Dstar ∧ (2 : ℝ) * gaugeTail (Ms l G).zc.dim (Ms l G).δc
      / (2 : ℝ) ^ fp.Kstar Dm0 dB Hm δ Nl kD δ * S.Dstar ^ (300 : ℕ) ≤ (1 : ℝ) ∧ (∀ (m :
      (Ms l G).Md), S.Dstar⁻¹ ≤ (Ms l G).L.εM m) ∧ (∀ (V : ℤ × ℤ), (↑((Ms l G).alive
      V).card : ℝ) ≤ S.Dstar) ∧ ∀ (V : ℤ × ℤ), (↑(Finset.image (Ms l G).keyOf ((Ms l
      G).alive V)).card : ℝ) ≤ Nl)
    (hA6 : (6 : ℝ) ≤ S.A0),
  let qG : bf.Grp → ℕ :=
    fun (G : bf.Grp) => clearInt (bf.vtag (bf.grpCenter d G)).C
  ∀ (_ : ∀ (G : bf.Grp), (1 : ℕ) ≤ qG G ∧ qG G ≤ S.Q0)
    (Vl0 : ℝ)
    (U : ℝ)
    (_ : U = max ((2 : ℝ) * (A.colBudget + (2 : ℝ)) * S.Dstar ^ (2 : ℕ)) √(TsideF A fp.P S.K
      (A.uslot p) ((2 : ℕ) ^ A.famFuel) ((2 : ℕ) * A.famFuel + (2 : ℕ)) (1 : ℝ) E cc (↑k
      : ℝ) (fun (_ : Fin (4 : ℕ)) => Vl0) ρ))
    (_ : (0 : ℝ) < S.Dstar)
    (_ : (1 : ℝ) ≤ S.Dstar)
    (_ : (16 : ℝ) ≤ U)
    (_ : (0 : ℝ) < U)
    (MV : ℝ)
    (_ : MV = (↑AD.Mp : ℝ) * (↑A.famVtxBound : ℝ))
    (_ : (0 : ℝ) ≤ MV)
    (ε : ℝ)
    (_ : ε = (U ^ (3 : ℕ) * S.Dstar ^ (5 : ℕ) * Real.exp (↑k : ℝ) * ((1 : ℝ) + MV))⁻¹)
    (_ : (0 : ℝ) < ε)
    (_ : ε ≤ U)
    (_ : ∀ (σ : ℝ), ε ≤ σ → σ ≤ U → (∃ (k : ℤ), σ = (2 : ℝ) ^ k) → S.Dstar⁻¹ ≤ σ → σ ∈ dyThr
      ε U S.Dstar)
    (_ : (↑(dyThr ε U S.Dstar).card : ℝ) ≤ Real.logb (2 : ℝ) U - Real.logb (2 : ℝ) ε + (3 :
      ℝ)),
  let Ts : Finset (ℕ × ℕ) :=
    Finset.range (Nat.log (2 : ℕ) ⌊S.Dstar⌋₊ + (1 : ℕ)) ×ˢ Finset.range (Nat.log (2 : ℕ)
      ⌊S.Dstar⌋₊ + (1 : ℕ))
  ∀ (_ : Ts = Finset.range (Nat.log (2 : ℕ) ⌊S.Dstar⌋₊ + (1 : ℕ)) ×ˢ Finset.range (Nat.log (2
      : ℕ) ⌊S.Dstar⌋₊ + (1 : ℕ))),
  let BN : ℕ :=
    ⌈(8 : ℝ) * A.colBudget + Nl⌉₊
  let τb : ℝ :=
    (1 : ℝ) / ((1 : ℝ) + (↑BN : ℝ) * A.colBudget ^ (2 : ℕ))
  ∀ (_ : (0 : ℝ) < τb)
    (_ : τb ≤ (1 : ℝ))
    (_ : τb * (↑BN : ℝ) * A.colBudget ^ (2 : ℕ) ≤ (1 : ℝ))
    (_ : Real.exp ((↑A.Dg : ℝ) * ((1 : ℝ) + Real.log A.Hsrc + Real.log τb⁻¹) ^ A.Dg) ≤ fp.Hed)
    (_ : ∀ I ∈ A.cells, dyadicGridCell A.G I.1 I.2 ⊆ Set.Icc (dyadicGridLeft A.G A.R.1 A.R.2)
      (dyadicGridLeft A.G A.R.1 A.R.2 + dyadicGridLength A.G A.R.1))
    (_ : Fin (4 : ℕ) → ↥gset → bf.Vtx)
    (_ : ∀ (l : Fin (4 : ℕ)), fp.bbase (Lf.role l) + fp.P ≤ fp.Hmax)
    (_ : (4 : ℝ) ≤ Nl)
    (_ : ∀ (l : Fin (4 : ℕ)) (y : ℝ), (Finset.card ({q : ↥gset × (bf.Lab ⊕ Fin fp.Mc) | ∃ I ∈
      A.cells, (∃ (k' : ℕ), fp.Cert k' (↑q.1 : bf.Grp) I) ∧ ∃ (p_1 : Fin fp.P), y ∈
      dyadicGridCell A.G I.1 I.2 ∧ q.2 ∈ mainLabelsM A.G fp.Mc (bf.origCols l) (AD.cat
      l) I (fp.brank (Lf.role l)) (fp.bmask I (↑q.1 : bf.Grp) (Lf.role l) ((↑p_1 : ℕ) +
      (1 : ℕ))) d})) ≤ BN)
    (_ : ∀ (l : Fin (4 : ℕ)) (y : ℝ), ∑ G : ↥gset, (↑((Ms l (↑G : bf.Grp)).ptSet y).card : ℝ)
      ≤ S.Dstar)
    (_ : fp.modeStar Dm0 dB Hm δ Nl kD ≤ S.Dstar)
    (_ : ∀ (l : Fin (4 : ℕ)), (↑(Lf.layers l).length : ℝ) ≤ (↑cc : ℝ) * (Real.log (↑k : ℝ) +
      (1 : ℝ)))
    (c : (l : Fin (4 : ℕ)) → (G : ↥gset) → ℤ → ℤ × ℤ → (Ms l (↑G : bf.Grp)).Md → ℂ)
    (_ : ∀ (l : Fin (4 : ℕ)) (G : ↥gset), ∀ b ∈ Finset.image (fun (β : ℕ) => A.R.1 + (↑(S.K *
      β) : ℤ)) (Finset.range (A.treeDepth + (1 : ℕ))), ∀ J ∈ fp.retainedV (↑G : bf.Grp)
      b S.K, ∑ m ∈ (Ms l (↑G : bf.Grp)).alive (ancAt A.G J (b - (4 : ℤ) * (↑S.K : ℤ))),
      ‖c l G b J m‖ ^ (2 : ℕ) ≤ (4 : ℝ) * S.Dstar ^ (2 : ℕ) * (1 : ℝ))
    (Rr : (l : Fin (4 : ℕ)) → (h : ℕ) → ℕ × ℕ → (G : ↥gset) → (Ms l (↑G : bf.Grp)).RepClass
      (S.withQ0 (qG (↑G : bf.Grp))) hA6 (S.sideParams (1 / 1024 : ℝ)) (10 : ℕ) h)
    (_ : ∀ (l : Fin (4 : ℕ)), ∀ h ≤ S.Jstar, ∀ (t : ℕ × ℕ) (G : ↥gset), (Rr l h t G).Nd = {c
      ∈ (Ms l (↑G : bf.Grp)).succNodes (S.withQ0 (qG (↑G : bf.Grp))) hA6 (S.sideParams
      (1 / 1024 : ℝ)) (fp.retainedPairs (↑G : bf.Grp) (Finset.image (fun (β : ℕ) =>
      A.R.1 + (↑(S.K * β) : ℤ)) (Finset.range (A.treeDepth + (1 : ℕ)))) S.K) h | (Ms l
      (↑G : bf.Grp)).nodeType1 (S.withQ0 (qG (↑G : bf.Grp))) hA6 (10 : ℕ) h c = t.1 ∧
      (Ms l (↑G : bf.Grp)).nodeType2 (S.withQ0 (qG (↑G : bf.Grp))) hA6 (10 : ℕ) h c =
      t.2})
    (Cut : Fin (4 : ℕ) → Finset (ℤ × ℤ))
    (_ : ∀ (l : Fin (4 : ℕ)), dyadicRootLength A.G (Cut l) ≤ ρ * dyadicGridLength A.G A.R.1),
  let cf : (l : Fin (4 : ℕ)) → (G : bf.Grp) → ℤ → ℤ × ℤ → (Ms l G).Md → ℂ :=
    fun (l : Fin (4 : ℕ)) (G : bf.Grp) => if hG : G ∈ gset then c l ⟨G, hG⟩ else fun _ _
      _ => (0 : ℂ)
  let D₀ : fp.SideInput :=
    { cat := AD.cat, mbs := mbs, Lf := Lf, u := A.uslot p, S := S, hA := hA6,
      SP := S.sideParams (1 / 1024 : ℝ), hK := hK1,
      n := Fintype.card (bf.Lab ⊕ Fin fp.Mc), Ms := Ms, c := cf }
  let gE : ℤ × ℤ → Fin A.famVtxBound → bf.Grp :=
    fun (I : ℤ × ℤ) (i : Fin A.famVtxBound) => if h : (↑i : ℕ) < (gs I).card then
      (↑(((gs I).equivFin.symm : Fin (gs I).card → ↥(gs I)) ⟨(↑i : ℕ), h⟩) : bf.Grp)
      else default
  ∀ (_ : ∀ (I : ℤ × ℤ), ∀ G ∈ gs I, ∃ (i : Fin A.famVtxBound), gE I i = G)
    (hcat : Fin (4 : ℕ) → List (CatCol bf.Vtx))
    (_ : ∀ (l : Fin (4 : ℕ)), ∀ d ∈ hcat l, d.birth ∈ AD.Tc ∧ d.rank = fp.Lc + (5 : ℕ) ∧ (∃
      (M : fp.MaskName d.birth), fp.maskOf d.birth M d.tag) ∧ ∃ R ∈ residueBox (bf.vtag
      d.tag).dim (9 : ℕ), ∃ (γ : ℝ), d = templateCol (bf.vtag d.tag) l R γ d.birth
      d.rank d.tag)
    (hmbb : ∀ (l : Fin (4 : ℕ)), ∀ e ∈ AD.cat l ++ hcat l, e.birth ∈ A.cells)
    (hmbT : ∀ (l : Fin (4 : ℕ)) (y : ℝ), (8 : ℝ) * A.colBudget + (↑(bf.tmplPath (AD.cat l ++
      hcat l) y) : ℝ) ≤ (8 : ℝ) * A.colBudget + ((1 : ℝ) + (↑AD.Mp : ℝ)) * Nl),
  let mb' : (l : Fin (4 : ℕ)) → bf.MainBudget (AD.cat l ++ hcat l) :=
    fun l =>
        { hb := hmbb l, B := 8 * A.colBudget + (1 + AD.Mp) * Nl, hTp := hmbT l }
  let D : fp.SideInput :=
    D₀.appendCat hcat mb'
  ∀ (_ : ∀ (l : Fin (4 : ℕ)), ∀ e ∈ hcat l, fp.hrank ≤ e.rank)
    (_ : ∀ (l : Fin (4 : ℕ)), D₀.Lf.role l ≤ (4 : ℕ))
    (_ : ∀ (l : Fin (4 : ℕ)), ∀ e ∈ hcat l, bf.occAvail (↑e.tag.2 : ℤ × ℤ) e.tag.1),
  let S1 : Finset (ℤ × ℤ) :=
    {I ∈ S0 | ∀ (j : Fin (4 : ℕ)), ∀ e ∈ Cut j, ¬dyadicGridCell A.G I.1 I.2 ⊆
      dyadicGridCell A.G e.1 e.2}
  ∀ (_ : S1 ⊆ S0)
    (_ : S1 ⊆ A.cells)
    (_ : ∀ I ∈ A.cells, ((I.1 - A.R.1) / (↑S.K : ℤ)).toNat < A.treeDepth + (1 : ℕ))
    (_ : ∀ I ∈ A.cells, A.blkStart S.K I.1 ∈ Finset.image (fun (β : ℕ) => A.R.1 + (↑(S.K * β)
      : ℤ)) (Finset.range (A.treeDepth + (1 : ℕ))))
    (_ : ∀ I ∈ S1, ∀ (l : Fin (4 : ℕ)), D.u ≠ some l → ∀ (w : fp.TestName I Unit), fp.MainRk
      w → (fp.testOf l I (fun (_ : Unit) => bf.basicIn fp.Mc l I) w).Pass A.G
      (bf.origCols l) I A.csrc A.Hsrc bf.vtag (A.w I) (catThreshold A.famVtxBound AD.τ₃
      AD.n (fp.testOf l I (fun (_ : Unit) => bf.basicIn fp.Mc l I) w).r) fp.mH (D.cat l))
    (_ : ∀ I ∈ S1, ∀ (a : Fin (4 : ℕ)) (w : fp.HelperName I (Fin A.famVtxBound)),
      (fp.helperOf a I (fun (i : Fin A.famVtxBound) => (D.toLeafQ qG).sv a (gE I i) I)
      w).Pass A.G (bf.origCols a) I A.csrc A.Hsrc bf.vtag (A.w I) (catThreshold
      A.famVtxBound AD.τ₃ AD.n (fp.Lc + (5 : ℕ))) fp.mH (D.cat a))
    (_ : ∀ (R : ℕ), (1 : ℕ) ≤ R → R ≤ fp.Lc + (4 : ℕ) → catThreshold A.famVtxBound AD.τ₃ AD.n
      R * (A.colBudget * √(AD.n (R - (1 : ℕ)))) ≤ AD.τ₃)
    (_ : catThreshold A.famVtxBound AD.τ₃ AD.n (fp.Lc + (5 : ℕ)) * (A.colBudget * √(AD.n
      (fp.Lc + (4 : ℕ)))) ≤ AD.τ₃)
    (_ : ∀ (R : ℕ), (0 : ℝ) ≤ catThreshold A.famVtxBound AD.τ₃ AD.n R)
    (_ : ∀ I ∈ S1, ∀ (l : Fin (4 : ℕ)), ∀ r ≤ fp.Lc + (4 : ℕ), ∀ (M : bf.Vtx → Prop),
      (↑(mainLabelsM A.G fp.Mc (bf.origCols l) (D.cat l) I r M d).card : ℝ) ≤ AD.n r),
  let NH : ℝ :=
    (2 : ℝ) * A.colBudget + ((1 : ℝ) + (↑AD.Mp : ℝ)) * Nl
  ∀ (_ : ∀ I ∈ S1, ∀ (a : Fin (4 : ℕ)) (M : bf.Vtx → Prop), (↑(mainLabelsM A.G fp.Mc
      (bf.origCols a) (D.cat a) I (fp.Lc + (5 : ℕ)) M d).card : ℝ) ≤ NH),
  let τ₂ : ℝ :=
    AD.τ₃ / ((1 : ℝ) + A.colBudget * √(AD.n (fp.Lc + (4 : ℕ))) * (A.colBudget * √NH))
  ∀ (_ : (0 : ℝ) < τ₂)
    (_ : τ₂ ≤ (1 : ℝ))
    (_ : τ₂ * (A.colBudget * √(AD.n (fp.Lc + (4 : ℕ))) * (A.colBudget * √NH)) ≤ AD.τ₃)
    (_ : Real.exp ((↑A.Dg : ℝ) * ((1 : ℝ) + Real.log A.Hsrc + Real.log τ₂⁻¹) ^ A.Dg) ≤ fp.Hed),
  let Nb : ℕ :=
    Nat.log (2 : ℕ) S.K + (1 : ℕ)
  ∀ (_ : Nb = Nat.log (2 : ℕ) S.K + (1 : ℕ))
    (_ : S.K ≤ (2 : ℕ) ^ Nb)
    (_ : (0 : ℝ) < dyadicGridLength A.G A.R.1)
    (_ : (0 : ℝ) ≤ Vl0),
  let Os : Finset (Fin (4 : ℕ) × Fin (4 : ℕ) × ℕ × ℕ × ℕ × ℕ) :=
    FamParams.SideLeafM.nOs ((2 : ℕ) ^ A.famFuel) ((2 : ℕ) * A.famFuel + (2 : ℕ))
  ∀ (_ : Os = FamParams.SideLeafM.nOs ((2 : ℕ) ^ A.famFuel) ((2 : ℕ) * A.famFuel + (2 : ℕ))),
  let Cjg : ℝ :=
    ((↑((2 : ℕ) * A.famFuel + (2 : ℕ)) : ℝ) + (1 : ℝ)) ^ (2 : ℕ) * Real.exp ((2 : ℝ) *
      ((1024 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) * ((1024 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) + (↑cc :
      ℝ) + (7 : ℝ)) * ((1 : ℝ) + Real.log ((2 : ℝ) * (↑k : ℝ))) ^ (2 : ℕ)))
  ∀ (_ : Cjg = ((↑((2 : ℕ) * A.famFuel + (2 : ℕ)) : ℝ) + (1 : ℝ)) ^ (2 : ℕ) * Real.exp ((2 :
      ℝ) * ((1024 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) * ((1024 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) +
      (↑cc : ℝ) + (7 : ℝ)) * ((1 : ℝ) + Real.log ((2 : ℝ) * (↑k : ℝ))) ^ (2 : ℕ)))),
  let Γa : Fin (4 : ℕ) → ℝ :=
    fun (_ : Fin (4 : ℕ)) => (↑Os.card : ℝ) * ((↑Nb : ℝ) * ((2 : ℝ) * FamParams.capV A
      cc (↑k : ℝ) + (16 : ℝ) * (Cjg * FamParams.SideInput.sideB0 A cc (↑k : ℝ) Vl0) +
      (16 : ℝ) * ((↑Nb : ℝ) * (Cjg * ((↑Nb : ℝ) * FamParams.capV A cc (↑k : ℝ))))) +
      FamParams.SideInput.sideB0 A cc (↑k : ℝ) Vl0) / dyadicGridLength A.G A.R.1
  ∀ (_ : Γa = fun (_ : Fin (4 : ℕ)) => (↑Os.card : ℝ) * ((↑Nb : ℝ) * ((2 : ℝ) *
      FamParams.capV A cc (↑k : ℝ) + (16 : ℝ) * (Cjg * FamParams.SideInput.sideB0 A cc
      (↑k : ℝ) Vl0) + (16 : ℝ) * ((↑Nb : ℝ) * (Cjg * ((↑Nb : ℝ) * FamParams.capV A cc
      (↑k : ℝ))))) + FamParams.SideInput.sideB0 A cc (↑k : ℝ) Vl0) / dyadicGridLength
      A.G A.R.1)
    (_ : ∀ (a : Fin (4 : ℕ)), D.u ≠ some a → fp.stackEA Os (D.cat a) (D.mbs a) (D.toLeafQ
      qG).Dpre Nb (FamParams.capV A cc (↑k : ℝ)) (FamParams.SideInput.sideB0 A cc (↑k :
      ℝ) ((fun (_ : Fin (4 : ℕ)) => Vl0) a)) ≤ ((↑fp.P : ℝ) + (2 : ℝ)) * Γa a *
      dyadicGridLength A.G A.R.1),
  let Γb : Fin (4 : ℕ) → ℝ :=
    fun (_ : Fin (4 : ℕ)) => (↑Os.card : ℝ) * ((↑Nb : ℝ) * FamParams.capV A cc (↑k : ℝ)
      + FamParams.SideInput.sideB0 A cc (↑k : ℝ) Vl0) / dyadicGridLength A.G A.R.1
  ∀ (_ : Γb = fun (_ : Fin (4 : ℕ)) => (↑Os.card : ℝ) * ((↑Nb : ℝ) * FamParams.capV A cc (↑k
      : ℝ) + FamParams.SideInput.sideB0 A cc (↑k : ℝ) Vl0) / dyadicGridLength A.G A.R.1)
    (_ : ∀ (b : Fin (4 : ℕ)), D.u ≠ some b → (↑Os.card : ℝ) * ((↑Nb : ℝ) * FamParams.capV A
      cc (↑k : ℝ) + FamParams.SideInput.sideB0 A cc (↑k : ℝ) ((fun (_ : Fin (4 : ℕ)) =>
      Vl0) b)) ≤ Γb b * dyadicGridLength A.G A.R.1),
  let ΓU : ℝ :=
    (↑Os.card : ℝ) * ((2 : ℝ) * ((4 : ℝ) * E * dyadicGridLength A.G A.R.1)) /
      dyadicGridLength A.G A.R.1
  ∀ (_ : ΓU = (↑Os.card : ℝ) * ((2 : ℝ) * ((4 : ℝ) * E * dyadicGridLength A.G A.R.1)) /
      dyadicGridLength A.G A.R.1)
    (_ : (↑Os.card : ℝ) * ((2 : ℝ) * ((4 : ℝ) * E * dyadicGridLength A.G A.R.1)) ≤ ΓU *
      dyadicGridLength A.G A.R.1)
    (_ : ∀ I ∈ S1, ∀ G ∈ gs I, ∀ (l : Fin (4 : ℕ)), D.u ≠ some l → (D.withQ0 (qG G)).RepAt L
      l G I)
    (Ee : ℝ)
    (_ : ∑ I ∈ S1, ∑ G ∈ gs I, ∑ l : Fin (4 : ℕ), ‖(D₀.withQ0 (qG G)).errAt L l G I‖ ^ (2 :
      ℕ) ≤ Ee)
    (_ : Ee ≤ ((8 : ℝ) * (↑dB : ℝ) * δ + (2 : ℝ) * δ ^ (2 : ℕ)) * ((4 : ℝ) * Nl * A.colBudget
      ^ (2 : ℕ) * (1 : ℝ)) * (↑((4 : ℕ) * (AD.Mp * A.famVtxBound)) : ℝ) *
      dyadicGridLength A.G A.R.1)
    (_ : ∑ I ∈ S1, ∑ G ∈ gs I, ∑ l : Fin (4 : ℕ), ‖(D.withQ0 (qG G)).errAt L l G I‖ ^ (2 : ℕ)
      ≤ Ee)
    (_ : ∑ I ∈ S1, dyadicGridLength A.G I.1 * (↑(gs I).card : ℝ) ≤ (↑(AD.Mp * A.famVtxBound)
      : ℝ) * dyadicGridLength A.G A.R.1)
    (_ : (1 : ℕ) ≤ dB)
    (_ : ∀ G ∈ gset, (D.withQ0 (qG G)).PrinOK G δ fp.Hed (fp.Kstar Dm0 dB Hm δ Nl kD δ)
      (fp.Kstar Dm0 dB Hm δ Nl kD δ))
    (_ : ∀ G ∈ gset, (D.withQ0 (qG G)).Stab)
    (_ : ∀ (j : Fin (4 : ℕ)) (G : ↥gset), D.c j (↑G : bf.Grp) = c j G),
  let Gq : ℝ :=
    Real.exp (((6144 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) * ((1024 : ℝ) * ((↑cc : ℝ) + (1 : ℝ))
      + (↑cc : ℝ) + (7 : ℝ)) + (4 : ℝ)) * ((1 : ℝ) + Real.log ((2 : ℝ) * (↑k : ℝ))) ^ (2
      : ℕ))
  ∀ (_ : ∀ (l : Fin (4 : ℕ)), ∑ G : ↥gset, ∑ b ∈ Finset.image (fun (β : ℕ) => A.R.1 + (↑(S.K
      * β) : ℤ)) (Finset.range (A.treeDepth + (1 : ℕ))), ‖(Ms l (↑G : bf.Grp)).blockSide
      (S.withQ0 (qG (↑G : bf.Grp))) hA6 (S.sideParams (1 / 1024 : ℝ)) b (fp.retainedV
      (↑G : bf.Grp) b S.K) (c l G b)‖ ^ (2 : ℕ) ≤ (24 : ℝ) * ((↑⌊(180 : ℝ) * (↑S.dmax :
      ℝ) * Real.log ((2 : ℝ) * S.Dm) / (1 / 1024 : ℝ)⌋₊ : ℝ) + (1 : ℝ)) * (Gq + (2 : ℝ)
      * (1 : ℝ) / S.Dstar ^ (394 : ℕ)) * dyadicGridLength A.G A.R.1)
    (_ : Vl0 = (24 : ℝ) * ((↑⌊(180 : ℝ) * (↑S.dmax : ℝ) * Real.log ((2 : ℝ) * S.Dm) / (1 /
      1024 : ℝ)⌋₊ : ℝ) + (1 : ℝ)) * (Gq + (2 : ℝ) * (1 : ℝ) / S.Dstar ^ (394 : ℕ)))
    (_ : Gq = Real.exp (((6144 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) * ((1024 : ℝ) * ((↑cc : ℝ) + (1 :
      ℝ)) + (↑cc : ℝ) + (7 : ℝ)) + (4 : ℝ)) * ((1 : ℝ) + Real.log ((2 : ℝ) * (↑k : ℝ)))
      ^ (2 : ℕ))),
  let Mt : ℝ :=
    (24 : ℝ) * ((2 : ℝ) * Gq + (2 : ℝ) * (↑S.K : ℝ) * Vl0) * (↑(Finset.range (S.Jstar +
      (1 : ℕ)) ×ˢ Ts ×ˢ dyThr ε U S.Dstar).card : ℝ) / ρ
  ∀ (_ : Mt = (24 : ℝ) * ((2 : ℝ) * Gq + (2 : ℝ) * (↑S.K : ℝ) * Vl0) * (↑(Finset.range
      (S.Jstar + (1 : ℕ)) ×ˢ Ts ×ˢ dyThr ε U S.Dstar).card : ℝ) / ρ)
    (_ : ∀ (j : Fin (4 : ℕ)) (y : ℝ), ∀ h ∈ ModeComponents.upperHeights D.SP.Jst D.SP.δs, ∀ t
      ∈ Finset.range (Nat.log (2 : ℕ) ⌊D.S.Dstar⌋₊ + (1 : ℕ)) ×ˢ Finset.range (Nat.log
      (2 : ℕ) ⌊D.S.Dstar⌋₊ + (1 : ℕ)), ∀ σ ∈ dyThr ε U S.Dstar, ∑ G : ↥gset,
      (↑(Finset.image (fun (p : (ℤ × ℤ) × ℤ × (ℤ × ℤ) × (D.Ms j (↑G : bf.Grp)).Md) =>
      (Rr j h t G).rep p.2) ({p ∈ fp.useInst (↑G : bf.Grp) D.S.K (Rr j h t G).Nd | (∀ e
      ∈ Cut j, ¬dyadicGridCell A.G p.1.1 p.1.2 ⊆ dyadicGridCell A.G e.1 e.2) ∧ y ∈
      dyadicGridCell A.G p.1.1 p.1.2 ∧ σ ^ (2 : ℕ) ≤ (D.Ms j (↑G : bf.Grp)).nodeSize
      (D.withQ0 (qG (↑G : bf.Grp))).S D.hA D.SP (D.c j (↑G : bf.Grp)) h p})).card : ℝ) ≤
      Mt * σ ^ (-2 : ℝ))
    (_ : ∀ I ∈ S1, ∀ G ∈ gs I, ∀ h ∈ ModeComponents.upperHeights D.SP.Jst D.SP.δs, ∀ (j : Fin
      (4 : ℕ)), ∀ F ∈ (D.withQ0 (qG G)).goodCls G I j h, (D.withQ0 (qG G)).clsSize G I j
      F ≤ U)
    (_ : √(D.Tside qG ((2 : ℕ) ^ A.famFuel) ((2 : ℕ) * A.famFuel + (2 : ℕ)) (1 : ℝ) E cc (↑k
      : ℝ) (fun (_ : Fin (4 : ℕ)) => Vl0) ρ) ≤ U)
    (_ : (2 : ℝ) ^ ⌊Real.logb (2 : ℝ) (S.Dstar ^ (250 : ℕ))⌋₊ ≤ S.Dstar ^ (250 : ℕ) ∧ S.Dstar
      ^ (250 : ℕ) < (2 : ℝ) ^ (⌊Real.logb (2 : ℝ) (S.Dstar ^ (250 : ℕ))⌋₊ + (1 : ℕ)))
    (_ : ∀ G ∈ gset, (∀ (j : Fin (4 : ℕ)), (8 : ℝ) * (D.Ms j G).Λ ≤ D.S.Ξ) ∧ (∀ (j : Fin (4 :
      ℕ)), (D.Ms j G).zc = bf.vtag (bf.grpCenter d G)) ∧ (bf.vtag (bf.grpCenter d
      G)).dim ≤ D.S.dmax),
  ∃ (F : Fin (6 : ℕ) → Finset (ℤ × ℤ)), (∀ (i : Fin (6 : ℕ)), ∀ c ∈ F i,
    dyadicGridCell A.G c.1 c.2 ⊆ dyadicGridCell A.G A.R.1 A.R.2) ∧ (∀ (i : Fin (6 :
    ℕ)), dyadicRootLength A.G (F i) ≤ (2 : ℝ) * ρ * dyadicGridLength A.G A.R.1) ∧ ∀ cs
    ⊆ AD.Tc, (∀ I ∈ cs, ¬∃ c ∈ fp.failRoots, dyadicGridCell A.G I.1 I.2 ⊆
    dyadicGridCell A.G c.1 c.2) → (∀ I ∈ cs, ∀ (i : Fin (6 : ℕ)), ∀ e ∈ F i,
    ¬dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G e.1 e.2) → ∑ I ∈ cs,
    dyadicGridLength A.G I.1 * min A.η ‖∑ G ∈ fp.groupsAt I ks, (fp.Λc I : (Fin (4 :
    ℕ) → ↥(ColumnL2 (bf.Lab ⊕ Fin fp.Mc))) → ℂ) fun (l : Fin (4 : ℕ)) => (fp.ballFilt
    l (AD.cat l) I G (Lf.role l) : ↥(ColumnL2 (bf.Lab ⊕ Fin fp.Mc)) → ↥(ColumnL2
    (bf.Lab ⊕ Fin fp.Mc))) (fp.inputL AD.cat I (bf.patIn fp.Mc p I) Lf.layers l)‖ ≤
    leafBnd Cl kD fp.P k cc A.η η₀ AD.τ₃ δ (finiteDepthConstant κ q Nd) (nbCM κ hq2
    hq3 + nbCUM κ hq2 hq3) q (dyadicGridLength A.G A.R.1)


open scoped Classical in
private def LeafEstimateStage5Statement : Prop :=
  ∀ (κ : LocalKernelClass)
    (c₀ : ℕ)
    (cc : ℕ)
    (_ : (1 : ℕ) ≤ cc)
    (Dm0 : ℕ)
    (Msch : ℝ)
    (_ : (0 : ℝ) < Msch)
    (Cg : ℕ)
    (_ : ∀ {κ : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ c₀} {bf : A.BasicFamilies} (fp
      : bf.FamParams) (dB : ℕ) {H δc N k δ : ℝ}, (1 : ℝ) ≤ k → (↑fp.Lc : ℝ) + (6 : ℝ) ≤
      k ^ (cc + (6 : ℕ)) → (↑fp.Hmax : ℝ) + (1 : ℝ) ≤ (k * (↑fp.P : ℝ)) ^ (cc + (6 : ℕ))
      → (↑dB : ℝ) ≤ k ^ (cc + (6 : ℕ)) → (2 : ℝ) ≤ fp.Hed → Real.log fp.Hed ≤ k ^ (cc +
      (6 : ℕ)) → (1 : ℝ) ≤ H → Real.log H ≤ k ^ (cc + (6 : ℕ)) → (0 : ℝ) < δc → δc⁻¹ ≤
      Real.exp (k ^ (cc + (6 : ℕ))) → (0 : ℝ) ≤ N → N ≤ Real.exp (k ^ (cc + (6 : ℕ))) →
      A.colBudget ≤ Real.exp (k ^ (cc + (6 : ℕ))) → (0 : ℝ) < δ → δ⁻¹ ≤ Real.exp (k ^
      (cc + (6 : ℕ))) → Real.log (fp.modeStarG Dm0 dB H δc N k δ) ≤ (↑Cg : ℝ) * (k *
      (↑fp.P : ℝ)) ^ Cg ∧ Real.log ((2 : ℝ) ^ (fp.Kstar Dm0 dB H δc N k δ + (1 : ℕ))) ≤
      (↑Cg : ℝ) * (k * (↑fp.P : ℝ)) ^ Cg)
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
    (eΛ : ℕ)
    (CM1 : ℕ)
    (t3 : ℕ)
    (Cb : ℕ)
    (Cl : ℕ)
    (_ : g = (8192 : ℕ) * (cc + (1 : ℕ)) * ((1024 : ℕ) * (cc + (1 : ℕ)) + cc + (7 : ℕ)) + cc
      ^ (2 : ℕ) + (8 : ℕ) ∧ cT = (10 : ℝ) ^ (22 : ℕ) * ((1 : ℝ) +
      localFormUniformConstant κ) ^ (2 : ℕ) ∧ cL = (159 : ℝ) + (32 : ℝ) * (↑g : ℝ) + (8
      : ℝ) * Real.log cT ∧ cK = ((1 : ℝ) + (7 : ℝ) * (10 : ℝ) ^ (9 : ℕ) + cT) * (cL + (2
      : ℝ)) ∧ cMc = (C4c κ + (4 : ℝ) * C3c κ) * cL ^ (4 : ℕ) * cK ^ (2 : ℕ) ∧ cm =
      (196608 : ℝ) * cT + (83 : ℝ) * ((1 : ℝ) + (81 : ℝ) * localFormUniformConstant κ *
      ((30000 : ℝ) + √cT)) * ((1 : ℝ) + cT) ^ (3 : ℕ) + cMc ∧ ce = (6642 : ℝ) *
      localFormUniformConstant κ * ((60000 : ℝ) + √cT) ^ (3 : ℕ) * (288 : ℝ) + (9 : ℝ) *
      ((16 : ℝ) * fourErrC κ (3 : ℕ) + (648 : ℝ) * threeErrC κ (3 : ℕ) (1 : ℕ) + (324 :
      ℝ) * threeErrC κ (3 : ℕ) (1 : ℕ) * √cT) ∧ ce2 = K1c * ((2 : ℝ) * fourKC κ (3 : ℕ)
      * (12 : ℝ) ^ (4 : ℕ)) + (4 : ℝ) * (K1c * ((8 : ℝ) * entryCU κ (3 : ℕ) (1 : ℕ) * (2
      : ℝ) ^ ((1 : ℕ) + (4 : ℕ)) * (12 : ℝ) ^ (3 : ℕ))) * (501 : ℝ) ∧ cQ = (65536 : ℝ) *
      ((8 : ℝ) + (80 : ℝ) * (9 : ℝ) ^ cc * (↑cc : ℝ)) * ((80 : ℝ) * (9 : ℝ) ^ cc * (↑cc
      : ℝ)) * ((4 : ℝ) * (↑cc : ℝ) ^ (2 : ℕ)) * ((17 : ℝ) * (10 : ℝ) ^ (7 : ℕ)) ∧ CΛ =
      (2 : ℕ) * Cg + (12 : ℕ) ∧ eΛ = Cg + (3 : ℕ) * cc ∧ CM1 = (⌈Msch⌉₊ + (1 : ℕ)) * CΛ
      ^ (16 : ℕ) ∧ t3 = (3 : ℕ) ^ cc ∧ Cb = CM1 + (501 : ℕ) * Cg + t3 + (2 : ℕ) * cc +
      (20 : ℕ) + (16 : ℕ) * eΛ ∧ Cl = ⌈cm * (↑Cb : ℝ) ^ (59 : ℕ) + ce * (↑Cb : ℝ) ^ (18
      : ℕ) + ce2 + (3 : ℝ) * (10 : ℝ) ^ (11 : ℕ) * cQ⌉₊ + (59 : ℕ) * Cb + (4 : ℕ) * g +
      (8 : ℕ) * cc + (8 : ℕ))
    (A : ActiveSetup κ c₀)
    (bf : A.BasicFamilies)
    (k : ℕ)
    (η₀ : ℝ)
    (E : ℝ)
    (_ : A.AncClosed)
    (_ : ∀ I ∈ A.cells, ∀ (s s' : Fin (4 : ℕ)), s ≠ s' → PairSmall (dyadicGridLeft A.G I.1
      I.2) (dyadicGridLength A.G I.1) (A.w I) s s' (A.Y I s) (A.Y I s') ((2 : ℝ) * η₀))
    (_ : A.SubRootProps η₀ E)
    (_ : A.S = (2 : ℝ))
    (_ : A.η = (4 : ℝ) * η₀)
    (_ : (0 : ℝ) < η₀)
    (_ : A.cells.Nonempty)
    (q : ℝ)
    (hq2 : (2 : ℝ) < q)
    (hq3 : q < (3 : ℝ))
    (Nd : ℕ)
    (_ : A.DepthWin Nd)
    (p : Fin (3 : ℕ))
    (AD : bf.AttemptData p)
    (d : bf.Vtx)
    (s : ℕ)
    (δ : ℝ)
    (ρ : ℝ)
    (kD : ℝ)
    (_ : (0 : ℝ) < δ)
    (_ : δ ≤ (1 / 8 : ℝ))
    (_ : (0 : ℝ) < ρ)
    (_ : ρ < (1 : ℝ))
    (_ : Real.log ((2 : ℝ) * A.colBudget) ≤ (↑k : ℝ) ^ cc)
    (_ : (↑((2 : ℕ) * A.famFuel + (2 : ℕ)) : ℝ) ≤ (↑cc : ℝ) * (Real.log (↑k : ℝ) + (1 : ℝ)))
    (_ : (1 : ℝ) ≤ (↑k : ℝ)),
  let fp : bf.FamParams :=
    AD.fp
  let dB : ℕ :=
    A.dBnd
  ∀ (_ : (↑fp.Lc : ℝ) + (6 : ℝ) ≤ (↑k : ℝ) ^ cc ∧ (↑fp.Hmax : ℝ) + (1 : ℝ) ≤ ((↑k : ℝ) *
      (↑fp.P : ℝ)) ^ cc ∧ (↑dB : ℝ) ≤ (↑k : ℝ) ^ cc ∧ Real.log fp.Hed ≤ (↑k : ℝ) ^ cc ∧
      Real.log A.Hsrc ≤ (↑k : ℝ) ^ cc ∧ Real.log (max A.H padW) ≤ (↑k : ℝ) ^ cc ∧ δ⁻¹ ≤
      Real.exp kD ∧ E ≤ (↑k : ℝ) ^ cc ∧ ρ⁻¹ ≤ (↑k : ℝ) ^ cc ∧ (2 : ℝ) + Real.log
      bumpConst + (100 : ℝ) ≤ (↑k : ℝ) ∧ (↑k : ℝ) ^ cc ≤ kD ∧ (2 : ℝ) ≤ (↑k : ℝ) ∧ (0 :
      ℝ) ≤ Real.log bumpConst)
    (_ : (8 : ℝ) * (↑dB : ℝ) * δ ≤ (1 : ℝ)),
  let Nl : ℝ :=
    AD.n (fp.Lc + (5 : ℕ))
  ∀ (_ : Real.log ((2 : ℝ) * ((8 : ℝ) * A.colBudget + ((1 : ℝ) + (↑AD.Mp : ℝ)) * Nl)) ≤ (↑k :
      ℝ) ^ cc)
    (_ : (2 : ℝ) ≤ A.colBudget)
    (_ : Monotone AD.n)
    (hNl0 : (0 : ℝ) ≤ Nl),
  let Hm : ℝ :=
    max (max A.Hsrc (Real.exp (↑dB : ℝ))) (max ((5832 : ℝ) * max A.H padW ^ (4 : ℕ))
      ((↑dB : ℝ) * (bumpConst * (8 : ℝ) ^ (32 : ℕ) * ((2 : ℝ) / δ))))
  ∀ (_ : (1 : ℝ) ≤ Hm)
    (_ : ∀ (w : bf.Vtx), (bf.vtag w).dim ≤ dB)
    (_ : ∀ (w : bf.Vtx) (a c : Fin (bf.vtag w).dim), (↑(rationalHeight ((bf.vtag w).C a c)) :
      ℝ) ≤ fp.Hed)
    (S : ModeSchedule)
    (_ : S.dmax = (2 : ℕ) * dB + (2 : ℕ))
    (_ : S.Dm = max (2 : ℝ) Nl)
    (_ : S.Valid (340 : ℕ) (5 : ℕ) (4 : ℕ) (600 : ℕ) (1 / 1024 : ℝ) (packetW S.dmax S.H))
    (_ : (2 : ℕ) ≤ S.dmax)
    (_ : (↑S.dmax : ℝ) ≤ S.Dstar)
    (_ : (2 : ℝ) ≤ S.Dstar)
    (_ : (2 : ℝ) ≤ S.Bstar)
    (_ : (1 : ℕ) ≤ S.Q0)
    (_ : (↑S.Q0 : ℝ) * (2 : ℝ) ^ (fp.Kstar Dm0 dB Hm δ Nl kD δ + (1 : ℕ)) ≤ S.Bstar)
    (_ : Real.log S.H ≤ Msch * ((↑((2 : ℕ) * dB + (2 : ℕ)) : ℝ) + Real.log (fp.modeStarG Dm0
      dB Hm δ Nl kD δ) + Real.log (fp.Bst Dm0 dB Hm δ Nl kD δ) + Real.log (max (2 : ℝ)
      Nl) + Real.log (↑(fp.Q0bd dB) : ℝ) + (1 : ℝ)) ^ (12 : ℕ))
    (_ : (↑S.K : ℝ) ≤ Msch * ((↑((2 : ℕ) * dB + (2 : ℕ)) : ℝ) + Real.log (fp.modeStarG Dm0 dB
      Hm δ Nl kD δ) + Real.log (fp.Bst Dm0 dB Hm δ Nl kD δ) + Real.log (max (2 : ℝ) Nl)
      + Real.log (↑(fp.Q0bd dB) : ℝ) + (1 : ℝ)) ^ (16 : ℕ))
    (hK1 : (1 : ℕ) ≤ S.K),
  let Lf : SearchLeaf :=
    leafAt A.famFuel fp.Lc (A.basicSlot p) s
  let ks : ℕ :=
    Lf.k
  let S0 : Finset (ℤ × ℤ) :=
    {I ∈ AD.Tc | ¬∃ c ∈ fp.failRoots, dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G
      c.1 c.2}
  ∀ (_ : S0 ⊆ AD.Tc),
  let gs : ℤ × ℤ → Finset bf.Grp :=
    fun (I : ℤ × ℤ) => fp.groupsAt I ks
  let gset : Finset bf.Grp :=
    S0.biUnion gs
  ∀ (_ : ∀ I ∈ S0, ∀ G ∈ gs I, fp.Cert ks G I ∧ fp.ActualUse G I)
    (hlenMc : ∀ (l : Fin (4 : ℕ)), (AD.cat l).length ≤ fp.Mc),
  let mbs : (l : Fin (4 : ℕ)) → bf.MainBudget (AD.cat l) :=
    fun l => MainBudget.ofCounts bf fp.Mc (AD.cat l) (hlenMc l) l (fun e he => AD.hTc
      (AD.hT l e he).1) (fun e he => (AD.hT l e he).2.1) hNl0 (fun I _ => AD.hlab l I _
      le_rfl)
  ∀ (Ms : Fin (4 : ℕ) → bf.Grp → ModeSystem A.G (Fintype.card (bf.Lab ⊕ Fin fp.Mc)))
    (L : (l : Fin (4 : ℕ)) → (G : bf.Grp) → LiftData (bf.Lab ⊕ Fin fp.Mc) (Ms l G).Md)
    (_ : ∀ (l : Fin (4 : ℕ)), ∀ G ∈ gset, fp.ModeExports l (AD.cat l) G (Lf.role l) d Dm0 dB
      Hm δ δ Nl (Ms l G) (L l G))
    (_ : ∀ (l : Fin (4 : ℕ)), ∀ G ∉ gset, (∀ (p : (Ms l G).Key), (Ms l G).dvOf p + (Ms l
      G).zc.dim ≤ (2 : ℕ) * dB + (2 : ℕ)) ∧ (Ms l G).Bσ = (1 : ℝ) ∧ ∀ (V : ℤ × ℤ), (Ms l
      G).alive V = ∅)
    (_ : S.Dstar = fp.modeStarG Dm0 dB Hm δ Nl kD δ)
    (_ : ∀ (l : Fin (4 : ℕ)), ∀ G ∈ gset, (∀ (q : (Ms l G).Key), (Ms l G).dvOf q + (Ms l
      G).zc.dim ≤ (2 : ℕ) * dB + (2 : ℕ)) ∧ (Ms l G).Λ ≤ S.Dstar ∧ gaugeSqNorm (Ms l
      G).zc.dim (Ms l G).δc ≤ S.Dstar ∧ (2 : ℝ) * gaugeTail (Ms l G).zc.dim (Ms l G).δc
      / (2 : ℝ) ^ fp.Kstar Dm0 dB Hm δ Nl kD δ * S.Dstar ^ (300 : ℕ) ≤ (1 : ℝ) ∧ (∀ (m :
      (Ms l G).Md), S.Dstar⁻¹ ≤ (Ms l G).L.εM m) ∧ (∀ (V : ℤ × ℤ), (↑((Ms l G).alive
      V).card : ℝ) ≤ S.Dstar) ∧ ∀ (V : ℤ × ℤ), (↑(Finset.image (Ms l G).keyOf ((Ms l
      G).alive V)).card : ℝ) ≤ Nl)
    (hA6 : (6 : ℝ) ≤ S.A0),
  let qG : bf.Grp → ℕ :=
    fun (G : bf.Grp) => clearInt (bf.vtag (bf.grpCenter d G)).C
  ∀ (_ : ∀ (G : bf.Grp), (1 : ℕ) ≤ qG G ∧ qG G ≤ S.Q0)
    (Vl0 : ℝ)
    (_ : Vl0 = (24 : ℝ) * ((↑⌊(180 : ℝ) * (↑S.dmax : ℝ) * Real.log ((2 : ℝ) * S.Dm) / (1 /
      1024 : ℝ)⌋₊ : ℝ) + (1 : ℝ)) * (Real.exp (((6144 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) *
      ((1024 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) + (↑cc : ℝ) + (7 : ℝ)) + (4 : ℝ)) * ((1 : ℝ) +
      Real.log ((2 : ℝ) * (↑k : ℝ))) ^ (2 : ℕ)) + (2 : ℝ) * (1 : ℝ) / S.Dstar ^ (394 :
      ℕ)))
    (U : ℝ)
    (_ : U = max ((2 : ℝ) * (A.colBudget + (2 : ℝ)) * S.Dstar ^ (2 : ℕ)) √(TsideF A fp.P S.K
      (A.uslot p) ((2 : ℕ) ^ A.famFuel) ((2 : ℕ) * A.famFuel + (2 : ℕ)) (1 : ℝ) E cc (↑k
      : ℝ) (fun (_ : Fin (4 : ℕ)) => Vl0) ρ))
    (_ : (2 : ℝ) * (A.colBudget + (2 : ℝ)) * S.Dstar ^ (2 : ℕ) ≤ U)
    (_ : (0 : ℝ) < S.Dstar)
    (_ : (1 : ℝ) ≤ S.Dstar)
    (_ : (16 : ℝ) ≤ U)
    (_ : (0 : ℝ) < U)
    (MV : ℝ)
    (_ : MV = (↑AD.Mp : ℝ) * (↑A.famVtxBound : ℝ))
    (_ : (0 : ℝ) ≤ MV)
    (ε : ℝ)
    (_ : ε = (U ^ (3 : ℕ) * S.Dstar ^ (5 : ℕ) * Real.exp (↑k : ℝ) * ((1 : ℝ) + MV))⁻¹)
    (_ : (0 : ℝ) < ε)
    (_ : ε ≤ U)
    (_ : S.Dstar⁻¹ ≤ U)
    (_ : ∀ σ ∈ dyThr ε U S.Dstar, S.Dstar⁻¹ ≤ σ)
    (_ : ∀ (σ : ℝ), ε ≤ σ → σ ≤ U → (∃ (k : ℤ), σ = (2 : ℝ) ^ k) → S.Dstar⁻¹ ≤ σ → σ ∈ dyThr
      ε U S.Dstar)
    (_ : (↑(dyThr ε U S.Dstar).card : ℝ) ≤ Real.logb (2 : ℝ) U - Real.logb (2 : ℝ) ε + (3 :
      ℝ)),
  let Ts : Finset (ℕ × ℕ) :=
    Finset.range (Nat.log (2 : ℕ) ⌊S.Dstar⌋₊ + (1 : ℕ)) ×ˢ Finset.range (Nat.log (2 : ℕ)
      ⌊S.Dstar⌋₊ + (1 : ℕ))
  ∀ (_ : Ts = Finset.range (Nat.log (2 : ℕ) ⌊S.Dstar⌋₊ + (1 : ℕ)) ×ˢ Finset.range (Nat.log (2
      : ℕ) ⌊S.Dstar⌋₊ + (1 : ℕ))),
  let BN : ℕ :=
    ⌈(8 : ℝ) * A.colBudget + Nl⌉₊
  let τb : ℝ :=
    (1 : ℝ) / ((1 : ℝ) + (↑BN : ℝ) * A.colBudget ^ (2 : ℕ))
  ∀ (_ : (0 : ℝ) < τb)
    (_ : τb ≤ (1 : ℝ))
    (_ : τb * (↑BN : ℝ) * A.colBudget ^ (2 : ℕ) ≤ (1 : ℝ))
    (_ : Real.exp ((↑A.Dg : ℝ) * ((1 : ℝ) + Real.log A.Hsrc + Real.log τb⁻¹) ^ A.Dg) ≤ fp.Hed)
    (_ : ∀ I ∈ A.cells, dyadicGridCell A.G I.1 I.2 ⊆ Set.Icc (dyadicGridLeft A.G A.R.1 A.R.2)
      (dyadicGridLeft A.G A.R.1 A.R.2 + dyadicGridLength A.G A.R.1))
    (ρ₀ : Fin (4 : ℕ) → ↥gset → Fin A.fcd0)
    (zc : Fin (4 : ℕ) → ↥gset → bf.Vtx)
    (gsc : Fin (4 : ℕ) → ↥gset → ℤ)
    (_ : ∀ (l : Fin (4 : ℕ)) (G : ↥gset), (↑G : bf.Grp).2.1 = some (ρ₀ l G, zc l G, gsc l G))
    (_ : ∀ (l : Fin (4 : ℕ)) (G : ↥gset), fp.MainLiftExports l (AD.cat l) (↑G : bf.Grp)
      (Lf.role l) d Dm0 dB Hm (gsc l G) (L l (↑G : bf.Grp)) (Ms l (↑G : bf.Grp)).wave
      (Ms l (↑G : bf.Grp)).cellOf)
    (_ : ∀ (l : Fin (4 : ℕ)), fp.bbase (Lf.role l) + fp.P ≤ fp.Hmax)
    (_ : (4 : ℝ) ≤ Nl)
    (_ : ∀ (l : Fin (4 : ℕ)) (y : ℝ), (Finset.card ({q : ↥gset × (bf.Lab ⊕ Fin fp.Mc) | ∃ I ∈
      A.cells, (∃ (k' : ℕ), fp.Cert k' (↑q.1 : bf.Grp) I) ∧ ∃ (p_1 : Fin fp.P), y ∈
      dyadicGridCell A.G I.1 I.2 ∧ q.2 ∈ mainLabelsM A.G fp.Mc (bf.origCols l) (AD.cat
      l) I (fp.brank (Lf.role l)) (fp.bmask I (↑q.1 : bf.Grp) (Lf.role l) ((↑p_1 : ℕ) +
      (1 : ℕ))) d})) ≤ BN)
    (_ : ∀ (l : Fin (4 : ℕ)) (y : ℝ), ∑ G : ↥gset, (↑((Ms l (↑G : bf.Grp)).ptSet y).card : ℝ)
      ≤ S.Dstar)
    (_ : ∀ (l : Fin (4 : ℕ)) (G : ↥gset), (2 : ℝ) * ((↑S.Q0 : ℝ) * ((3 : ℝ) * ((Ms l (↑G :
      bf.Grp)).Bσ * (Ms l (↑G : bf.Grp)).Bσ) ^ (2 : ℕ))) ^ (2 : ℕ) ≤ (↑⌊S.Dstar⌋₊ : ℝ))
    (_ : fp.modeStar Dm0 dB Hm δ Nl kD ≤ S.Dstar)
    (_ : ∀ (l : Fin (4 : ℕ)), (↑(Lf.layers l).length : ℝ) ≤ (↑cc : ℝ) * (Real.log (↑k : ℝ) +
      (1 : ℝ)))
    (c : (l : Fin (4 : ℕ)) → (G : ↥gset) → ℤ → ℤ × ℤ → (Ms l (↑G : bf.Grp)).Md → ℂ)
    (_ : ∀ (l : Fin (4 : ℕ)) (G : ↥gset), ∀ b ∈ Finset.image (fun (β : ℕ) => A.R.1 + (↑(S.K *
      β) : ℤ)) (Finset.range (A.treeDepth + (1 : ℕ))), ∀ J ∈ fp.retainedV (↑G : bf.Grp)
      b S.K, ∑ m ∈ (Ms l (↑G : bf.Grp)).alive (ancAt A.G J (b - (4 : ℤ) * (↑S.K : ℤ))),
      ‖c l G b J m‖ ^ (2 : ℕ) ≤ (4 : ℝ) * S.Dstar ^ (2 : ℕ) * (1 : ℝ))
    (_ : ∀ (l : Fin (4 : ℕ)), ∑ G : ↥gset, ∑ b ∈ Finset.image (fun (β : ℕ) => A.R.1 + (↑(S.K
      * β) : ℤ)) (Finset.range (A.treeDepth + (1 : ℕ))), ‖(Ms l (↑G : bf.Grp)).blockSide
      (S.withQ0 (qG (↑G : bf.Grp))) hA6 (S.sideParams (1 / 1024 : ℝ)) b (fp.retainedV
      (↑G : bf.Grp) b S.K) (c l G b)‖ ^ (2 : ℕ) ≤ (24 : ℝ) * ((↑⌊(180 : ℝ) * (↑S.dmax :
      ℝ) * Real.log ((2 : ℝ) * S.Dm) / (1 / 1024 : ℝ)⌋₊ : ℝ) + (1 : ℝ)) * (Real.exp
      (((6144 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) * ((1024 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) + (↑cc
      : ℝ) + (7 : ℝ)) + (4 : ℝ)) * ((1 : ℝ) + Real.log ((2 : ℝ) * (↑k : ℝ))) ^ (2 : ℕ))
      + (2 : ℝ) * (1 : ℝ) / S.Dstar ^ (394 : ℕ)) * dyadicGridLength A.G A.R.1)
    (Rr : (l : Fin (4 : ℕ)) → (h : ℕ) → ℕ × ℕ → (G : ↥gset) → (Ms l (↑G : bf.Grp)).RepClass
      (S.withQ0 (qG (↑G : bf.Grp))) hA6 (S.sideParams (1 / 1024 : ℝ)) (10 : ℕ) h)
    (_ : ∀ (l : Fin (4 : ℕ)), ∀ h ≤ S.Jstar, ∀ (t : ℕ × ℕ) (G : ↥gset), (Rr l h t G).Nd = {c
      ∈ (Ms l (↑G : bf.Grp)).succNodes (S.withQ0 (qG (↑G : bf.Grp))) hA6 (S.sideParams
      (1 / 1024 : ℝ)) (fp.retainedPairs (↑G : bf.Grp) (Finset.image (fun (β : ℕ) =>
      A.R.1 + (↑(S.K * β) : ℤ)) (Finset.range (A.treeDepth + (1 : ℕ)))) S.K) h | (Ms l
      (↑G : bf.Grp)).nodeType1 (S.withQ0 (qG (↑G : bf.Grp))) hA6 (10 : ℕ) h c = t.1 ∧
      (Ms l (↑G : bf.Grp)).nodeType2 (S.withQ0 (qG (↑G : bf.Grp))) hA6 (10 : ℕ) h c =
      t.2})
    (Cut : Fin (4 : ℕ) → Finset (ℤ × ℤ))
    (_ : ∀ (l : Fin (4 : ℕ)), dyadicRootLength A.G (Cut l) ≤ ρ * dyadicGridLength A.G A.R.1)
    (_ : ∀ (l : Fin (4 : ℕ)) (y : ℝ), ∀ h ∈ Finset.range (S.Jstar + (1 : ℕ)), ∀ t ∈ Ts, ∀ σ ∈
      dyThr ε U S.Dstar, ∑ G : ↥gset, (↑(Finset.image (fun (p : (ℤ × ℤ) × ℤ × (ℤ × ℤ) ×
      (Ms l (↑G : bf.Grp)).Md) => (Rr l h t G).rep p.2) ({p ∈ fp.useInst (↑G : bf.Grp)
      S.K (Rr l h t G).Nd | (∀ e ∈ Cut l, ¬dyadicGridCell A.G p.1.1 p.1.2 ⊆
      dyadicGridCell A.G e.1 e.2) ∧ y ∈ dyadicGridCell A.G p.1.1 p.1.2 ∧ σ ^ (2 : ℕ) ≤
      (Ms l (↑G : bf.Grp)).nodeSize (S.withQ0 (qG (↑G : bf.Grp))) hA6 (S.sideParams (1 /
      1024 : ℝ)) (c l G) h p})).card : ℝ) ≤ min S.Dstar ((24 : ℝ) * ((2 : ℝ) * Real.exp
      (((6144 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) * ((1024 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) + (↑cc
      : ℝ) + (7 : ℝ)) + (4 : ℝ)) * ((1 : ℝ) + Real.log ((2 : ℝ) * (↑k : ℝ))) ^ (2 : ℕ))
      + (2 : ℝ) * (↑S.K : ℝ) * ((24 : ℝ) * ((↑⌊(180 : ℝ) * (↑S.dmax : ℝ) * Real.log ((2
      : ℝ) * S.Dm) / (1 / 1024 : ℝ)⌋₊ : ℝ) + (1 : ℝ)) * (Real.exp (((6144 : ℝ) * ((↑cc :
      ℝ) + (1 : ℝ)) * ((1024 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) + (↑cc : ℝ) + (7 : ℝ)) + (4 :
      ℝ)) * ((1 : ℝ) + Real.log ((2 : ℝ) * (↑k : ℝ))) ^ (2 : ℕ)) + (2 : ℝ) * (1 : ℝ) /
      S.Dstar ^ (394 : ℕ)))) * (↑(Finset.range (S.Jstar + (1 : ℕ)) ×ˢ Ts ×ˢ dyThr ε U
      S.Dstar).card : ℝ) / (ρ * σ ^ (2 : ℕ)))),
  let cf : (l : Fin (4 : ℕ)) → (G : bf.Grp) → ℤ → ℤ × ℤ → (Ms l G).Md → ℂ :=
    fun (l : Fin (4 : ℕ)) (G : bf.Grp) => if hG : G ∈ gset then c l ⟨G, hG⟩ else fun _ _
      _ => (0 : ℂ)
  let D₀ : fp.SideInput :=
    { cat := AD.cat, mbs := mbs, Lf := Lf, u := A.uslot p, S := S, hA := hA6,
      SP := S.sideParams (1 / 1024 : ℝ), hK := hK1,
      n := Fintype.card (bf.Lab ⊕ Fin fp.Mc), Ms := Ms, c := cf }
  let gE : ℤ × ℤ → Fin A.famVtxBound → bf.Grp :=
    fun (I : ℤ × ℤ) (i : Fin A.famVtxBound) => if h : (↑i : ℕ) < (gs I).card then
      (↑(((gs I).equivFin.symm : Fin (gs I).card → ↥(gs I)) ⟨(↑i : ℕ), h⟩) : bf.Grp)
      else default
  ∀ (_ : ∀ (I : ℤ × ℤ), ∀ G ∈ gs I, ∃ (i : Fin A.famVtxBound), gE I i = G)
    (hcat : Fin (4 : ℕ) → List (CatCol bf.Vtx))
    (_ : ∀ (l : Fin (4 : ℕ)), ∀ d ∈ hcat l, d.birth ∈ AD.Tc ∧ d.rank = fp.Lc + (5 : ℕ) ∧ (∃
      (M : fp.MaskName d.birth), fp.maskOf d.birth M d.tag) ∧ ∃ R ∈ residueBox (bf.vtag
      d.tag).dim (9 : ℕ), ∃ (γ : ℝ), d = templateCol (bf.vtag d.tag) l R γ d.birth
      d.rank d.tag)
    (hmbb : ∀ (l : Fin (4 : ℕ)), ∀ e ∈ AD.cat l ++ hcat l, e.birth ∈ A.cells)
    (hmbT : ∀ (l : Fin (4 : ℕ)) (y : ℝ), (8 : ℝ) * A.colBudget + (↑(bf.tmplPath (AD.cat l ++
      hcat l) y) : ℝ) ≤ (8 : ℝ) * A.colBudget + ((1 : ℝ) + (↑AD.Mp : ℝ)) * Nl),
  let mb' : (l : Fin (4 : ℕ)) → bf.MainBudget (AD.cat l ++ hcat l) :=
    fun l =>
        { hb := hmbb l, B := 8 * A.colBudget + (1 + AD.Mp) * Nl, hTp := hmbT l }
  let D : fp.SideInput :=
    D₀.appendCat hcat mb'
  ∀ (_ : ∀ (l : Fin (4 : ℕ)), ∀ e ∈ hcat l, fp.hrank ≤ e.rank)
    (_ : ∀ (l : Fin (4 : ℕ)), D₀.Lf.role l ≤ (4 : ℕ))
    (_ : ∀ (l : Fin (4 : ℕ)), ∀ e ∈ hcat l, bf.occAvail (↑e.tag.2 : ℤ × ℤ) e.tag.1),
  let S1 : Finset (ℤ × ℤ) :=
    {I ∈ S0 | ∀ (j : Fin (4 : ℕ)), ∀ e ∈ Cut j, ¬dyadicGridCell A.G I.1 I.2 ⊆
      dyadicGridCell A.G e.1 e.2}
  ∀ (_ : S1 ⊆ S0)
    (_ : S1 ⊆ A.cells)
    (_ : ∀ I ∈ A.cells, ((I.1 - A.R.1) / (↑S.K : ℤ)).toNat < A.treeDepth + (1 : ℕ))
    (_ : ∀ I ∈ A.cells, A.blkStart S.K I.1 ∈ Finset.image (fun (β : ℕ) => A.R.1 + (↑(S.K * β)
      : ℤ)) (Finset.range (A.treeDepth + (1 : ℕ))))
    (_ : ∀ I ∈ S1, ∀ (l : Fin (4 : ℕ)), D.u ≠ some l → ∀ (w : fp.TestName I Unit), fp.MainRk
      w → (fp.testOf l I (fun (_ : Unit) => bf.basicIn fp.Mc l I) w).Pass A.G
      (bf.origCols l) I A.csrc A.Hsrc bf.vtag (A.w I) (catThreshold A.famVtxBound AD.τ₃
      AD.n (fp.testOf l I (fun (_ : Unit) => bf.basicIn fp.Mc l I) w).r) fp.mH (D.cat l))
    (_ : ∀ I ∈ S1, ∀ (a : Fin (4 : ℕ)) (w : fp.HelperName I (Fin A.famVtxBound)),
      (fp.helperOf a I (fun (i : Fin A.famVtxBound) => (D.toLeafQ qG).sv a (gE I i) I)
      w).Pass A.G (bf.origCols a) I A.csrc A.Hsrc bf.vtag (A.w I) (catThreshold
      A.famVtxBound AD.τ₃ AD.n (fp.Lc + (5 : ℕ))) fp.mH (D.cat a))
    (_ : ∀ (R : ℕ), (1 : ℕ) ≤ R → R ≤ fp.Lc + (4 : ℕ) → catThreshold A.famVtxBound AD.τ₃ AD.n
      R * (A.colBudget * √(AD.n (R - (1 : ℕ)))) ≤ AD.τ₃)
    (_ : catThreshold A.famVtxBound AD.τ₃ AD.n (fp.Lc + (5 : ℕ)) * (A.colBudget * √(AD.n
      (fp.Lc + (4 : ℕ)))) ≤ AD.τ₃)
    (_ : ∀ (R : ℕ), (0 : ℝ) ≤ catThreshold A.famVtxBound AD.τ₃ AD.n R)
    (_ : ∀ I ∈ S1, ∀ (l : Fin (4 : ℕ)), ∀ r ≤ fp.Lc + (4 : ℕ), ∀ (M : bf.Vtx → Prop),
      (↑(mainLabelsM A.G fp.Mc (bf.origCols l) (D.cat l) I r M d).card : ℝ) ≤ AD.n r),
  let NH : ℝ :=
    (2 : ℝ) * A.colBudget + ((1 : ℝ) + (↑AD.Mp : ℝ)) * Nl
  ∀ (_ : ∀ I ∈ S1, ∀ (a : Fin (4 : ℕ)) (M : bf.Vtx → Prop), (↑(mainLabelsM A.G fp.Mc
      (bf.origCols a) (D.cat a) I (fp.Lc + (5 : ℕ)) M d).card : ℝ) ≤ NH),
  let τ₂ : ℝ :=
    AD.τ₃ / ((1 : ℝ) + A.colBudget * √(AD.n (fp.Lc + (4 : ℕ))) * (A.colBudget * √NH))
  ∀ (_ : (0 : ℝ) < τ₂)
    (_ : τ₂ ≤ (1 : ℝ))
    (_ : τ₂ * (A.colBudget * √(AD.n (fp.Lc + (4 : ℕ))) * (A.colBudget * √NH)) ≤ AD.τ₃)
    (_ : Real.exp ((↑A.Dg : ℝ) * ((1 : ℝ) + Real.log A.Hsrc + Real.log τ₂⁻¹) ^ A.Dg) ≤ fp.Hed),
  let Nb : ℕ :=
    Nat.log (2 : ℕ) S.K + (1 : ℕ)
  ∀ (_ : Nb = Nat.log (2 : ℕ) S.K + (1 : ℕ))
    (_ : S.K ≤ (2 : ℕ) ^ Nb)
    (_ : (0 : ℝ) < dyadicGridLength A.G A.R.1)
    (_ : (0 : ℝ) ≤ Vl0),
  let Os : Finset (Fin (4 : ℕ) × Fin (4 : ℕ) × ℕ × ℕ × ℕ × ℕ) :=
    FamParams.SideLeafM.nOs ((2 : ℕ) ^ A.famFuel) ((2 : ℕ) * A.famFuel + (2 : ℕ))
  ∀ (_ : Os = FamParams.SideLeafM.nOs ((2 : ℕ) ^ A.famFuel) ((2 : ℕ) * A.famFuel + (2 : ℕ))),
  let Cjg : ℝ :=
    ((↑((2 : ℕ) * A.famFuel + (2 : ℕ)) : ℝ) + (1 : ℝ)) ^ (2 : ℕ) * Real.exp ((2 : ℝ) *
      ((1024 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) * ((1024 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) + (↑cc :
      ℝ) + (7 : ℝ)) * ((1 : ℝ) + Real.log ((2 : ℝ) * (↑k : ℝ))) ^ (2 : ℕ)))
  ∀ (_ : Cjg = ((↑((2 : ℕ) * A.famFuel + (2 : ℕ)) : ℝ) + (1 : ℝ)) ^ (2 : ℕ) * Real.exp ((2 :
      ℝ) * ((1024 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) * ((1024 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) +
      (↑cc : ℝ) + (7 : ℝ)) * ((1 : ℝ) + Real.log ((2 : ℝ) * (↑k : ℝ))) ^ (2 : ℕ)))),
  let Γa : Fin (4 : ℕ) → ℝ :=
    fun (_ : Fin (4 : ℕ)) => (↑Os.card : ℝ) * ((↑Nb : ℝ) * ((2 : ℝ) * FamParams.capV A
      cc (↑k : ℝ) + (16 : ℝ) * (Cjg * FamParams.SideInput.sideB0 A cc (↑k : ℝ) Vl0) +
      (16 : ℝ) * ((↑Nb : ℝ) * (Cjg * ((↑Nb : ℝ) * FamParams.capV A cc (↑k : ℝ))))) +
      FamParams.SideInput.sideB0 A cc (↑k : ℝ) Vl0) / dyadicGridLength A.G A.R.1
  ∀ (_ : Γa = fun (_ : Fin (4 : ℕ)) => (↑Os.card : ℝ) * ((↑Nb : ℝ) * ((2 : ℝ) *
      FamParams.capV A cc (↑k : ℝ) + (16 : ℝ) * (Cjg * FamParams.SideInput.sideB0 A cc
      (↑k : ℝ) Vl0) + (16 : ℝ) * ((↑Nb : ℝ) * (Cjg * ((↑Nb : ℝ) * FamParams.capV A cc
      (↑k : ℝ))))) + FamParams.SideInput.sideB0 A cc (↑k : ℝ) Vl0) / dyadicGridLength
      A.G A.R.1)
    (_ : ∀ (a : Fin (4 : ℕ)), D.u ≠ some a → fp.stackEA Os (D.cat a) (D.mbs a) (D.toLeafQ
      qG).Dpre Nb (FamParams.capV A cc (↑k : ℝ)) (FamParams.SideInput.sideB0 A cc (↑k :
      ℝ) ((fun (_ : Fin (4 : ℕ)) => Vl0) a)) ≤ ((↑fp.P : ℝ) + (2 : ℝ)) * Γa a *
      dyadicGridLength A.G A.R.1),
  let Γb : Fin (4 : ℕ) → ℝ :=
    fun (_ : Fin (4 : ℕ)) => (↑Os.card : ℝ) * ((↑Nb : ℝ) * FamParams.capV A cc (↑k : ℝ)
      + FamParams.SideInput.sideB0 A cc (↑k : ℝ) Vl0) / dyadicGridLength A.G A.R.1
  ∀ (_ : Γb = fun (_ : Fin (4 : ℕ)) => (↑Os.card : ℝ) * ((↑Nb : ℝ) * FamParams.capV A cc (↑k
      : ℝ) + FamParams.SideInput.sideB0 A cc (↑k : ℝ) Vl0) / dyadicGridLength A.G A.R.1)
    (_ : ∀ (b : Fin (4 : ℕ)), D.u ≠ some b → (↑Os.card : ℝ) * ((↑Nb : ℝ) * FamParams.capV A
      cc (↑k : ℝ) + FamParams.SideInput.sideB0 A cc (↑k : ℝ) ((fun (_ : Fin (4 : ℕ)) =>
      Vl0) b)) ≤ Γb b * dyadicGridLength A.G A.R.1),
  let ΓU : ℝ :=
    (↑Os.card : ℝ) * ((2 : ℝ) * ((4 : ℝ) * E * dyadicGridLength A.G A.R.1)) /
      dyadicGridLength A.G A.R.1
  ∀ (_ : ΓU = (↑Os.card : ℝ) * ((2 : ℝ) * ((4 : ℝ) * E * dyadicGridLength A.G A.R.1)) /
      dyadicGridLength A.G A.R.1)
    (_ : (↑Os.card : ℝ) * ((2 : ℝ) * ((4 : ℝ) * E * dyadicGridLength A.G A.R.1)) ≤ ΓU *
      dyadicGridLength A.G A.R.1)
    (_ : ∀ I ∈ S1, ∀ G ∈ gs I, ∀ (l : Fin (4 : ℕ)), D.u ≠ some l → (D.withQ0 (qG G)).RepAt L
      l G I)
    (Ee : ℝ)
    (_ : ∑ I ∈ S1, ∑ G ∈ gs I, ∑ l : Fin (4 : ℕ), ‖(D₀.withQ0 (qG G)).errAt L l G I‖ ^ (2 :
      ℕ) ≤ Ee)
    (_ : Ee ≤ ((8 : ℝ) * (↑dB : ℝ) * δ + (2 : ℝ) * δ ^ (2 : ℕ)) * ((4 : ℝ) * Nl * A.colBudget
      ^ (2 : ℕ) * (1 : ℝ)) * (↑((4 : ℕ) * (AD.Mp * A.famVtxBound)) : ℝ) *
      dyadicGridLength A.G A.R.1)
    (_ : ∑ I ∈ S1, ∑ G ∈ gs I, ∑ l : Fin (4 : ℕ), ‖(D.withQ0 (qG G)).errAt L l G I‖ ^ (2 : ℕ)
      ≤ Ee)
    (_ : ∑ I ∈ S1, dyadicGridLength A.G I.1 * (↑(gs I).card : ℝ) ≤ (↑(AD.Mp * A.famVtxBound)
      : ℝ) * dyadicGridLength A.G A.R.1),
  ∃ (F : Fin (6 : ℕ) → Finset (ℤ × ℤ)), (∀ (i : Fin (6 : ℕ)), ∀ c ∈ F i,
    dyadicGridCell A.G c.1 c.2 ⊆ dyadicGridCell A.G A.R.1 A.R.2) ∧ (∀ (i : Fin (6 :
    ℕ)), dyadicRootLength A.G (F i) ≤ (2 : ℝ) * ρ * dyadicGridLength A.G A.R.1) ∧ ∀ cs
    ⊆ AD.Tc, (∀ I ∈ cs, ¬∃ c ∈ fp.failRoots, dyadicGridCell A.G I.1 I.2 ⊆
    dyadicGridCell A.G c.1 c.2) → (∀ I ∈ cs, ∀ (i : Fin (6 : ℕ)), ∀ e ∈ F i,
    ¬dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G e.1 e.2) → ∑ I ∈ cs,
    dyadicGridLength A.G I.1 * min A.η ‖∑ G ∈ fp.groupsAt I ks, (fp.Λc I : (Fin (4 :
    ℕ) → ↥(ColumnL2 (bf.Lab ⊕ Fin fp.Mc))) → ℂ) fun (l : Fin (4 : ℕ)) => (fp.ballFilt
    l (AD.cat l) I G (Lf.role l) : ↥(ColumnL2 (bf.Lab ⊕ Fin fp.Mc)) → ↥(ColumnL2
    (bf.Lab ⊕ Fin fp.Mc))) (fp.inputL AD.cat I (bf.patIn fp.Mc p I) Lf.layers l)‖ ≤
    leafBnd Cl kD fp.P k cc A.η η₀ AD.τ₃ δ (finiteDepthConstant κ q Nd) (nbCM κ hq2
    hq3 + nbCUM κ hq2 hq3) q (dyadicGridLength A.G A.R.1)


open scoped Classical in
private def LeafEstimateStage4Statement : Prop :=
  ∀ (κ : LocalKernelClass)
    (c₀ : ℕ)
    (cc : ℕ)
    (_ : (1 : ℕ) ≤ cc)
    (Dm0 : ℕ)
    (Msch : ℝ)
    (_ : (0 : ℝ) < Msch)
    (Cg : ℕ)
    (_ : ∀ {κ : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ c₀} {bf : A.BasicFamilies} (fp
      : bf.FamParams) (dB : ℕ) {H δc N k δ : ℝ}, (1 : ℝ) ≤ k → (↑fp.Lc : ℝ) + (6 : ℝ) ≤
      k ^ (cc + (6 : ℕ)) → (↑fp.Hmax : ℝ) + (1 : ℝ) ≤ (k * (↑fp.P : ℝ)) ^ (cc + (6 : ℕ))
      → (↑dB : ℝ) ≤ k ^ (cc + (6 : ℕ)) → (2 : ℝ) ≤ fp.Hed → Real.log fp.Hed ≤ k ^ (cc +
      (6 : ℕ)) → (1 : ℝ) ≤ H → Real.log H ≤ k ^ (cc + (6 : ℕ)) → (0 : ℝ) < δc → δc⁻¹ ≤
      Real.exp (k ^ (cc + (6 : ℕ))) → (0 : ℝ) ≤ N → N ≤ Real.exp (k ^ (cc + (6 : ℕ))) →
      A.colBudget ≤ Real.exp (k ^ (cc + (6 : ℕ))) → (0 : ℝ) < δ → δ⁻¹ ≤ Real.exp (k ^
      (cc + (6 : ℕ))) → Real.log (fp.modeStarG Dm0 dB H δc N k δ) ≤ (↑Cg : ℝ) * (k *
      (↑fp.P : ℝ)) ^ Cg ∧ Real.log ((2 : ℝ) ^ (fp.Kstar Dm0 dB H δc N k δ + (1 : ℕ))) ≤
      (↑Cg : ℝ) * (k * (↑fp.P : ℝ)) ^ Cg)
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
    (eΛ : ℕ)
    (CM1 : ℕ)
    (t3 : ℕ)
    (Cb : ℕ)
    (Cl : ℕ)
    (_ : g = (8192 : ℕ) * (cc + (1 : ℕ)) * ((1024 : ℕ) * (cc + (1 : ℕ)) + cc + (7 : ℕ)) + cc
      ^ (2 : ℕ) + (8 : ℕ) ∧ cT = (10 : ℝ) ^ (22 : ℕ) * ((1 : ℝ) +
      localFormUniformConstant κ) ^ (2 : ℕ) ∧ cL = (159 : ℝ) + (32 : ℝ) * (↑g : ℝ) + (8
      : ℝ) * Real.log cT ∧ cK = ((1 : ℝ) + (7 : ℝ) * (10 : ℝ) ^ (9 : ℕ) + cT) * (cL + (2
      : ℝ)) ∧ cMc = (C4c κ + (4 : ℝ) * C3c κ) * cL ^ (4 : ℕ) * cK ^ (2 : ℕ) ∧ cm =
      (196608 : ℝ) * cT + (83 : ℝ) * ((1 : ℝ) + (81 : ℝ) * localFormUniformConstant κ *
      ((30000 : ℝ) + √cT)) * ((1 : ℝ) + cT) ^ (3 : ℕ) + cMc ∧ ce = (6642 : ℝ) *
      localFormUniformConstant κ * ((60000 : ℝ) + √cT) ^ (3 : ℕ) * (288 : ℝ) + (9 : ℝ) *
      ((16 : ℝ) * fourErrC κ (3 : ℕ) + (648 : ℝ) * threeErrC κ (3 : ℕ) (1 : ℕ) + (324 :
      ℝ) * threeErrC κ (3 : ℕ) (1 : ℕ) * √cT) ∧ ce2 = K1c * ((2 : ℝ) * fourKC κ (3 : ℕ)
      * (12 : ℝ) ^ (4 : ℕ)) + (4 : ℝ) * (K1c * ((8 : ℝ) * entryCU κ (3 : ℕ) (1 : ℕ) * (2
      : ℝ) ^ ((1 : ℕ) + (4 : ℕ)) * (12 : ℝ) ^ (3 : ℕ))) * (501 : ℝ) ∧ cQ = (65536 : ℝ) *
      ((8 : ℝ) + (80 : ℝ) * (9 : ℝ) ^ cc * (↑cc : ℝ)) * ((80 : ℝ) * (9 : ℝ) ^ cc * (↑cc
      : ℝ)) * ((4 : ℝ) * (↑cc : ℝ) ^ (2 : ℕ)) * ((17 : ℝ) * (10 : ℝ) ^ (7 : ℕ)) ∧ CΛ =
      (2 : ℕ) * Cg + (12 : ℕ) ∧ eΛ = Cg + (3 : ℕ) * cc ∧ CM1 = (⌈Msch⌉₊ + (1 : ℕ)) * CΛ
      ^ (16 : ℕ) ∧ t3 = (3 : ℕ) ^ cc ∧ Cb = CM1 + (501 : ℕ) * Cg + t3 + (2 : ℕ) * cc +
      (20 : ℕ) + (16 : ℕ) * eΛ ∧ Cl = ⌈cm * (↑Cb : ℝ) ^ (59 : ℕ) + ce * (↑Cb : ℝ) ^ (18
      : ℕ) + ce2 + (3 : ℝ) * (10 : ℝ) ^ (11 : ℕ) * cQ⌉₊ + (59 : ℕ) * Cb + (4 : ℕ) * g +
      (8 : ℕ) * cc + (8 : ℕ))
    (A : ActiveSetup κ c₀)
    (bf : A.BasicFamilies)
    (k : ℕ)
    (η₀ : ℝ)
    (E : ℝ)
    (_ : A.AncClosed)
    (_ : ∀ I ∈ A.cells, ∀ (s s' : Fin (4 : ℕ)), s ≠ s' → PairSmall (dyadicGridLeft A.G I.1
      I.2) (dyadicGridLength A.G I.1) (A.w I) s s' (A.Y I s) (A.Y I s') ((2 : ℝ) * η₀))
    (_ : A.SubRootProps η₀ E)
    (_ : A.S = (2 : ℝ))
    (_ : A.η = (4 : ℝ) * η₀)
    (_ : (0 : ℝ) < η₀)
    (_ : A.cells.Nonempty)
    (q : ℝ)
    (hq2 : (2 : ℝ) < q)
    (hq3 : q < (3 : ℝ))
    (Nd : ℕ)
    (_ : A.DepthWin Nd)
    (p : Fin (3 : ℕ))
    (AD : bf.AttemptData p)
    (d : bf.Vtx)
    (s : ℕ)
    (δ : ℝ)
    (ρ : ℝ)
    (kD : ℝ)
    (_ : (0 : ℝ) < δ)
    (_ : δ ≤ (1 / 8 : ℝ))
    (_ : (0 : ℝ) < ρ)
    (_ : ρ < (1 : ℝ))
    (_ : Real.log ((2 : ℝ) * A.colBudget) ≤ (↑k : ℝ) ^ cc)
    (_ : (↑((2 : ℕ) * A.famFuel + (2 : ℕ)) : ℝ) ≤ (↑cc : ℝ) * (Real.log (↑k : ℝ) + (1 : ℝ)))
    (_ : (1 : ℝ) ≤ (↑k : ℝ)),
  let fp : bf.FamParams :=
    AD.fp
  let dB : ℕ :=
    A.dBnd
  ∀ (_ : (↑fp.Lc : ℝ) + (6 : ℝ) ≤ (↑k : ℝ) ^ cc ∧ (↑fp.Hmax : ℝ) + (1 : ℝ) ≤ ((↑k : ℝ) *
      (↑fp.P : ℝ)) ^ cc ∧ (↑dB : ℝ) ≤ (↑k : ℝ) ^ cc ∧ Real.log fp.Hed ≤ (↑k : ℝ) ^ cc ∧
      Real.log A.Hsrc ≤ (↑k : ℝ) ^ cc ∧ Real.log (max A.H padW) ≤ (↑k : ℝ) ^ cc ∧ δ⁻¹ ≤
      Real.exp kD ∧ E ≤ (↑k : ℝ) ^ cc ∧ ρ⁻¹ ≤ (↑k : ℝ) ^ cc ∧ (2 : ℝ) + Real.log
      bumpConst + (100 : ℝ) ≤ (↑k : ℝ) ∧ (↑k : ℝ) ^ cc ≤ kD ∧ (2 : ℝ) ≤ (↑k : ℝ) ∧ (0 :
      ℝ) ≤ Real.log bumpConst)
    (_ : (8 : ℝ) * (↑dB : ℝ) * δ ≤ (1 : ℝ)),
  let Nl : ℝ :=
    AD.n (fp.Lc + (5 : ℕ))
  ∀ (_ : Real.log ((2 : ℝ) * ((8 : ℝ) * A.colBudget + ((1 : ℝ) + (↑AD.Mp : ℝ)) * Nl)) ≤ (↑k :
      ℝ) ^ cc)
    (_ : (2 : ℝ) ≤ A.colBudget)
    (_ : Monotone AD.n)
    (hNl0 : (0 : ℝ) ≤ Nl),
  let Hm : ℝ :=
    max (max A.Hsrc (Real.exp (↑dB : ℝ))) (max ((5832 : ℝ) * max A.H padW ^ (4 : ℕ))
      ((↑dB : ℝ) * (bumpConst * (8 : ℝ) ^ (32 : ℕ) * ((2 : ℝ) / δ))))
  ∀ (_ : (1 : ℝ) ≤ Hm)
    (_ : ∀ (w : bf.Vtx), (bf.vtag w).dim ≤ dB)
    (_ : ∀ (w : bf.Vtx) (a c : Fin (bf.vtag w).dim), (↑(rationalHeight ((bf.vtag w).C a c)) :
      ℝ) ≤ fp.Hed)
    (S : ModeSchedule)
    (_ : S.dmax = (2 : ℕ) * dB + (2 : ℕ))
    (_ : S.Dm = max (2 : ℝ) Nl)
    (_ : S.Valid (340 : ℕ) (5 : ℕ) (4 : ℕ) (600 : ℕ) (1 / 1024 : ℝ) (packetW S.dmax S.H))
    (_ : (2 : ℕ) ≤ S.dmax)
    (_ : (↑S.dmax : ℝ) ≤ S.Dstar)
    (_ : (2 : ℝ) ≤ S.Dstar)
    (_ : (2 : ℝ) ≤ S.Bstar)
    (_ : (1 : ℕ) ≤ S.Q0)
    (_ : (↑S.Q0 : ℝ) * (2 : ℝ) ^ (fp.Kstar Dm0 dB Hm δ Nl kD δ + (1 : ℕ)) ≤ S.Bstar)
    (_ : Real.log S.H ≤ Msch * ((↑((2 : ℕ) * dB + (2 : ℕ)) : ℝ) + Real.log (fp.modeStarG Dm0
      dB Hm δ Nl kD δ) + Real.log (fp.Bst Dm0 dB Hm δ Nl kD δ) + Real.log (max (2 : ℝ)
      Nl) + Real.log (↑(fp.Q0bd dB) : ℝ) + (1 : ℝ)) ^ (12 : ℕ))
    (_ : (↑S.K : ℝ) ≤ Msch * ((↑((2 : ℕ) * dB + (2 : ℕ)) : ℝ) + Real.log (fp.modeStarG Dm0 dB
      Hm δ Nl kD δ) + Real.log (fp.Bst Dm0 dB Hm δ Nl kD δ) + Real.log (max (2 : ℝ) Nl)
      + Real.log (↑(fp.Q0bd dB) : ℝ) + (1 : ℝ)) ^ (16 : ℕ))
    (hK1 : (1 : ℕ) ≤ S.K),
  let Lf : SearchLeaf :=
    leafAt A.famFuel fp.Lc (A.basicSlot p) s
  let ks : ℕ :=
    Lf.k
  let S0 : Finset (ℤ × ℤ) :=
    {I ∈ AD.Tc | ¬∃ c ∈ fp.failRoots, dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G
      c.1 c.2}
  ∀ (_ : S0 ⊆ AD.Tc),
  let gs : ℤ × ℤ → Finset bf.Grp :=
    fun (I : ℤ × ℤ) => fp.groupsAt I ks
  let gset : Finset bf.Grp :=
    S0.biUnion gs
  ∀ (_ : ∀ I ∈ S0, ∀ G ∈ gs I, fp.Cert ks G I ∧ fp.ActualUse G I),
  let U_1 : Fin (4 : ℕ) → bf.Grp → Finset (ℤ × ℤ) :=
    fun (_ : Fin (4 : ℕ)) (G : bf.Grp) => {I ∈ S0 | G ∈ gs I}
  ∀ (hlenMc : ∀ (l : Fin (4 : ℕ)), (AD.cat l).length ≤ fp.Mc),
  let mbs : (l : Fin (4 : ℕ)) → bf.MainBudget (AD.cat l) :=
    fun l => MainBudget.ofCounts bf fp.Mc (AD.cat l) (hlenMc l) l (fun e he => AD.hTc
      (AD.hT l e he).1) (fun e he => (AD.hT l e he).2.1) hNl0 (fun I _ => AD.hlab l I _
      le_rfl)
  ∀ (Ms : Fin (4 : ℕ) → bf.Grp → ModeSystem A.G (Fintype.card (bf.Lab ⊕ Fin fp.Mc)))
    (L : (l : Fin (4 : ℕ)) → (G : bf.Grp) → LiftData (bf.Lab ⊕ Fin fp.Mc) (Ms l G).Md)
    (_ : ∀ (l : Fin (4 : ℕ)), ∀ G ∈ gset, fp.ModeExports l (AD.cat l) G (Lf.role l) d Dm0 dB
      Hm δ δ Nl (Ms l G) (L l G))
    (_ : ∀ (l : Fin (4 : ℕ)), ∀ G ∉ gset, (∀ (p : (Ms l G).Key), (Ms l G).dvOf p + (Ms l
      G).zc.dim ≤ (2 : ℕ) * dB + (2 : ℕ)) ∧ (Ms l G).Bσ = (1 : ℝ) ∧ ∀ (V : ℤ × ℤ), (Ms l
      G).alive V = ∅)
    (_ : PLift (∑ l : Fin (4 : ℕ), ∑ G ∈ gset, ∑ I ∈ U_1 l G, ∫ (y : ℝ) in dyadicGridCell A.G
      I.1 I.2, ‖((↑(↑(fp.physError (Ms l G) (L l G) l (AD.cat l) (mbs l) G (Lf.role l)
      (Lf.layers l) S.K (A.blkStart S.K I.1)) : ℝ →ₘ[volume] ColumnHilbert (bf.Lab ⊕ Fin
      fp.Mc)) : ℝ → ColumnHilbert (bf.Lab ⊕ Fin fp.Mc)) y).ofLp none‖ ^ (2 : ℕ) ≤ ((8 :
      ℝ) * (↑dB : ℝ) * δ + (2 : ℝ) * δ ^ (2 : ℕ)) * ((4 : ℝ) * Nl * A.colBudget ^ (2 :
      ℕ) * (1 : ℝ)) * (↑((4 : ℕ) * (AD.Mp * A.famVtxBound)) : ℝ) * dyadicGridLength A.G
      A.R.1))
    (_ : S.Dstar = fp.modeStarG Dm0 dB Hm δ Nl kD δ)
    (_ : ∀ (l : Fin (4 : ℕ)), ∀ G ∈ gset, (∀ (q : (Ms l G).Key), (Ms l G).dvOf q + (Ms l
      G).zc.dim ≤ (2 : ℕ) * dB + (2 : ℕ)) ∧ (Ms l G).Λ ≤ S.Dstar ∧ gaugeSqNorm (Ms l
      G).zc.dim (Ms l G).δc ≤ S.Dstar ∧ (2 : ℝ) * gaugeTail (Ms l G).zc.dim (Ms l G).δc
      / (2 : ℝ) ^ fp.Kstar Dm0 dB Hm δ Nl kD δ * S.Dstar ^ (300 : ℕ) ≤ (1 : ℝ) ∧ (∀ (m :
      (Ms l G).Md), S.Dstar⁻¹ ≤ (Ms l G).L.εM m) ∧ (∀ (V : ℤ × ℤ), (↑((Ms l G).alive
      V).card : ℝ) ≤ S.Dstar) ∧ ∀ (V : ℤ × ℤ), (↑(Finset.image (Ms l G).keyOf ((Ms l
      G).alive V)).card : ℝ) ≤ Nl)
    (hA6 : (6 : ℝ) ≤ S.A0),
  let qG : bf.Grp → ℕ :=
    fun (G : bf.Grp) => clearInt (bf.vtag (bf.grpCenter d G)).C
  ∀ (_ : ∀ (G : bf.Grp), (1 : ℕ) ≤ qG G ∧ qG G ≤ S.Q0)
    (Vl0 : ℝ)
    (_ : Vl0 = (24 : ℝ) * ((↑⌊(180 : ℝ) * (↑S.dmax : ℝ) * Real.log ((2 : ℝ) * S.Dm) / (1 /
      1024 : ℝ)⌋₊ : ℝ) + (1 : ℝ)) * (Real.exp (((6144 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) *
      ((1024 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) + (↑cc : ℝ) + (7 : ℝ)) + (4 : ℝ)) * ((1 : ℝ) +
      Real.log ((2 : ℝ) * (↑k : ℝ))) ^ (2 : ℕ)) + (2 : ℝ) * (1 : ℝ) / S.Dstar ^ (394 :
      ℕ)))
    (U : ℝ)
    (_ : U = max ((2 : ℝ) * (A.colBudget + (2 : ℝ)) * S.Dstar ^ (2 : ℕ)) √(TsideF A fp.P S.K
      (A.uslot p) ((2 : ℕ) ^ A.famFuel) ((2 : ℕ) * A.famFuel + (2 : ℕ)) (1 : ℝ) E cc (↑k
      : ℝ) (fun (_ : Fin (4 : ℕ)) => Vl0) ρ))
    (_ : (2 : ℝ) * (A.colBudget + (2 : ℝ)) * S.Dstar ^ (2 : ℕ) ≤ U)
    (_ : (0 : ℝ) < S.Dstar)
    (_ : (1 : ℝ) ≤ S.Dstar)
    (_ : (16 : ℝ) ≤ U)
    (_ : (0 : ℝ) < U)
    (MV : ℝ)
    (_ : MV = (↑AD.Mp : ℝ) * (↑A.famVtxBound : ℝ))
    (_ : (0 : ℝ) ≤ MV)
    (ε : ℝ)
    (_ : ε = (U ^ (3 : ℕ) * S.Dstar ^ (5 : ℕ) * Real.exp (↑k : ℝ) * ((1 : ℝ) + MV))⁻¹)
    (_ : (0 : ℝ) < ε)
    (_ : ε ≤ U)
    (_ : S.Dstar⁻¹ ≤ U)
    (_ : ∀ σ ∈ dyThr ε U S.Dstar, S.Dstar⁻¹ ≤ σ)
    (_ : ∀ (σ : ℝ), ε ≤ σ → σ ≤ U → (∃ (k : ℤ), σ = (2 : ℝ) ^ k) → S.Dstar⁻¹ ≤ σ → σ ∈ dyThr
      ε U S.Dstar)
    (_ : (↑(dyThr ε U S.Dstar).card : ℝ) ≤ Real.logb (2 : ℝ) U - Real.logb (2 : ℝ) ε + (3 :
      ℝ)),
  let Ts : Finset (ℕ × ℕ) :=
    Finset.range (Nat.log (2 : ℕ) ⌊S.Dstar⌋₊ + (1 : ℕ)) ×ˢ Finset.range (Nat.log (2 : ℕ)
      ⌊S.Dstar⌋₊ + (1 : ℕ))
  ∀ (_ : Ts = Finset.range (Nat.log (2 : ℕ) ⌊S.Dstar⌋₊ + (1 : ℕ)) ×ˢ Finset.range (Nat.log (2
      : ℕ) ⌊S.Dstar⌋₊ + (1 : ℕ))),
  let BN : ℕ :=
    ⌈(8 : ℝ) * A.colBudget + Nl⌉₊
  let τb : ℝ :=
    (1 : ℝ) / ((1 : ℝ) + (↑BN : ℝ) * A.colBudget ^ (2 : ℕ))
  ∀ (_ : (0 : ℝ) < τb)
    (_ : τb ≤ (1 : ℝ))
    (_ : τb * (↑BN : ℝ) * A.colBudget ^ (2 : ℕ) ≤ (1 : ℝ))
    (_ : Real.exp ((↑A.Dg : ℝ) * ((1 : ℝ) + Real.log A.Hsrc + Real.log τb⁻¹) ^ A.Dg) ≤ fp.Hed)
    (_ : ∀ I ∈ A.cells, dyadicGridCell A.G I.1 I.2 ⊆ Set.Icc (dyadicGridLeft A.G A.R.1 A.R.2)
      (dyadicGridLeft A.G A.R.1 A.R.2 + dyadicGridLength A.G A.R.1))
    (ρ₀ : Fin (4 : ℕ) → ↥gset → Fin A.fcd0)
    (zc : Fin (4 : ℕ) → ↥gset → bf.Vtx)
    (gsc : Fin (4 : ℕ) → ↥gset → ℤ)
    (_ : ∀ (l : Fin (4 : ℕ)) (G : ↥gset), (↑G : bf.Grp).2.1 = some (ρ₀ l G, zc l G, gsc l G))
    (_ : ∀ (l : Fin (4 : ℕ)) (G : ↥gset), fp.MainLiftExports l (AD.cat l) (↑G : bf.Grp)
      (Lf.role l) d Dm0 dB Hm (gsc l G) (L l (↑G : bf.Grp)) (Ms l (↑G : bf.Grp)).wave
      (Ms l (↑G : bf.Grp)).cellOf)
    (_ : ∀ (l : Fin (4 : ℕ)), fp.bbase (Lf.role l) + fp.P ≤ fp.Hmax)
    (_ : (4 : ℝ) ≤ Nl)
    (_ : ∀ (l : Fin (4 : ℕ)) (y : ℝ), (Finset.card ({q : ↥gset × (bf.Lab ⊕ Fin fp.Mc) | ∃ I ∈
      A.cells, (∃ (k' : ℕ), fp.Cert k' (↑q.1 : bf.Grp) I) ∧ ∃ (p_1 : Fin fp.P), y ∈
      dyadicGridCell A.G I.1 I.2 ∧ q.2 ∈ mainLabelsM A.G fp.Mc (bf.origCols l) (AD.cat
      l) I (fp.brank (Lf.role l)) (fp.bmask I (↑q.1 : bf.Grp) (Lf.role l) ((↑p_1 : ℕ) +
      (1 : ℕ))) d})) ≤ BN)
    (_ : ∀ (l : Fin (4 : ℕ)) (y : ℝ), ∑ G : ↥gset, (↑((Ms l (↑G : bf.Grp)).ptSet y).card : ℝ)
      ≤ S.Dstar)
    (_ : ∀ (l : Fin (4 : ℕ)) (G : ↥gset), (2 : ℝ) * ((↑S.Q0 : ℝ) * ((3 : ℝ) * ((Ms l (↑G :
      bf.Grp)).Bσ * (Ms l (↑G : bf.Grp)).Bσ) ^ (2 : ℕ))) ^ (2 : ℕ) ≤ (↑⌊S.Dstar⌋₊ : ℝ))
    (_ : fp.modeStar Dm0 dB Hm δ Nl kD ≤ S.Dstar)
    (_ : ∀ (l : Fin (4 : ℕ)), (↑(Lf.layers l).length : ℝ) ≤ (↑cc : ℝ) * (Real.log (↑k : ℝ) +
      (1 : ℝ)))
    (c : (l : Fin (4 : ℕ)) → (G : ↥gset) → ℤ → ℤ × ℤ → (Ms l (↑G : bf.Grp)).Md → ℂ)
    (_ : ∀ (l : Fin (4 : ℕ)) (G : ↥gset), ∀ b ∈ Finset.image (fun (β : ℕ) => A.R.1 + (↑(S.K *
      β) : ℤ)) (Finset.range (A.treeDepth + (1 : ℕ))), ∀ J ∈ fp.retainedV (↑G : bf.Grp)
      b S.K, (Ms l (↑G : bf.Grp)).frozenEval (S.withQ0 (qG (↑G : bf.Grp))) b J (c l G b
      J) = (columnL2Restriction (dyadicGridCell A.G J.1 J.2) (dyadicGridCell_measurable
      A.G J.1 J.2) : ↥(ColumnL2 (Ms l (↑G : bf.Grp)).Md) → ↥(ColumnL2 (Ms l (↑G :
      bf.Grp)).Md)) (((L l (↑G : bf.Grp)).op : ↥(ColumnL2 (bf.Lab ⊕ Fin fp.Mc)) →
      ↥(ColumnL2 (Ms l (↑G : bf.Grp)).Md)) (fp.frozenZ l (AD.cat l) (mbs l) (↑G :
      bf.Grp) (Lf.role l) (Lf.layers l) (b - (4 : ℤ) * (↑S.K : ℤ)))))
    (_ : ∀ (l : Fin (4 : ℕ)) (G : ↥gset), ∀ b ∈ Finset.image (fun (β : ℕ) => A.R.1 + (↑(S.K *
      β) : ℤ)) (Finset.range (A.treeDepth + (1 : ℕ))), ∀ J ∈ fp.retainedV (↑G : bf.Grp)
      b S.K, ∑ m ∈ (Ms l (↑G : bf.Grp)).alive (ancAt A.G J (b - (4 : ℤ) * (↑S.K : ℤ))),
      ‖c l G b J m‖ ^ (2 : ℕ) ≤ (4 : ℝ) * S.Dstar ^ (2 : ℕ) * (1 : ℝ))
    (_ : ∀ (l : Fin (4 : ℕ)), ∑ G : ↥gset, ∑ b ∈ Finset.image (fun (β : ℕ) => A.R.1 + (↑(S.K
      * β) : ℤ)) (Finset.range (A.treeDepth + (1 : ℕ))), ‖(Ms l (↑G : bf.Grp)).blockSide
      (S.withQ0 (qG (↑G : bf.Grp))) hA6 (S.sideParams (1 / 1024 : ℝ)) b (fp.retainedV
      (↑G : bf.Grp) b S.K) (c l G b)‖ ^ (2 : ℕ) ≤ (24 : ℝ) * ((↑⌊(180 : ℝ) * (↑S.dmax :
      ℝ) * Real.log ((2 : ℝ) * S.Dm) / (1 / 1024 : ℝ)⌋₊ : ℝ) + (1 : ℝ)) * (Real.exp
      (((6144 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) * ((1024 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) + (↑cc
      : ℝ) + (7 : ℝ)) + (4 : ℝ)) * ((1 : ℝ) + Real.log ((2 : ℝ) * (↑k : ℝ))) ^ (2 : ℕ))
      + (2 : ℝ) * (1 : ℝ) / S.Dstar ^ (394 : ℕ)) * dyadicGridLength A.G A.R.1)
    (Rr : (l : Fin (4 : ℕ)) → (h : ℕ) → ℕ × ℕ → (G : ↥gset) → (Ms l (↑G : bf.Grp)).RepClass
      (S.withQ0 (qG (↑G : bf.Grp))) hA6 (S.sideParams (1 / 1024 : ℝ)) (10 : ℕ) h)
    (_ : ∀ (l : Fin (4 : ℕ)), ∀ h ≤ S.Jstar, ∀ (t : ℕ × ℕ) (G : ↥gset), (Rr l h t G).Nd = {c
      ∈ (Ms l (↑G : bf.Grp)).succNodes (S.withQ0 (qG (↑G : bf.Grp))) hA6 (S.sideParams
      (1 / 1024 : ℝ)) (fp.retainedPairs (↑G : bf.Grp) (Finset.image (fun (β : ℕ) =>
      A.R.1 + (↑(S.K * β) : ℤ)) (Finset.range (A.treeDepth + (1 : ℕ)))) S.K) h | (Ms l
      (↑G : bf.Grp)).nodeType1 (S.withQ0 (qG (↑G : bf.Grp))) hA6 (10 : ℕ) h c = t.1 ∧
      (Ms l (↑G : bf.Grp)).nodeType2 (S.withQ0 (qG (↑G : bf.Grp))) hA6 (10 : ℕ) h c =
      t.2})
    (Cut : Fin (4 : ℕ) → Finset (ℤ × ℤ))
    (_ : ∀ (l : Fin (4 : ℕ)), dyadicRootLength A.G (Cut l) ≤ ρ * dyadicGridLength A.G A.R.1)
    (_ : ∀ (l : Fin (4 : ℕ)) (y : ℝ), ∀ h ∈ Finset.range (S.Jstar + (1 : ℕ)), ∀ t ∈ Ts, ∀ σ ∈
      dyThr ε U S.Dstar, ∑ G : ↥gset, (↑(Finset.image (fun (p : (ℤ × ℤ) × ℤ × (ℤ × ℤ) ×
      (Ms l (↑G : bf.Grp)).Md) => (Rr l h t G).rep p.2) ({p ∈ fp.useInst (↑G : bf.Grp)
      S.K (Rr l h t G).Nd | (∀ e ∈ Cut l, ¬dyadicGridCell A.G p.1.1 p.1.2 ⊆
      dyadicGridCell A.G e.1 e.2) ∧ y ∈ dyadicGridCell A.G p.1.1 p.1.2 ∧ σ ^ (2 : ℕ) ≤
      (Ms l (↑G : bf.Grp)).nodeSize (S.withQ0 (qG (↑G : bf.Grp))) hA6 (S.sideParams (1 /
      1024 : ℝ)) (c l G) h p})).card : ℝ) ≤ min S.Dstar ((24 : ℝ) * ((2 : ℝ) * Real.exp
      (((6144 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) * ((1024 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) + (↑cc
      : ℝ) + (7 : ℝ)) + (4 : ℝ)) * ((1 : ℝ) + Real.log ((2 : ℝ) * (↑k : ℝ))) ^ (2 : ℕ))
      + (2 : ℝ) * (↑S.K : ℝ) * ((24 : ℝ) * ((↑⌊(180 : ℝ) * (↑S.dmax : ℝ) * Real.log ((2
      : ℝ) * S.Dm) / (1 / 1024 : ℝ)⌋₊ : ℝ) + (1 : ℝ)) * (Real.exp (((6144 : ℝ) * ((↑cc :
      ℝ) + (1 : ℝ)) * ((1024 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) + (↑cc : ℝ) + (7 : ℝ)) + (4 :
      ℝ)) * ((1 : ℝ) + Real.log ((2 : ℝ) * (↑k : ℝ))) ^ (2 : ℕ)) + (2 : ℝ) * (1 : ℝ) /
      S.Dstar ^ (394 : ℕ)))) * (↑(Finset.range (S.Jstar + (1 : ℕ)) ×ˢ Ts ×ˢ dyThr ε U
      S.Dstar).card : ℝ) / (ρ * σ ^ (2 : ℕ)))),
  let cf : (l : Fin (4 : ℕ)) → (G : bf.Grp) → ℤ → ℤ × ℤ → (Ms l G).Md → ℂ :=
    fun (l : Fin (4 : ℕ)) (G : bf.Grp) => if hG : G ∈ gset then c l ⟨G, hG⟩ else fun _ _
      _ => (0 : ℂ)
  let D₀ : fp.SideInput :=
    { cat := AD.cat, mbs := mbs, Lf := Lf, u := A.uslot p, S := S, hA := hA6,
      SP := S.sideParams (1 / 1024 : ℝ), hK := hK1,
      n := Fintype.card (bf.Lab ⊕ Fin fp.Mc), Ms := Ms, c := cf }
  let gE : ℤ × ℤ → Fin A.famVtxBound → bf.Grp :=
    fun (I : ℤ × ℤ) (i : Fin A.famVtxBound) => if h : (↑i : ℕ) < (gs I).card then
      (↑(((gs I).equivFin.symm : Fin (gs I).card → ↥(gs I)) ⟨(↑i : ℕ), h⟩) : bf.Grp)
      else default
  ∀ (_ : ∀ (I : ℤ × ℤ), ∀ G ∈ gs I, ∃ (i : Fin A.famVtxBound), gE I i = G)
    (hcat : Fin (4 : ℕ) → List (CatCol bf.Vtx))
    (_ : ∀ (l : Fin (4 : ℕ)), ∀ d ∈ hcat l, d.birth ∈ AD.Tc ∧ d.rank = fp.Lc + (5 : ℕ) ∧ (∃
      (M : fp.MaskName d.birth), fp.maskOf d.birth M d.tag) ∧ ∃ R ∈ residueBox (bf.vtag
      d.tag).dim (9 : ℕ), ∃ (γ : ℝ), d = templateCol (bf.vtag d.tag) l R γ d.birth
      d.rank d.tag)
    (_ : ∀ (l : Fin (4 : ℕ)) (y : ℝ), (↑(bf.tmplPath (AD.cat l ++ hcat l) y) : ℝ) ≤ ((1 : ℝ)
      + (↑AD.Mp : ℝ)) * Nl)
    (hmbb : ∀ (l : Fin (4 : ℕ)), ∀ e ∈ AD.cat l ++ hcat l, e.birth ∈ A.cells)
    (hmbT : ∀ (l : Fin (4 : ℕ)) (y : ℝ), (8 : ℝ) * A.colBudget + (↑(bf.tmplPath (AD.cat l ++
      hcat l) y) : ℝ) ≤ (8 : ℝ) * A.colBudget + ((1 : ℝ) + (↑AD.Mp : ℝ)) * Nl),
  let mb' : (l : Fin (4 : ℕ)) → bf.MainBudget (AD.cat l ++ hcat l) :=
    fun l =>
        { hb := hmbb l, B := 8 * A.colBudget + (1 + AD.Mp) * Nl, hTp := hmbT l }
  let D : fp.SideInput :=
    D₀.appendCat hcat mb'
  ∀ (_ : ∀ (l : Fin (4 : ℕ)), ∀ e ∈ hcat l, fp.hrank ≤ e.rank)
    (_ : ∀ (l : Fin (4 : ℕ)), D₀.Lf.role l ≤ (4 : ℕ))
    (_ : ∀ (l : Fin (4 : ℕ)), ∀ e ∈ hcat l, bf.occAvail (↑e.tag.2 : ℤ × ℤ) e.tag.1),
  let S1 : Finset (ℤ × ℤ) :=
    {I ∈ S0 | ∀ (j : Fin (4 : ℕ)), ∀ e ∈ Cut j, ¬dyadicGridCell A.G I.1 I.2 ⊆
      dyadicGridCell A.G e.1 e.2}
  ∀ (_ : S1 ⊆ S0)
    (_ : S1 ⊆ A.cells)
    (_ : ∀ I ∈ A.cells, ((I.1 - A.R.1) / (↑S.K : ℤ)).toNat < A.treeDepth + (1 : ℕ))
    (_ : ∀ I ∈ A.cells, A.blkStart S.K I.1 ∈ Finset.image (fun (β : ℕ) => A.R.1 + (↑(S.K * β)
      : ℤ)) (Finset.range (A.treeDepth + (1 : ℕ))))
    (_ : ∀ I ∈ S1, ∀ (l : Fin (4 : ℕ)), D.u ≠ some l → ∀ (w : fp.TestName I Unit), fp.MainRk
      w → (fp.testOf l I (fun (_ : Unit) => bf.basicIn fp.Mc l I) w).Pass A.G
      (bf.origCols l) I A.csrc A.Hsrc bf.vtag (A.w I) (catThreshold A.famVtxBound AD.τ₃
      AD.n (fp.testOf l I (fun (_ : Unit) => bf.basicIn fp.Mc l I) w).r) fp.mH (D.cat l))
    (_ : ∀ I ∈ S1, ∀ (a : Fin (4 : ℕ)) (w : fp.HelperName I (Fin A.famVtxBound)),
      (fp.helperOf a I (fun (i : Fin A.famVtxBound) => (D.toLeafQ qG).sv a (gE I i) I)
      w).Pass A.G (bf.origCols a) I A.csrc A.Hsrc bf.vtag (A.w I) (catThreshold
      A.famVtxBound AD.τ₃ AD.n (fp.Lc + (5 : ℕ))) fp.mH (D.cat a))
    (_ : ∀ (R : ℕ), (1 : ℕ) ≤ R → R ≤ fp.Lc + (4 : ℕ) → catThreshold A.famVtxBound AD.τ₃ AD.n
      R * (A.colBudget * √(AD.n (R - (1 : ℕ)))) ≤ AD.τ₃)
    (_ : catThreshold A.famVtxBound AD.τ₃ AD.n (fp.Lc + (5 : ℕ)) * (A.colBudget * √(AD.n
      (fp.Lc + (4 : ℕ)))) ≤ AD.τ₃)
    (_ : ∀ (R : ℕ), (0 : ℝ) ≤ catThreshold A.famVtxBound AD.τ₃ AD.n R)
    (_ : ∀ I ∈ S1, ∀ (l : Fin (4 : ℕ)), ∀ r ≤ fp.Lc + (4 : ℕ), ∀ (M : bf.Vtx → Prop),
      (↑(mainLabelsM A.G fp.Mc (bf.origCols l) (D.cat l) I r M d).card : ℝ) ≤ AD.n r),
  ∃ (F : Fin (6 : ℕ) → Finset (ℤ × ℤ)), (∀ (i : Fin (6 : ℕ)), ∀ c ∈ F i,
    dyadicGridCell A.G c.1 c.2 ⊆ dyadicGridCell A.G A.R.1 A.R.2) ∧ (∀ (i : Fin (6 :
    ℕ)), dyadicRootLength A.G (F i) ≤ (2 : ℝ) * ρ * dyadicGridLength A.G A.R.1) ∧ ∀ cs
    ⊆ AD.Tc, (∀ I ∈ cs, ¬∃ c ∈ fp.failRoots, dyadicGridCell A.G I.1 I.2 ⊆
    dyadicGridCell A.G c.1 c.2) → (∀ I ∈ cs, ∀ (i : Fin (6 : ℕ)), ∀ e ∈ F i,
    ¬dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G e.1 e.2) → ∑ I ∈ cs,
    dyadicGridLength A.G I.1 * min A.η ‖∑ G ∈ fp.groupsAt I ks, (fp.Λc I : (Fin (4 :
    ℕ) → ↥(ColumnL2 (bf.Lab ⊕ Fin fp.Mc))) → ℂ) fun (l : Fin (4 : ℕ)) => (fp.ballFilt
    l (AD.cat l) I G (Lf.role l) : ↥(ColumnL2 (bf.Lab ⊕ Fin fp.Mc)) → ↥(ColumnL2
    (bf.Lab ⊕ Fin fp.Mc))) (fp.inputL AD.cat I (bf.patIn fp.Mc p I) Lf.layers l)‖ ≤
    leafBnd Cl kD fp.P k cc A.η η₀ AD.τ₃ δ (finiteDepthConstant κ q Nd) (nbCM κ hq2
    hq3 + nbCUM κ hq2 hq3) q (dyadicGridLength A.G A.R.1)


open scoped Classical in
private def LeafEstimateStage3Statement : Prop :=
  ∀ (κ : LocalKernelClass)
    (c₀ : ℕ)
    (cc : ℕ)
    (_ : (1 : ℕ) ≤ cc)
    (Dm0 : ℕ)
    (Msch : ℝ)
    (_ : (0 : ℝ) < Msch)
    (Cg : ℕ)
    (_ : ∀ {κ : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ c₀} {bf : A.BasicFamilies} (fp
      : bf.FamParams) (dB : ℕ) {H δc N k δ : ℝ}, (1 : ℝ) ≤ k → (↑fp.Lc : ℝ) + (6 : ℝ) ≤
      k ^ (cc + (6 : ℕ)) → (↑fp.Hmax : ℝ) + (1 : ℝ) ≤ (k * (↑fp.P : ℝ)) ^ (cc + (6 : ℕ))
      → (↑dB : ℝ) ≤ k ^ (cc + (6 : ℕ)) → (2 : ℝ) ≤ fp.Hed → Real.log fp.Hed ≤ k ^ (cc +
      (6 : ℕ)) → (1 : ℝ) ≤ H → Real.log H ≤ k ^ (cc + (6 : ℕ)) → (0 : ℝ) < δc → δc⁻¹ ≤
      Real.exp (k ^ (cc + (6 : ℕ))) → (0 : ℝ) ≤ N → N ≤ Real.exp (k ^ (cc + (6 : ℕ))) →
      A.colBudget ≤ Real.exp (k ^ (cc + (6 : ℕ))) → (0 : ℝ) < δ → δ⁻¹ ≤ Real.exp (k ^
      (cc + (6 : ℕ))) → Real.log (fp.modeStarG Dm0 dB H δc N k δ) ≤ (↑Cg : ℝ) * (k *
      (↑fp.P : ℝ)) ^ Cg ∧ Real.log ((2 : ℝ) ^ (fp.Kstar Dm0 dB H δc N k δ + (1 : ℕ))) ≤
      (↑Cg : ℝ) * (k * (↑fp.P : ℝ)) ^ Cg)
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
    (eΛ : ℕ)
    (CM1 : ℕ)
    (t3 : ℕ)
    (Cb : ℕ)
    (Cl : ℕ)
    (_ : g = (8192 : ℕ) * (cc + (1 : ℕ)) * ((1024 : ℕ) * (cc + (1 : ℕ)) + cc + (7 : ℕ)) + cc
      ^ (2 : ℕ) + (8 : ℕ) ∧ cT = (10 : ℝ) ^ (22 : ℕ) * ((1 : ℝ) +
      localFormUniformConstant κ) ^ (2 : ℕ) ∧ cL = (159 : ℝ) + (32 : ℝ) * (↑g : ℝ) + (8
      : ℝ) * Real.log cT ∧ cK = ((1 : ℝ) + (7 : ℝ) * (10 : ℝ) ^ (9 : ℕ) + cT) * (cL + (2
      : ℝ)) ∧ cMc = (C4c κ + (4 : ℝ) * C3c κ) * cL ^ (4 : ℕ) * cK ^ (2 : ℕ) ∧ cm =
      (196608 : ℝ) * cT + (83 : ℝ) * ((1 : ℝ) + (81 : ℝ) * localFormUniformConstant κ *
      ((30000 : ℝ) + √cT)) * ((1 : ℝ) + cT) ^ (3 : ℕ) + cMc ∧ ce = (6642 : ℝ) *
      localFormUniformConstant κ * ((60000 : ℝ) + √cT) ^ (3 : ℕ) * (288 : ℝ) + (9 : ℝ) *
      ((16 : ℝ) * fourErrC κ (3 : ℕ) + (648 : ℝ) * threeErrC κ (3 : ℕ) (1 : ℕ) + (324 :
      ℝ) * threeErrC κ (3 : ℕ) (1 : ℕ) * √cT) ∧ ce2 = K1c * ((2 : ℝ) * fourKC κ (3 : ℕ)
      * (12 : ℝ) ^ (4 : ℕ)) + (4 : ℝ) * (K1c * ((8 : ℝ) * entryCU κ (3 : ℕ) (1 : ℕ) * (2
      : ℝ) ^ ((1 : ℕ) + (4 : ℕ)) * (12 : ℝ) ^ (3 : ℕ))) * (501 : ℝ) ∧ cQ = (65536 : ℝ) *
      ((8 : ℝ) + (80 : ℝ) * (9 : ℝ) ^ cc * (↑cc : ℝ)) * ((80 : ℝ) * (9 : ℝ) ^ cc * (↑cc
      : ℝ)) * ((4 : ℝ) * (↑cc : ℝ) ^ (2 : ℕ)) * ((17 : ℝ) * (10 : ℝ) ^ (7 : ℕ)) ∧ CΛ =
      (2 : ℕ) * Cg + (12 : ℕ) ∧ eΛ = Cg + (3 : ℕ) * cc ∧ CM1 = (⌈Msch⌉₊ + (1 : ℕ)) * CΛ
      ^ (16 : ℕ) ∧ t3 = (3 : ℕ) ^ cc ∧ Cb = CM1 + (501 : ℕ) * Cg + t3 + (2 : ℕ) * cc +
      (20 : ℕ) + (16 : ℕ) * eΛ ∧ Cl = ⌈cm * (↑Cb : ℝ) ^ (59 : ℕ) + ce * (↑Cb : ℝ) ^ (18
      : ℕ) + ce2 + (3 : ℝ) * (10 : ℝ) ^ (11 : ℕ) * cQ⌉₊ + (59 : ℕ) * Cb + (4 : ℕ) * g +
      (8 : ℕ) * cc + (8 : ℕ))
    (A : ActiveSetup κ c₀)
    (bf : A.BasicFamilies)
    (k : ℕ)
    (η₀ : ℝ)
    (E : ℝ)
    (_ : A.AncClosed)
    (_ : ∀ I ∈ A.cells, ∀ (s s' : Fin (4 : ℕ)), s ≠ s' → PairSmall (dyadicGridLeft A.G I.1
      I.2) (dyadicGridLength A.G I.1) (A.w I) s s' (A.Y I s) (A.Y I s') ((2 : ℝ) * η₀))
    (_ : A.SubRootProps η₀ E)
    (_ : A.S = (2 : ℝ))
    (_ : A.η = (4 : ℝ) * η₀)
    (_ : (0 : ℝ) < η₀)
    (_ : A.cells.Nonempty)
    (q : ℝ)
    (hq2 : (2 : ℝ) < q)
    (hq3 : q < (3 : ℝ))
    (Nd : ℕ)
    (_ : A.DepthWin Nd)
    (p : Fin (3 : ℕ))
    (AD : bf.AttemptData p)
    (d : bf.Vtx)
    (s : ℕ)
    (δ : ℝ)
    (ρ : ℝ)
    (kD : ℝ)
    (_ : (0 : ℝ) < δ)
    (_ : δ ≤ (1 / 8 : ℝ))
    (_ : (0 : ℝ) < ρ)
    (_ : ρ < (1 : ℝ))
    (_ : Real.log ((2 : ℝ) * A.colBudget) ≤ (↑k : ℝ) ^ cc)
    (_ : (↑((2 : ℕ) * A.famFuel + (2 : ℕ)) : ℝ) ≤ (↑cc : ℝ) * (Real.log (↑k : ℝ) + (1 : ℝ)))
    (_ : (1 : ℝ) ≤ (↑k : ℝ)),
  let fp : bf.FamParams :=
    AD.fp
  let dB : ℕ :=
    A.dBnd
  ∀ (_ : (↑fp.Lc : ℝ) + (6 : ℝ) ≤ (↑k : ℝ) ^ cc ∧ (↑fp.Hmax : ℝ) + (1 : ℝ) ≤ ((↑k : ℝ) *
      (↑fp.P : ℝ)) ^ cc ∧ (↑dB : ℝ) ≤ (↑k : ℝ) ^ cc ∧ Real.log fp.Hed ≤ (↑k : ℝ) ^ cc ∧
      Real.log A.Hsrc ≤ (↑k : ℝ) ^ cc ∧ Real.log (max A.H padW) ≤ (↑k : ℝ) ^ cc ∧ δ⁻¹ ≤
      Real.exp kD ∧ E ≤ (↑k : ℝ) ^ cc ∧ ρ⁻¹ ≤ (↑k : ℝ) ^ cc ∧ (2 : ℝ) + Real.log
      bumpConst + (100 : ℝ) ≤ (↑k : ℝ) ∧ (↑k : ℝ) ^ cc ≤ kD ∧ (2 : ℝ) ≤ (↑k : ℝ) ∧ (0 :
      ℝ) ≤ Real.log bumpConst)
    (_ : (8 : ℝ) * (↑dB : ℝ) * δ ≤ (1 : ℝ)),
  let Nl : ℝ :=
    AD.n (fp.Lc + (5 : ℕ))
  ∀ (_ : Real.log ((2 : ℝ) * ((8 : ℝ) * A.colBudget + ((1 : ℝ) + (↑AD.Mp : ℝ)) * Nl)) ≤ (↑k :
      ℝ) ^ cc)
    (_ : (2 : ℝ) ≤ A.colBudget)
    (_ : Monotone AD.n)
    (hNl0 : (0 : ℝ) ≤ Nl),
  let Hm : ℝ :=
    max (max A.Hsrc (Real.exp (↑dB : ℝ))) (max ((5832 : ℝ) * max A.H padW ^ (4 : ℕ))
      ((↑dB : ℝ) * (bumpConst * (8 : ℝ) ^ (32 : ℕ) * ((2 : ℝ) / δ))))
  ∀ (_ : (1 : ℝ) ≤ Hm)
    (_ : ∀ (w : bf.Vtx), (bf.vtag w).dim ≤ dB)
    (_ : ∀ (w : bf.Vtx) (a c : Fin (bf.vtag w).dim), (↑(rationalHeight ((bf.vtag w).C a c)) :
      ℝ) ≤ fp.Hed)
    (S : ModeSchedule)
    (_ : S.dmax = (2 : ℕ) * dB + (2 : ℕ))
    (_ : S.Dm = max (2 : ℝ) Nl)
    (_ : S.Valid (340 : ℕ) (5 : ℕ) (4 : ℕ) (600 : ℕ) (1 / 1024 : ℝ) (packetW S.dmax S.H))
    (_ : (2 : ℕ) ≤ S.dmax)
    (_ : (↑S.dmax : ℝ) ≤ S.Dstar)
    (_ : (2 : ℝ) ≤ S.Dstar)
    (_ : (2 : ℝ) ≤ S.Bstar)
    (_ : (1 : ℕ) ≤ S.Q0)
    (_ : (↑S.Q0 : ℝ) * (2 : ℝ) ^ (fp.Kstar Dm0 dB Hm δ Nl kD δ + (1 : ℕ)) ≤ S.Bstar)
    (_ : Real.log S.H ≤ Msch * ((↑((2 : ℕ) * dB + (2 : ℕ)) : ℝ) + Real.log (fp.modeStarG Dm0
      dB Hm δ Nl kD δ) + Real.log (fp.Bst Dm0 dB Hm δ Nl kD δ) + Real.log (max (2 : ℝ)
      Nl) + Real.log (↑(fp.Q0bd dB) : ℝ) + (1 : ℝ)) ^ (12 : ℕ))
    (_ : (↑S.K : ℝ) ≤ Msch * ((↑((2 : ℕ) * dB + (2 : ℕ)) : ℝ) + Real.log (fp.modeStarG Dm0 dB
      Hm δ Nl kD δ) + Real.log (fp.Bst Dm0 dB Hm δ Nl kD δ) + Real.log (max (2 : ℝ) Nl)
      + Real.log (↑(fp.Q0bd dB) : ℝ) + (1 : ℝ)) ^ (16 : ℕ))
    (_ : (1 : ℕ) ≤ S.K),
  let Lf : SearchLeaf :=
    leafAt A.famFuel fp.Lc (A.basicSlot p) s
  let ks : ℕ :=
    Lf.k
  let S0 : Finset (ℤ × ℤ) :=
    {I ∈ AD.Tc | ¬∃ c ∈ fp.failRoots, dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G
      c.1 c.2}
  ∀ (_ : S0 ⊆ AD.Tc)
    (_ : S0 ⊆ A.cells),
  let gs : ℤ × ℤ → Finset bf.Grp :=
    fun (I : ℤ × ℤ) => fp.groupsAt I ks
  let gset : Finset bf.Grp :=
    S0.biUnion gs
  ∀ (_ : ∀ I ∈ S0, ∀ G ∈ gs I, fp.Cert ks G I ∧ fp.ActualUse G I),
  let U_1 : Fin (4 : ℕ) → bf.Grp → Finset (ℤ × ℤ) :=
    fun (_ : Fin (4 : ℕ)) (G : bf.Grp) => {I ∈ S0 | G ∈ gs I}
  ∀ (hlenMc : ∀ (l : Fin (4 : ℕ)), (AD.cat l).length ≤ fp.Mc),
  let mbs : (l : Fin (4 : ℕ)) → bf.MainBudget (AD.cat l) :=
    fun l => MainBudget.ofCounts bf fp.Mc (AD.cat l) (hlenMc l) l (fun e he => AD.hTc
      (AD.hT l e he).1) (fun e he => (AD.hT l e he).2.1) hNl0 (fun I _ => AD.hlab l I _
      le_rfl)
  ∀ (Ms : Fin (4 : ℕ) → bf.Grp → ModeSystem A.G (Fintype.card (bf.Lab ⊕ Fin fp.Mc)))
    (L : (l : Fin (4 : ℕ)) → (G : bf.Grp) → LiftData (bf.Lab ⊕ Fin fp.Mc) (Ms l G).Md)
    (_ : ∀ (l : Fin (4 : ℕ)), ∀ G ∈ gset, fp.ModeExports l (AD.cat l) G (Lf.role l) d Dm0 dB
      Hm δ δ Nl (Ms l G) (L l G))
    (_ : ∀ (l : Fin (4 : ℕ)), ∀ G ∉ gset, (∀ (p : (Ms l G).Key), (Ms l G).dvOf p + (Ms l
      G).zc.dim ≤ (2 : ℕ) * dB + (2 : ℕ)) ∧ (Ms l G).Bσ = (1 : ℝ) ∧ ∀ (V : ℤ × ℤ), (Ms l
      G).alive V = ∅)
    (_ : PLift (∑ l : Fin (4 : ℕ), ∑ G ∈ gset, ∑ I ∈ U_1 l G, ∫ (y : ℝ) in dyadicGridCell A.G
      I.1 I.2, ‖((↑(↑(fp.physError (Ms l G) (L l G) l (AD.cat l) (mbs l) G (Lf.role l)
      (Lf.layers l) S.K (A.blkStart S.K I.1)) : ℝ →ₘ[volume] ColumnHilbert (bf.Lab ⊕ Fin
      fp.Mc)) : ℝ → ColumnHilbert (bf.Lab ⊕ Fin fp.Mc)) y).ofLp none‖ ^ (2 : ℕ) ≤ ((8 :
      ℝ) * (↑dB : ℝ) * δ + (2 : ℝ) * δ ^ (2 : ℕ)) * ((4 : ℝ) * Nl * A.colBudget ^ (2 :
      ℕ) * (1 : ℝ)) * (↑((4 : ℕ) * (AD.Mp * A.famVtxBound)) : ℝ) * dyadicGridLength A.G
      A.R.1))
    (_ : S.Dstar = fp.modeStarG Dm0 dB Hm δ Nl kD δ)
    (_ : ∀ (l : Fin (4 : ℕ)), ∀ G ∈ gset, (∀ (q : (Ms l G).Key), (Ms l G).dvOf q + (Ms l
      G).zc.dim ≤ (2 : ℕ) * dB + (2 : ℕ)) ∧ (Ms l G).Λ ≤ S.Dstar ∧ gaugeSqNorm (Ms l
      G).zc.dim (Ms l G).δc ≤ S.Dstar ∧ (2 : ℝ) * gaugeTail (Ms l G).zc.dim (Ms l G).δc
      / (2 : ℝ) ^ fp.Kstar Dm0 dB Hm δ Nl kD δ * S.Dstar ^ (300 : ℕ) ≤ (1 : ℝ) ∧ (∀ (m :
      (Ms l G).Md), S.Dstar⁻¹ ≤ (Ms l G).L.εM m) ∧ (∀ (V : ℤ × ℤ), (↑((Ms l G).alive
      V).card : ℝ) ≤ S.Dstar) ∧ ∀ (V : ℤ × ℤ), (↑(Finset.image (Ms l G).keyOf ((Ms l
      G).alive V)).card : ℝ) ≤ Nl)
    (hA6 : (6 : ℝ) ≤ S.A0),
  let qG : bf.Grp → ℕ :=
    fun (G : bf.Grp) => clearInt (bf.vtag (bf.grpCenter d G)).C
  ∀ (_ : ∀ (G : bf.Grp), (1 : ℕ) ≤ qG G ∧ qG G ≤ S.Q0)
    (Vl0 : ℝ)
    (_ : Vl0 = (24 : ℝ) * ((↑⌊(180 : ℝ) * (↑S.dmax : ℝ) * Real.log ((2 : ℝ) * S.Dm) / (1 /
      1024 : ℝ)⌋₊ : ℝ) + (1 : ℝ)) * (Real.exp (((6144 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) *
      ((1024 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) + (↑cc : ℝ) + (7 : ℝ)) + (4 : ℝ)) * ((1 : ℝ) +
      Real.log ((2 : ℝ) * (↑k : ℝ))) ^ (2 : ℕ)) + (2 : ℝ) * (1 : ℝ) / S.Dstar ^ (394 :
      ℕ)))
    (U : ℝ)
    (_ : U = max ((2 : ℝ) * (A.colBudget + (2 : ℝ)) * S.Dstar ^ (2 : ℕ)) √(TsideF A fp.P S.K
      (A.uslot p) ((2 : ℕ) ^ A.famFuel) ((2 : ℕ) * A.famFuel + (2 : ℕ)) (1 : ℝ) E cc (↑k
      : ℝ) (fun (_ : Fin (4 : ℕ)) => Vl0) ρ))
    (_ : (2 : ℝ) * (A.colBudget + (2 : ℝ)) * S.Dstar ^ (2 : ℕ) ≤ U)
    (_ : (0 : ℝ) < S.Dstar)
    (_ : (1 : ℝ) ≤ S.Dstar)
    (_ : (16 : ℝ) ≤ U)
    (_ : (0 : ℝ) < U)
    (MV : ℝ)
    (_ : MV = (↑AD.Mp : ℝ) * (↑A.famVtxBound : ℝ))
    (_ : (0 : ℝ) ≤ MV)
    (ε : ℝ)
    (_ : ε = (U ^ (3 : ℕ) * S.Dstar ^ (5 : ℕ) * Real.exp (↑k : ℝ) * ((1 : ℝ) + MV))⁻¹)
    (_ : (0 : ℝ) < ε)
    (_ : ε ≤ U)
    (_ : S.Dstar⁻¹ ≤ U)
    (_ : ∀ σ ∈ dyThr ε U S.Dstar, S.Dstar⁻¹ ≤ σ)
    (_ : ∀ (σ : ℝ), ε ≤ σ → σ ≤ U → (∃ (k : ℤ), σ = (2 : ℝ) ^ k) → S.Dstar⁻¹ ≤ σ → σ ∈ dyThr
      ε U S.Dstar)
    (_ : (↑(dyThr ε U S.Dstar).card : ℝ) ≤ Real.logb (2 : ℝ) U - Real.logb (2 : ℝ) ε + (3 :
      ℝ)),
  let Ts : Finset (ℕ × ℕ) :=
    Finset.range (Nat.log (2 : ℕ) ⌊S.Dstar⌋₊ + (1 : ℕ)) ×ˢ Finset.range (Nat.log (2 : ℕ)
      ⌊S.Dstar⌋₊ + (1 : ℕ))
  ∀ (_ : Ts = Finset.range (Nat.log (2 : ℕ) ⌊S.Dstar⌋₊ + (1 : ℕ)) ×ˢ Finset.range (Nat.log (2
      : ℕ) ⌊S.Dstar⌋₊ + (1 : ℕ))),
  let BN : ℕ :=
    ⌈(8 : ℝ) * A.colBudget + Nl⌉₊
  let τb : ℝ :=
    (1 : ℝ) / ((1 : ℝ) + (↑BN : ℝ) * A.colBudget ^ (2 : ℕ))
  ∀ (_ : (0 : ℝ) < τb)
    (_ : τb ≤ (1 : ℝ))
    (_ : τb * (↑BN : ℝ) * A.colBudget ^ (2 : ℕ) ≤ (1 : ℝ))
    (_ : Real.exp ((↑A.Dg : ℝ) * ((1 : ℝ) + Real.log A.Hsrc + Real.log τb⁻¹) ^ A.Dg) ≤ fp.Hed)
    (_ : ∀ I ∈ A.cells, dyadicGridCell A.G I.1 I.2 ⊆ Set.Icc (dyadicGridLeft A.G A.R.1 A.R.2)
      (dyadicGridLeft A.G A.R.1 A.R.2 + dyadicGridLength A.G A.R.1))
    (ρ₀ : Fin (4 : ℕ) → ↥gset → Fin A.fcd0)
    (zc : Fin (4 : ℕ) → ↥gset → bf.Vtx)
    (gsc : Fin (4 : ℕ) → ↥gset → ℤ)
    (_ : ∀ (l : Fin (4 : ℕ)) (G : ↥gset), (↑G : bf.Grp).2.1 = some (ρ₀ l G, zc l G, gsc l G))
    (_ : ∀ (l : Fin (4 : ℕ)) (G : ↥gset), fp.MainLiftExports l (AD.cat l) (↑G : bf.Grp)
      (Lf.role l) d Dm0 dB Hm (gsc l G) (L l (↑G : bf.Grp)) (Ms l (↑G : bf.Grp)).wave
      (Ms l (↑G : bf.Grp)).cellOf)
    (_ : ∀ (l : Fin (4 : ℕ)), fp.bbase (Lf.role l) + fp.P ≤ fp.Hmax)
    (_ : (4 : ℝ) ≤ Nl)
    (_ : ∀ (l : Fin (4 : ℕ)) (y : ℝ), (Finset.card ({q : ↥gset × (bf.Lab ⊕ Fin fp.Mc) | ∃ I ∈
      A.cells, (∃ (k' : ℕ), fp.Cert k' (↑q.1 : bf.Grp) I) ∧ ∃ (p_1 : Fin fp.P), y ∈
      dyadicGridCell A.G I.1 I.2 ∧ q.2 ∈ mainLabelsM A.G fp.Mc (bf.origCols l) (AD.cat
      l) I (fp.brank (Lf.role l)) (fp.bmask I (↑q.1 : bf.Grp) (Lf.role l) ((↑p_1 : ℕ) +
      (1 : ℕ))) d})) ≤ BN)
    (_ : ∀ (l : Fin (4 : ℕ)) (y : ℝ), ∑ G : ↥gset, (↑((Ms l (↑G : bf.Grp)).ptSet y).card : ℝ)
      ≤ S.Dstar)
    (_ : ∀ (l : Fin (4 : ℕ)) (G : ↥gset), (2 : ℝ) * ((↑S.Q0 : ℝ) * ((3 : ℝ) * ((Ms l (↑G :
      bf.Grp)).Bσ * (Ms l (↑G : bf.Grp)).Bσ) ^ (2 : ℕ))) ^ (2 : ℕ) ≤ (↑⌊S.Dstar⌋₊ : ℝ))
    (_ : fp.modeStar Dm0 dB Hm δ Nl kD ≤ S.Dstar)
    (_ : ∀ (l : Fin (4 : ℕ)), (↑(Lf.layers l).length : ℝ) ≤ (↑cc : ℝ) * (Real.log (↑k : ℝ) +
      (1 : ℝ)))
    (c : (l : Fin (4 : ℕ)) → (G : ↥gset) → ℤ → ℤ × ℤ → (Ms l (↑G : bf.Grp)).Md → ℂ)
    (_ : ∀ (l : Fin (4 : ℕ)) (G : ↥gset), ∀ b ∈ Finset.image (fun (β : ℕ) => A.R.1 + (↑(S.K *
      β) : ℤ)) (Finset.range (A.treeDepth + (1 : ℕ))), ∀ J ∈ fp.retainedV (↑G : bf.Grp)
      b S.K, (Ms l (↑G : bf.Grp)).frozenEval (S.withQ0 (qG (↑G : bf.Grp))) b J (c l G b
      J) = (columnL2Restriction (dyadicGridCell A.G J.1 J.2) (dyadicGridCell_measurable
      A.G J.1 J.2) : ↥(ColumnL2 (Ms l (↑G : bf.Grp)).Md) → ↥(ColumnL2 (Ms l (↑G :
      bf.Grp)).Md)) (((L l (↑G : bf.Grp)).op : ↥(ColumnL2 (bf.Lab ⊕ Fin fp.Mc)) →
      ↥(ColumnL2 (Ms l (↑G : bf.Grp)).Md)) (fp.frozenZ l (AD.cat l) (mbs l) (↑G :
      bf.Grp) (Lf.role l) (Lf.layers l) (b - (4 : ℤ) * (↑S.K : ℤ)))))
    (_ : ∀ (l : Fin (4 : ℕ)) (G : ↥gset), ∀ b ∈ Finset.image (fun (β : ℕ) => A.R.1 + (↑(S.K *
      β) : ℤ)) (Finset.range (A.treeDepth + (1 : ℕ))), ∀ J ∈ fp.retainedV (↑G : bf.Grp)
      b S.K, ∑ m ∈ (Ms l (↑G : bf.Grp)).alive (ancAt A.G J (b - (4 : ℤ) * (↑S.K : ℤ))),
      ‖c l G b J m‖ ^ (2 : ℕ) ≤ (4 : ℝ) * S.Dstar ^ (2 : ℕ) * (1 : ℝ))
    (_ : ∀ (l : Fin (4 : ℕ)), ∑ G : ↥gset, ∑ b ∈ Finset.image (fun (β : ℕ) => A.R.1 + (↑(S.K
      * β) : ℤ)) (Finset.range (A.treeDepth + (1 : ℕ))), ‖(Ms l (↑G : bf.Grp)).blockSide
      (S.withQ0 (qG (↑G : bf.Grp))) hA6 (S.sideParams (1 / 1024 : ℝ)) b (fp.retainedV
      (↑G : bf.Grp) b S.K) (c l G b)‖ ^ (2 : ℕ) ≤ (24 : ℝ) * ((↑⌊(180 : ℝ) * (↑S.dmax :
      ℝ) * Real.log ((2 : ℝ) * S.Dm) / (1 / 1024 : ℝ)⌋₊ : ℝ) + (1 : ℝ)) * (Real.exp
      (((6144 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) * ((1024 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) + (↑cc
      : ℝ) + (7 : ℝ)) + (4 : ℝ)) * ((1 : ℝ) + Real.log ((2 : ℝ) * (↑k : ℝ))) ^ (2 : ℕ))
      + (2 : ℝ) * (1 : ℝ) / S.Dstar ^ (394 : ℕ)) * dyadicGridLength A.G A.R.1)
    (Rr : (l : Fin (4 : ℕ)) → (h : ℕ) → ℕ × ℕ → (G : ↥gset) → (Ms l (↑G : bf.Grp)).RepClass
      (S.withQ0 (qG (↑G : bf.Grp))) hA6 (S.sideParams (1 / 1024 : ℝ)) (10 : ℕ) h)
    (_ : ∀ (l : Fin (4 : ℕ)), ∀ h ≤ S.Jstar, ∀ (t : ℕ × ℕ) (G : ↥gset), (Rr l h t G).Nd = {c
      ∈ (Ms l (↑G : bf.Grp)).succNodes (S.withQ0 (qG (↑G : bf.Grp))) hA6 (S.sideParams
      (1 / 1024 : ℝ)) (fp.retainedPairs (↑G : bf.Grp) (Finset.image (fun (β : ℕ) =>
      A.R.1 + (↑(S.K * β) : ℤ)) (Finset.range (A.treeDepth + (1 : ℕ)))) S.K) h | (Ms l
      (↑G : bf.Grp)).nodeType1 (S.withQ0 (qG (↑G : bf.Grp))) hA6 (10 : ℕ) h c = t.1 ∧
      (Ms l (↑G : bf.Grp)).nodeType2 (S.withQ0 (qG (↑G : bf.Grp))) hA6 (10 : ℕ) h c =
      t.2})
    (Cut : Fin (4 : ℕ) → Finset (ℤ × ℤ))
    (_ : ∀ (l : Fin (4 : ℕ)), dyadicRootLength A.G (Cut l) ≤ ρ * dyadicGridLength A.G A.R.1)
    (_ : ∀ (l : Fin (4 : ℕ)) (y : ℝ), ∀ h ∈ Finset.range (S.Jstar + (1 : ℕ)), ∀ t ∈ Ts, ∀ σ ∈
      dyThr ε U S.Dstar, ∑ G : ↥gset, (↑(Finset.image (fun (p : (ℤ × ℤ) × ℤ × (ℤ × ℤ) ×
      (Ms l (↑G : bf.Grp)).Md) => (Rr l h t G).rep p.2) ({p ∈ fp.useInst (↑G : bf.Grp)
      S.K (Rr l h t G).Nd | (∀ e ∈ Cut l, ¬dyadicGridCell A.G p.1.1 p.1.2 ⊆
      dyadicGridCell A.G e.1 e.2) ∧ y ∈ dyadicGridCell A.G p.1.1 p.1.2 ∧ σ ^ (2 : ℕ) ≤
      (Ms l (↑G : bf.Grp)).nodeSize (S.withQ0 (qG (↑G : bf.Grp))) hA6 (S.sideParams (1 /
      1024 : ℝ)) (c l G) h p})).card : ℝ) ≤ min S.Dstar ((24 : ℝ) * ((2 : ℝ) * Real.exp
      (((6144 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) * ((1024 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) + (↑cc
      : ℝ) + (7 : ℝ)) + (4 : ℝ)) * ((1 : ℝ) + Real.log ((2 : ℝ) * (↑k : ℝ))) ^ (2 : ℕ))
      + (2 : ℝ) * (↑S.K : ℝ) * ((24 : ℝ) * ((↑⌊(180 : ℝ) * (↑S.dmax : ℝ) * Real.log ((2
      : ℝ) * S.Dm) / (1 / 1024 : ℝ)⌋₊ : ℝ) + (1 : ℝ)) * (Real.exp (((6144 : ℝ) * ((↑cc :
      ℝ) + (1 : ℝ)) * ((1024 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) + (↑cc : ℝ) + (7 : ℝ)) + (4 :
      ℝ)) * ((1 : ℝ) + Real.log ((2 : ℝ) * (↑k : ℝ))) ^ (2 : ℕ)) + (2 : ℝ) * (1 : ℝ) /
      S.Dstar ^ (394 : ℕ)))) * (↑(Finset.range (S.Jstar + (1 : ℕ)) ×ˢ Ts ×ˢ dyThr ε U
      S.Dstar).card : ℝ) / (ρ * σ ^ (2 : ℕ)))),
  let gE : ℤ × ℤ → Fin A.famVtxBound → bf.Grp :=
    fun (I : ℤ × ℤ) (i : Fin A.famVtxBound) => if h : (↑i : ℕ) < (gs I).card then
      (↑(((gs I).equivFin.symm : Fin (gs I).card → ↥(gs I)) ⟨(↑i : ℕ), h⟩) : bf.Grp)
      else default
  ∀ (_ : ∀ (I : ℤ × ℤ), ∀ G ∈ gs I, ∃ (i : Fin A.famVtxBound), gE I i = G),
  let Wm : Type :=
    { x : (_ : Fin (4 : ℕ)) × (I : ↥AD.Tc) × fp.TestName (↑I : ℤ × ℤ) Unit // fp.MainRk
      x.snd.snd }
  let main : Wm → Fin (4 : ℕ) × (ℤ × ℤ) × MainTest bf.Vtx bf.Lab fp.Mc :=
    fun (x : Wm) => ((↑x : (_ : Fin (4 : ℕ)) × (I : ↥AD.Tc) × fp.TestName (↑I : ℤ × ℤ)
      Unit).fst, (↑(↑x : (_ : Fin (4 : ℕ)) × (I : ↥AD.Tc) × fp.TestName (↑I : ℤ × ℤ)
      Unit).snd.fst : ℤ × ℤ), fp.testOf (↑x : (_ : Fin (4 : ℕ)) × (I : ↥AD.Tc) ×
      fp.TestName (↑I : ℤ × ℤ) Unit).fst (↑(↑x : (_ : Fin (4 : ℕ)) × (I : ↥AD.Tc) ×
      fp.TestName (↑I : ℤ × ℤ) Unit).snd.fst : ℤ × ℤ) (fun (_ : Unit) => bf.patIn fp.Mc
      p (↑(↑x : (_ : Fin (4 : ℕ)) × (I : ↥AD.Tc) × fp.TestName (↑I : ℤ × ℤ)
      Unit).snd.fst : ℤ × ℤ) (↑x : (_ : Fin (4 : ℕ)) × (I : ↥AD.Tc) × fp.TestName (↑I :
      ℤ × ℤ) Unit).fst) (↑x : (_ : Fin (4 : ℕ)) × (I : ↥AD.Tc) × fp.TestName (↑I : ℤ ×
      ℤ) Unit).snd.snd)
  ∀ (_ : ∀ (i : Wm), (main i).2.2.r ≤ fp.Lc + (4 : ℕ) ∧ ∀ l' < (main i).2.2.m, (main
      i).2.2.hr l' ≤ fp.Lc + (4 : ℕ)),
  ∃ (F : Fin (6 : ℕ) → Finset (ℤ × ℤ)), (∀ (i : Fin (6 : ℕ)), ∀ c ∈ F i,
    dyadicGridCell A.G c.1 c.2 ⊆ dyadicGridCell A.G A.R.1 A.R.2) ∧ (∀ (i : Fin (6 :
    ℕ)), dyadicRootLength A.G (F i) ≤ (2 : ℝ) * ρ * dyadicGridLength A.G A.R.1) ∧ ∀ cs
    ⊆ AD.Tc, (∀ I ∈ cs, ¬∃ c ∈ fp.failRoots, dyadicGridCell A.G I.1 I.2 ⊆
    dyadicGridCell A.G c.1 c.2) → (∀ I ∈ cs, ∀ (i : Fin (6 : ℕ)), ∀ e ∈ F i,
    ¬dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G e.1 e.2) → ∑ I ∈ cs,
    dyadicGridLength A.G I.1 * min A.η ‖∑ G ∈ fp.groupsAt I ks, (fp.Λc I : (Fin (4 :
    ℕ) → ↥(ColumnL2 (bf.Lab ⊕ Fin fp.Mc))) → ℂ) fun (l : Fin (4 : ℕ)) => (fp.ballFilt
    l (AD.cat l) I G (Lf.role l) : ↥(ColumnL2 (bf.Lab ⊕ Fin fp.Mc)) → ↥(ColumnL2
    (bf.Lab ⊕ Fin fp.Mc))) (fp.inputL AD.cat I (bf.patIn fp.Mc p I) Lf.layers l)‖ ≤
    leafBnd Cl kD fp.P k cc A.η η₀ AD.τ₃ δ (finiteDepthConstant κ q Nd) (nbCM κ hq2
    hq3 + nbCUM κ hq2 hq3) q (dyadicGridLength A.G A.R.1)


open scoped Classical in
private def LeafEstimateStage2Statement : Prop :=
  ∀ (κ : LocalKernelClass)
    (c₀ : ℕ)
    (cc : ℕ)
    (_ : (1 : ℕ) ≤ cc)
    (Dm0 : ℕ)
    (Msch : ℝ)
    (_ : (0 : ℝ) < Msch)
    (Cg : ℕ)
    (_ : ∀ {κ : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ c₀} {bf : A.BasicFamilies} (fp
      : bf.FamParams) (dB : ℕ) {H δc N k δ : ℝ}, (1 : ℝ) ≤ k → (↑fp.Lc : ℝ) + (6 : ℝ) ≤
      k ^ (cc + (6 : ℕ)) → (↑fp.Hmax : ℝ) + (1 : ℝ) ≤ (k * (↑fp.P : ℝ)) ^ (cc + (6 : ℕ))
      → (↑dB : ℝ) ≤ k ^ (cc + (6 : ℕ)) → (2 : ℝ) ≤ fp.Hed → Real.log fp.Hed ≤ k ^ (cc +
      (6 : ℕ)) → (1 : ℝ) ≤ H → Real.log H ≤ k ^ (cc + (6 : ℕ)) → (0 : ℝ) < δc → δc⁻¹ ≤
      Real.exp (k ^ (cc + (6 : ℕ))) → (0 : ℝ) ≤ N → N ≤ Real.exp (k ^ (cc + (6 : ℕ))) →
      A.colBudget ≤ Real.exp (k ^ (cc + (6 : ℕ))) → (0 : ℝ) < δ → δ⁻¹ ≤ Real.exp (k ^
      (cc + (6 : ℕ))) → Real.log (fp.modeStarG Dm0 dB H δc N k δ) ≤ (↑Cg : ℝ) * (k *
      (↑fp.P : ℝ)) ^ Cg ∧ Real.log ((2 : ℝ) ^ (fp.Kstar Dm0 dB H δc N k δ + (1 : ℕ))) ≤
      (↑Cg : ℝ) * (k * (↑fp.P : ℝ)) ^ Cg)
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
    (eΛ : ℕ)
    (CM1 : ℕ)
    (t3 : ℕ)
    (Cb : ℕ)
    (Cl : ℕ)
    (_ : g = (8192 : ℕ) * (cc + (1 : ℕ)) * ((1024 : ℕ) * (cc + (1 : ℕ)) + cc + (7 : ℕ)) + cc
      ^ (2 : ℕ) + (8 : ℕ) ∧ cT = (10 : ℝ) ^ (22 : ℕ) * ((1 : ℝ) +
      localFormUniformConstant κ) ^ (2 : ℕ) ∧ cL = (159 : ℝ) + (32 : ℝ) * (↑g : ℝ) + (8
      : ℝ) * Real.log cT ∧ cK = ((1 : ℝ) + (7 : ℝ) * (10 : ℝ) ^ (9 : ℕ) + cT) * (cL + (2
      : ℝ)) ∧ cMc = (C4c κ + (4 : ℝ) * C3c κ) * cL ^ (4 : ℕ) * cK ^ (2 : ℕ) ∧ cm =
      (196608 : ℝ) * cT + (83 : ℝ) * ((1 : ℝ) + (81 : ℝ) * localFormUniformConstant κ *
      ((30000 : ℝ) + √cT)) * ((1 : ℝ) + cT) ^ (3 : ℕ) + cMc ∧ ce = (6642 : ℝ) *
      localFormUniformConstant κ * ((60000 : ℝ) + √cT) ^ (3 : ℕ) * (288 : ℝ) + (9 : ℝ) *
      ((16 : ℝ) * fourErrC κ (3 : ℕ) + (648 : ℝ) * threeErrC κ (3 : ℕ) (1 : ℕ) + (324 :
      ℝ) * threeErrC κ (3 : ℕ) (1 : ℕ) * √cT) ∧ ce2 = K1c * ((2 : ℝ) * fourKC κ (3 : ℕ)
      * (12 : ℝ) ^ (4 : ℕ)) + (4 : ℝ) * (K1c * ((8 : ℝ) * entryCU κ (3 : ℕ) (1 : ℕ) * (2
      : ℝ) ^ ((1 : ℕ) + (4 : ℕ)) * (12 : ℝ) ^ (3 : ℕ))) * (501 : ℝ) ∧ cQ = (65536 : ℝ) *
      ((8 : ℝ) + (80 : ℝ) * (9 : ℝ) ^ cc * (↑cc : ℝ)) * ((80 : ℝ) * (9 : ℝ) ^ cc * (↑cc
      : ℝ)) * ((4 : ℝ) * (↑cc : ℝ) ^ (2 : ℕ)) * ((17 : ℝ) * (10 : ℝ) ^ (7 : ℕ)) ∧ CΛ =
      (2 : ℕ) * Cg + (12 : ℕ) ∧ eΛ = Cg + (3 : ℕ) * cc ∧ CM1 = (⌈Msch⌉₊ + (1 : ℕ)) * CΛ
      ^ (16 : ℕ) ∧ t3 = (3 : ℕ) ^ cc ∧ Cb = CM1 + (501 : ℕ) * Cg + t3 + (2 : ℕ) * cc +
      (20 : ℕ) + (16 : ℕ) * eΛ ∧ Cl = ⌈cm * (↑Cb : ℝ) ^ (59 : ℕ) + ce * (↑Cb : ℝ) ^ (18
      : ℕ) + ce2 + (3 : ℝ) * (10 : ℝ) ^ (11 : ℕ) * cQ⌉₊ + (59 : ℕ) * Cb + (4 : ℕ) * g +
      (8 : ℕ) * cc + (8 : ℕ))
    (A : ActiveSetup κ c₀)
    (bf : A.BasicFamilies)
    (k : ℕ)
    (η₀ : ℝ)
    (E : ℝ)
    (_ : A.AncClosed)
    (_ : ∀ I ∈ A.cells, ∀ (s s' : Fin (4 : ℕ)), s ≠ s' → PairSmall (dyadicGridLeft A.G I.1
      I.2) (dyadicGridLength A.G I.1) (A.w I) s s' (A.Y I s) (A.Y I s') ((2 : ℝ) * η₀))
    (_ : A.SubRootProps η₀ E)
    (_ : A.S = (2 : ℝ))
    (_ : A.η = (4 : ℝ) * η₀)
    (_ : (0 : ℝ) < η₀)
    (_ : A.cells.Nonempty)
    (q : ℝ)
    (hq2 : (2 : ℝ) < q)
    (hq3 : q < (3 : ℝ))
    (Nd : ℕ)
    (_ : A.DepthWin Nd)
    (p : Fin (3 : ℕ))
    (AD : bf.AttemptData p)
    (d : bf.Vtx)
    (s : ℕ)
    (δ : ℝ)
    (ρ : ℝ)
    (kD : ℝ)
    (_ : (0 : ℝ) < δ)
    (_ : δ ≤ (1 / 8 : ℝ))
    (_ : (0 : ℝ) < ρ)
    (_ : ρ < (1 : ℝ))
    (_ : Real.log ((2 : ℝ) * A.colBudget) ≤ (↑k : ℝ) ^ cc)
    (_ : (↑((2 : ℕ) * A.famFuel + (2 : ℕ)) : ℝ) ≤ (↑cc : ℝ) * (Real.log (↑k : ℝ) + (1 : ℝ)))
    (_ : (1 : ℝ) ≤ (↑k : ℝ)),
  let fp : bf.FamParams :=
    AD.fp
  let dB : ℕ :=
    A.dBnd
  ∀ (_ : (↑fp.Lc : ℝ) + (6 : ℝ) ≤ (↑k : ℝ) ^ cc ∧ (↑fp.Hmax : ℝ) + (1 : ℝ) ≤ ((↑k : ℝ) *
      (↑fp.P : ℝ)) ^ cc ∧ (↑dB : ℝ) ≤ (↑k : ℝ) ^ cc ∧ Real.log fp.Hed ≤ (↑k : ℝ) ^ cc ∧
      Real.log A.Hsrc ≤ (↑k : ℝ) ^ cc ∧ Real.log (max A.H padW) ≤ (↑k : ℝ) ^ cc ∧ δ⁻¹ ≤
      Real.exp kD ∧ E ≤ (↑k : ℝ) ^ cc ∧ ρ⁻¹ ≤ (↑k : ℝ) ^ cc ∧ (2 : ℝ) + Real.log
      bumpConst + (100 : ℝ) ≤ (↑k : ℝ) ∧ (↑k : ℝ) ^ cc ≤ kD ∧ (2 : ℝ) ≤ (↑k : ℝ) ∧ (0 :
      ℝ) ≤ Real.log bumpConst)
    (_ : (8 : ℝ) * (↑dB : ℝ) * δ ≤ (1 : ℝ)),
  let Nl : ℝ :=
    AD.n (fp.Lc + (5 : ℕ))
  ∀ (_ : Real.log ((2 : ℝ) * ((8 : ℝ) * A.colBudget + ((1 : ℝ) + (↑AD.Mp : ℝ)) * Nl)) ≤ (↑k :
      ℝ) ^ cc)
    (_ : (2 : ℝ) ≤ A.colBudget)
    (_ : Monotone AD.n)
    (hNl0 : (0 : ℝ) ≤ Nl),
  let Hm : ℝ :=
    max (max A.Hsrc (Real.exp (↑dB : ℝ))) (max ((5832 : ℝ) * max A.H padW ^ (4 : ℕ))
      ((↑dB : ℝ) * (bumpConst * (8 : ℝ) ^ (32 : ℕ) * ((2 : ℝ) / δ))))
  ∀ (_ : (1 : ℝ) ≤ Hm)
    (_ : ∀ (w : bf.Vtx), (bf.vtag w).dim ≤ dB)
    (_ : ∀ (w : bf.Vtx) (a c : Fin (bf.vtag w).dim), (↑(rationalHeight ((bf.vtag w).C a c)) :
      ℝ) ≤ fp.Hed)
    (S : ModeSchedule)
    (_ : S.dmax = (2 : ℕ) * dB + (2 : ℕ))
    (_ : S.Dm = max (2 : ℝ) Nl)
    (_ : S.Q0 = fp.Q0bd dB)
    (_ : S.Valid (340 : ℕ) (5 : ℕ) (4 : ℕ) (600 : ℕ) (1 / 1024 : ℝ) (packetW S.dmax S.H))
    (_ : (8 : ℝ) * ((↑S.dmax : ℝ) + (1 : ℝ)) ^ (3 : ℕ) * Real.log ((2 : ℝ) * S.H) / Real.log
      (2 : ℝ) ≤ packetW S.dmax S.H)
    (_ : (2 : ℕ) ≤ S.dmax)
    (_ : (↑S.dmax : ℝ) ≤ S.Dstar)
    (_ : (2 : ℝ) ≤ S.Dstar)
    (_ : (2 : ℝ) ≤ S.Bstar)
    (_ : (1 : ℕ) ≤ S.Q0)
    (_ : (↑S.Q0 : ℝ) * (2 : ℝ) ^ (fp.Kstar Dm0 dB Hm δ Nl kD δ + (1 : ℕ)) ≤ S.Bstar)
    (_ : Real.log S.H ≤ Msch * ((↑((2 : ℕ) * dB + (2 : ℕ)) : ℝ) + Real.log (fp.modeStarG Dm0
      dB Hm δ Nl kD δ) + Real.log (fp.Bst Dm0 dB Hm δ Nl kD δ) + Real.log (max (2 : ℝ)
      Nl) + Real.log (↑(fp.Q0bd dB) : ℝ) + (1 : ℝ)) ^ (12 : ℕ))
    (_ : (↑S.K : ℝ) ≤ Msch * ((↑((2 : ℕ) * dB + (2 : ℕ)) : ℝ) + Real.log (fp.modeStarG Dm0 dB
      Hm δ Nl kD δ) + Real.log (fp.Bst Dm0 dB Hm δ Nl kD δ) + Real.log (max (2 : ℝ) Nl)
      + Real.log (↑(fp.Q0bd dB) : ℝ) + (1 : ℝ)) ^ (16 : ℕ))
    (_ : (1 : ℕ) ≤ S.K),
  let Lf : SearchLeaf :=
    leafAt A.famFuel fp.Lc (A.basicSlot p) s
  ∀ (_ : Lf = leafAt A.famFuel fp.Lc (A.basicSlot p) s),
  let ks : ℕ :=
    Lf.k
  let S0 : Finset (ℤ × ℤ) :=
    {I ∈ AD.Tc | ¬∃ c ∈ fp.failRoots, dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G
      c.1 c.2}
  ∀ (_ : S0 ⊆ AD.Tc)
    (_ : S0 ⊆ A.cells),
  let gs : ℤ × ℤ → Finset bf.Grp :=
    fun (I : ℤ × ℤ) => fp.groupsAt I ks
  let gset : Finset bf.Grp :=
    S0.biUnion gs
  ∀ (_ : ∀ I ∈ S0, ∀ G ∈ gs I, fp.Cert ks G I ∧ fp.ActualUse G I),
  let U_1 : Fin (4 : ℕ) → bf.Grp → Finset (ℤ × ℤ) :=
    fun (_ : Fin (4 : ℕ)) (G : bf.Grp) => {I ∈ S0 | G ∈ gs I}
  ∀ (hlenMc : ∀ (l : Fin (4 : ℕ)), (AD.cat l).length ≤ fp.Mc),
  let mbs : (l : Fin (4 : ℕ)) → bf.MainBudget (AD.cat l) :=
    fun l => MainBudget.ofCounts bf fp.Mc (AD.cat l) (hlenMc l) l (fun e he => AD.hTc
      (AD.hT l e he).1) (fun e he => (AD.hT l e he).2.1) hNl0 (fun I _ => AD.hlab l I _
      le_rfl)
  ∀ (_ : ∀ (l : Fin (4 : ℕ)), ∀ I ∈ A.cells, (↑(mainLabels A.G fp.Mc (bf.origCols l) (AD.cat
      l) I (fp.brank (Lf.role l))).card : ℝ) ≤ Nl)
    (Ms : Fin (4 : ℕ) → bf.Grp → ModeSystem A.G (Fintype.card (bf.Lab ⊕ Fin fp.Mc)))
    (L : (l : Fin (4 : ℕ)) → (G : bf.Grp) → LiftData (bf.Lab ⊕ Fin fp.Mc) (Ms l G).Md)
    (_ : ∀ (l : Fin (4 : ℕ)), ∀ G ∈ gset, fp.ModeExports l (AD.cat l) G (Lf.role l) d Dm0 dB
      Hm δ δ Nl (Ms l G) (L l G))
    (_ : ∀ (l : Fin (4 : ℕ)), ∀ G ∉ gset, (∀ (p : (Ms l G).Key), (Ms l G).dvOf p + (Ms l
      G).zc.dim ≤ (2 : ℕ) * dB + (2 : ℕ)) ∧ (Ms l G).Bσ = (1 : ℝ) ∧ ∀ (V : ℤ × ℤ), (Ms l
      G).alive V = ∅)
    (_ : PLift (∑ l : Fin (4 : ℕ), ∑ G ∈ gset, ∑ I ∈ U_1 l G, ∫ (y : ℝ) in dyadicGridCell A.G
      I.1 I.2, ‖((↑(↑(fp.physError (Ms l G) (L l G) l (AD.cat l) (mbs l) G (Lf.role l)
      (Lf.layers l) S.K (A.blkStart S.K I.1)) : ℝ →ₘ[volume] ColumnHilbert (bf.Lab ⊕ Fin
      fp.Mc)) : ℝ → ColumnHilbert (bf.Lab ⊕ Fin fp.Mc)) y).ofLp none‖ ^ (2 : ℕ) ≤ ((8 :
      ℝ) * (↑dB : ℝ) * δ + (2 : ℝ) * δ ^ (2 : ℕ)) * ((4 : ℝ) * Nl * A.colBudget ^ (2 :
      ℕ) * (1 : ℝ)) * (↑((4 : ℕ) * (AD.Mp * A.famVtxBound)) : ℝ) * dyadicGridLength A.G
      A.R.1))
    (_ : S.Dstar = fp.modeStarG Dm0 dB Hm δ Nl kD δ)
    (_ : ∀ (l : Fin (4 : ℕ)), ∀ G ∈ gset, (∀ (q : (Ms l G).Key), (Ms l G).dvOf q + (Ms l
      G).zc.dim ≤ (2 : ℕ) * dB + (2 : ℕ)) ∧ (Ms l G).Λ ≤ S.Dstar ∧ gaugeSqNorm (Ms l
      G).zc.dim (Ms l G).δc ≤ S.Dstar ∧ (2 : ℝ) * gaugeTail (Ms l G).zc.dim (Ms l G).δc
      / (2 : ℝ) ^ fp.Kstar Dm0 dB Hm δ Nl kD δ * S.Dstar ^ (300 : ℕ) ≤ (1 : ℝ) ∧ (∀ (m :
      (Ms l G).Md), S.Dstar⁻¹ ≤ (Ms l G).L.εM m) ∧ (∀ (V : ℤ × ℤ), (↑((Ms l G).alive
      V).card : ℝ) ≤ S.Dstar) ∧ ∀ (V : ℤ × ℤ), (↑(Finset.image (Ms l G).keyOf ((Ms l
      G).alive V)).card : ℝ) ≤ Nl)
    (_ : (6 : ℝ) ≤ S.A0),
  let qG : bf.Grp → ℕ :=
    fun (G : bf.Grp) => clearInt (bf.vtag (bf.grpCenter d G)).C
  ∀ (_ : ∀ (G : bf.Grp), (1 : ℕ) ≤ qG G ∧ qG G ≤ S.Q0)
    (Vl0 : ℝ)
    (_ : Vl0 = (24 : ℝ) * ((↑⌊(180 : ℝ) * (↑S.dmax : ℝ) * Real.log ((2 : ℝ) * S.Dm) / (1 /
      1024 : ℝ)⌋₊ : ℝ) + (1 : ℝ)) * (Real.exp (((6144 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) *
      ((1024 : ℝ) * ((↑cc : ℝ) + (1 : ℝ)) + (↑cc : ℝ) + (7 : ℝ)) + (4 : ℝ)) * ((1 : ℝ) +
      Real.log ((2 : ℝ) * (↑k : ℝ))) ^ (2 : ℕ)) + (2 : ℝ) * (1 : ℝ) / S.Dstar ^ (394 :
      ℕ)))
    (U : ℝ)
    (_ : U = max ((2 : ℝ) * (A.colBudget + (2 : ℝ)) * S.Dstar ^ (2 : ℕ)) √(TsideF A fp.P S.K
      (A.uslot p) ((2 : ℕ) ^ A.famFuel) ((2 : ℕ) * A.famFuel + (2 : ℕ)) (1 : ℝ) E cc (↑k
      : ℝ) (fun (_ : Fin (4 : ℕ)) => Vl0) ρ))
    (_ : (2 : ℝ) * (A.colBudget + (2 : ℝ)) * S.Dstar ^ (2 : ℕ) ≤ U)
    (_ : (0 : ℝ) < S.Dstar)
    (_ : (1 : ℝ) ≤ S.Dstar)
    (_ : (16 : ℝ) ≤ U)
    (_ : (0 : ℝ) < U)
    (MV : ℝ)
    (_ : MV = (↑AD.Mp : ℝ) * (↑A.famVtxBound : ℝ))
    (_ : (0 : ℝ) ≤ MV)
    (ε : ℝ)
    (_ : ε = (U ^ (3 : ℕ) * S.Dstar ^ (5 : ℕ) * Real.exp (↑k : ℝ) * ((1 : ℝ) + MV))⁻¹)
    (_ : (0 : ℝ) < ε)
    (_ : ε ≤ U)
    (_ : S.Dstar⁻¹ ≤ U)
    (_ : (dyThr ε U S.Dstar).Nonempty)
    (_ : ∀ σ ∈ dyThr ε U S.Dstar, S.Dstar⁻¹ ≤ σ)
    (_ : ∀ (σ : ℝ), ε ≤ σ → σ ≤ U → (∃ (k : ℤ), σ = (2 : ℝ) ^ k) → S.Dstar⁻¹ ≤ σ → σ ∈ dyThr
      ε U S.Dstar)
    (_ : (↑(dyThr ε U S.Dstar).card : ℝ) ≤ Real.logb (2 : ℝ) U - Real.logb (2 : ℝ) ε + (3 :
      ℝ)),
  let Ts : Finset (ℕ × ℕ) :=
    Finset.range (Nat.log (2 : ℕ) ⌊S.Dstar⌋₊ + (1 : ℕ)) ×ˢ Finset.range (Nat.log (2 : ℕ)
      ⌊S.Dstar⌋₊ + (1 : ℕ))
  ∀ (_ : Ts = Finset.range (Nat.log (2 : ℕ) ⌊S.Dstar⌋₊ + (1 : ℕ)) ×ˢ Finset.range (Nat.log (2
      : ℕ) ⌊S.Dstar⌋₊ + (1 : ℕ)))
    (_ : Ts.Nonempty),
  let BN : ℕ :=
    ⌈(8 : ℝ) * A.colBudget + Nl⌉₊
  let τb : ℝ :=
    (1 : ℝ) / ((1 : ℝ) + (↑BN : ℝ) * A.colBudget ^ (2 : ℕ))
  ∀ (_ : (0 : ℝ) < τb)
    (_ : τb ≤ (1 : ℝ))
    (_ : τb * (↑BN : ℝ) * A.colBudget ^ (2 : ℕ) ≤ (1 : ℝ))
    (_ : Real.exp ((↑A.Dg : ℝ) * ((1 : ℝ) + Real.log A.Hsrc + Real.log τb⁻¹) ^ A.Dg) ≤ fp.Hed)
    (_ : ∀ I ∈ A.cells, dyadicGridCell A.G I.1 I.2 ⊆ Set.Icc (dyadicGridLeft A.G A.R.1 A.R.2)
      (dyadicGridLeft A.G A.R.1 A.R.2 + dyadicGridLength A.G A.R.1))
    (ρ₀ : Fin (4 : ℕ) → ↥gset → Fin A.fcd0)
    (zc : Fin (4 : ℕ) → ↥gset → bf.Vtx)
    (gsc : Fin (4 : ℕ) → ↥gset → ℤ)
    (_ : ∀ (l : Fin (4 : ℕ)) (G : ↥gset), (↑G : bf.Grp).2.1 = some (ρ₀ l G, zc l G, gsc l G))
    (_ : ∀ (l : Fin (4 : ℕ)) (G : ↥gset), fp.MainLiftExports l (AD.cat l) (↑G : bf.Grp)
      (Lf.role l) d Dm0 dB Hm (gsc l G) (L l (↑G : bf.Grp)) (Ms l (↑G : bf.Grp)).wave
      (Ms l (↑G : bf.Grp)).cellOf)
    (_ : ∀ (l : Fin (4 : ℕ)) (G : ↥gset) (m : (Ms l (↑G : bf.Grp)).Md), (L l (↑G :
      bf.Grp)).εM m = (Ms l (↑G : bf.Grp)).L.εM m)
    (_ : ∀ (l : Fin (4 : ℕ)) (G : ↥gset), (Ms l (↑G : bf.Grp)).δc = δ)
    (_ : ∀ (G : ↥gset), (↑G : bf.Grp).1 = ks)
    (_ : ∀ (l : Fin (4 : ℕ)), fp.bbase (Lf.role l) + fp.P ≤ fp.Hmax),
  ∃ (F : Fin (6 : ℕ) → Finset (ℤ × ℤ)), (∀ (i : Fin (6 : ℕ)), ∀ c ∈ F i,
    dyadicGridCell A.G c.1 c.2 ⊆ dyadicGridCell A.G A.R.1 A.R.2) ∧ (∀ (i : Fin (6 :
    ℕ)), dyadicRootLength A.G (F i) ≤ (2 : ℝ) * ρ * dyadicGridLength A.G A.R.1) ∧ ∀ cs
    ⊆ AD.Tc, (∀ I ∈ cs, ¬∃ c ∈ fp.failRoots, dyadicGridCell A.G I.1 I.2 ⊆
    dyadicGridCell A.G c.1 c.2) → (∀ I ∈ cs, ∀ (i : Fin (6 : ℕ)), ∀ e ∈ F i,
    ¬dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G e.1 e.2) → ∑ I ∈ cs,
    dyadicGridLength A.G I.1 * min A.η ‖∑ G ∈ fp.groupsAt I ks, (fp.Λc I : (Fin (4 :
    ℕ) → ↥(ColumnL2 (bf.Lab ⊕ Fin fp.Mc))) → ℂ) fun (l : Fin (4 : ℕ)) => (fp.ballFilt
    l (AD.cat l) I G (Lf.role l) : ↥(ColumnL2 (bf.Lab ⊕ Fin fp.Mc)) → ↥(ColumnL2
    (bf.Lab ⊕ Fin fp.Mc))) (fp.inputL AD.cat I (bf.patIn fp.Mc p I) Lf.layers l)‖ ≤
    leafBnd Cl kD fp.P k cc A.η η₀ AD.τ₃ δ (finiteDepthConstant κ q Nd) (nbCM κ hq2
    hq3 + nbCUM κ hq2 hq3) q (dyadicGridLength A.G A.R.1)


open scoped Classical in
private def LeafEstimateStage1Statement : Prop :=
  ∀ (κ : LocalKernelClass)
    (c₀ : ℕ)
    (cc : ℕ)
    (_ : (1 : ℕ) ≤ cc)
    (Dm0 : ℕ)
    (_ : ∀ (A : ActiveSetup κ c₀) (bf : A.BasicFamilies) (fp : bf.FamParams) (cat : Fin (4 :
      ℕ) → List (CatCol bf.Vtx)), (∀ (l : Fin (4 : ℕ)), ∀ e ∈ cat l, ∃ R ∈ residueBox
      (bf.vtag e.tag).dim (9 : ℕ), ∃ (γ : ℝ), e = templateCol (bf.vtag e.tag) l R γ
      e.birth e.rank e.tag) → (∀ (l : Fin (4 : ℕ)), ∀ e ∈ cat l, bf.occAvail (↑e.tag.2 :
      ℤ × ℤ) e.tag.1) → ∀ (mbs : (l : Fin (4 : ℕ)) → bf.MainBudget (cat l)) (jj : Fin (4
      : ℕ) → ℕ) (lsi : Fin (4 : ℕ) → List (ℕ × Bool)) (d : bf.Vtx) (gset : Finset
      bf.Grp), (∀ G ∈ gset, ∃ (I : ℤ × ℤ), fp.ActualUse G I) → A.AncClosed → ∀ {K : ℕ}
      (blk : ℤ × ℤ → ℤ), (∀ (I : ℤ × ℤ), blk I ≤ I.1 ∧ I.1 < blk I + (↑K : ℤ)) → ∀ (U :
      Fin (4 : ℕ) → bf.Grp → Finset (ℤ × ℤ)), (∀ (l : Fin (4 : ℕ)) (G : bf.Grp), ∀ I ∈ U
      l G, fp.ActualUse G I) → ∀ {Nuse : ℕ}, (∀ (y : ℝ), ∑ l : Fin (4 : ℕ), ∑ G ∈ gset,
      (Finset.card ({I ∈ U l G | y ∈ dyadicGridCell A.G I.1 I.2})) ≤ Nuse) → (2 : ℝ) ≤
      fp.Hed → ∀ {dB : ℕ}, (∀ (w : bf.Vtx), (bf.vtag w).dim ≤ dB) → (∀ (w : bf.Vtx) (a c
      : Fin (bf.vtag w).dim), (↑(rationalHeight ((bf.vtag w).C a c)) : ℝ) ≤ fp.Hed) → ∀
      {δ : ℝ}, (0 : ℝ) < δ → δ ≤ (1 / 8 : ℝ) → (8 : ℝ) * (↑dB : ℝ) * δ ≤ (1 : ℝ) → ∀ {H
      : ℝ}, A.Hsrc ≤ H → (↑dB : ℝ) ≤ Real.log H → (∀ (w : bf.Vtx) (l : Fin (4 : ℕ)) (i k
      : Fin (bf.vtag w).dim), (↑(chartRationalHeight (((↑(-slotCoeff l) : ℚ) • (bf.vtag
      w).C) i k)) : ℝ) ≤ H) → (↑dB : ℝ) * (bumpConst * (8 : ℝ) ^ (32 : ℕ) * ((2 : ℝ) /
      δ)) ≤ H → ∀ {δc : ℝ}, (0 : ℝ) < δc → ∀ {N CF : ℝ}, (0 : ℝ) ≤ N → (0 : ℝ) ≤ CF → (∀
      (l : Fin (4 : ℕ)), ∀ I ∈ A.cells, (↑(mainLabels A.G fp.Mc (bf.origCols l) (cat l)
      I (fp.brank (jj l))).card : ℝ) ≤ N) → δc ^ (2 : ℕ) * N * A.colBudget ^ (2 : ℕ) ≤
      (1 : ℝ) → (∀ (l : Fin (4 : ℕ)) (jb : Fin (2 : ℕ)), ∀ V ∈ A.cells,
      ‖(columnL2Restriction (dyadicGridCell A.G V.1 V.2) (dyadicGridCell_measurable A.G
      V.1 V.2) : ↥(ColumnL2 (bf.P l jb).V) → ↥(ColumnL2 (bf.P l jb).V)) (bf.P l jb).Z‖ ^
      (2 : ℕ) ≤ CF * dyadicGridLength A.G V.1) → ∃ (Ms : Fin (4 : ℕ) → bf.Grp →
      ModeSystem A.G (Fintype.card (bf.Lab ⊕ Fin fp.Mc))) (L : (l : Fin (4 : ℕ)) → (G :
      bf.Grp) → LiftData (bf.Lab ⊕ Fin fp.Mc) (Ms l G).Md), (∀ (l : Fin (4 : ℕ)), ∀ G ∈
      gset, fp.ModeExports l (cat l) G (jj l) d Dm0 dB H δ δc N (Ms l G) (L l G)) ∧ (∀
      (l : Fin (4 : ℕ)), ∀ G ∉ gset, (∀ (p : (Ms l G).Key), (Ms l G).dvOf p + (Ms l
      G).zc.dim ≤ (2 : ℕ) * dB + (2 : ℕ)) ∧ (Ms l G).Bσ = (1 : ℝ) ∧ ∀ (V : ℤ × ℤ), (Ms l
      G).alive V = ∅) ∧ ∑ l : Fin (4 : ℕ), ∑ G ∈ gset, ∑ I ∈ U l G, ∫ (y : ℝ) in
      dyadicGridCell A.G I.1 I.2, ‖((↑(↑(fp.physError (Ms l G) (L l G) l (cat l) (mbs l)
      G (jj l) (lsi l) K (blk I)) : ℝ →ₘ[volume] ColumnHilbert (bf.Lab ⊕ Fin fp.Mc)) : ℝ
      → ColumnHilbert (bf.Lab ⊕ Fin fp.Mc)) y).ofLp none‖ ^ (2 : ℕ) ≤ ((8 : ℝ) * (↑dB :
      ℝ) * δ + (2 : ℝ) * δc ^ (2 : ℕ)) * ((4 : ℝ) * N * A.colBudget ^ (2 : ℕ) * CF) *
      (↑Nuse : ℝ) * dyadicGridLength A.G A.R.1)
    (Msch : ℝ)
    (_ : (0 : ℝ) < Msch)
    (Cg : ℕ)
    (_ : ∀ {κ : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ c₀} {bf : A.BasicFamilies} (fp
      : bf.FamParams) (dB : ℕ) {H δc N k δ : ℝ}, (1 : ℝ) ≤ k → (↑fp.Lc : ℝ) + (6 : ℝ) ≤
      k ^ (cc + (6 : ℕ)) → (↑fp.Hmax : ℝ) + (1 : ℝ) ≤ (k * (↑fp.P : ℝ)) ^ (cc + (6 : ℕ))
      → (↑dB : ℝ) ≤ k ^ (cc + (6 : ℕ)) → (2 : ℝ) ≤ fp.Hed → Real.log fp.Hed ≤ k ^ (cc +
      (6 : ℕ)) → (1 : ℝ) ≤ H → Real.log H ≤ k ^ (cc + (6 : ℕ)) → (0 : ℝ) < δc → δc⁻¹ ≤
      Real.exp (k ^ (cc + (6 : ℕ))) → (0 : ℝ) ≤ N → N ≤ Real.exp (k ^ (cc + (6 : ℕ))) →
      A.colBudget ≤ Real.exp (k ^ (cc + (6 : ℕ))) → (0 : ℝ) < δ → δ⁻¹ ≤ Real.exp (k ^
      (cc + (6 : ℕ))) → Real.log (fp.modeStarG Dm0 dB H δc N k δ) ≤ (↑Cg : ℝ) * (k *
      (↑fp.P : ℝ)) ^ Cg ∧ Real.log ((2 : ℝ) ^ (fp.Kstar Dm0 dB H δc N k δ + (1 : ℕ))) ≤
      (↑Cg : ℝ) * (k * (↑fp.P : ℝ)) ^ Cg)
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
    (eΛ : ℕ)
    (CM1 : ℕ)
    (t3 : ℕ)
    (Cb : ℕ)
    (Cl : ℕ)
    (_ : g = (8192 : ℕ) * (cc + (1 : ℕ)) * ((1024 : ℕ) * (cc + (1 : ℕ)) + cc + (7 : ℕ)) + cc
      ^ (2 : ℕ) + (8 : ℕ) ∧ cT = (10 : ℝ) ^ (22 : ℕ) * ((1 : ℝ) +
      localFormUniformConstant κ) ^ (2 : ℕ) ∧ cL = (159 : ℝ) + (32 : ℝ) * (↑g : ℝ) + (8
      : ℝ) * Real.log cT ∧ cK = ((1 : ℝ) + (7 : ℝ) * (10 : ℝ) ^ (9 : ℕ) + cT) * (cL + (2
      : ℝ)) ∧ cMc = (C4c κ + (4 : ℝ) * C3c κ) * cL ^ (4 : ℕ) * cK ^ (2 : ℕ) ∧ cm =
      (196608 : ℝ) * cT + (83 : ℝ) * ((1 : ℝ) + (81 : ℝ) * localFormUniformConstant κ *
      ((30000 : ℝ) + √cT)) * ((1 : ℝ) + cT) ^ (3 : ℕ) + cMc ∧ ce = (6642 : ℝ) *
      localFormUniformConstant κ * ((60000 : ℝ) + √cT) ^ (3 : ℕ) * (288 : ℝ) + (9 : ℝ) *
      ((16 : ℝ) * fourErrC κ (3 : ℕ) + (648 : ℝ) * threeErrC κ (3 : ℕ) (1 : ℕ) + (324 :
      ℝ) * threeErrC κ (3 : ℕ) (1 : ℕ) * √cT) ∧ ce2 = K1c * ((2 : ℝ) * fourKC κ (3 : ℕ)
      * (12 : ℝ) ^ (4 : ℕ)) + (4 : ℝ) * (K1c * ((8 : ℝ) * entryCU κ (3 : ℕ) (1 : ℕ) * (2
      : ℝ) ^ ((1 : ℕ) + (4 : ℕ)) * (12 : ℝ) ^ (3 : ℕ))) * (501 : ℝ) ∧ cQ = (65536 : ℝ) *
      ((8 : ℝ) + (80 : ℝ) * (9 : ℝ) ^ cc * (↑cc : ℝ)) * ((80 : ℝ) * (9 : ℝ) ^ cc * (↑cc
      : ℝ)) * ((4 : ℝ) * (↑cc : ℝ) ^ (2 : ℕ)) * ((17 : ℝ) * (10 : ℝ) ^ (7 : ℕ)) ∧ CΛ =
      (2 : ℕ) * Cg + (12 : ℕ) ∧ eΛ = Cg + (3 : ℕ) * cc ∧ CM1 = (⌈Msch⌉₊ + (1 : ℕ)) * CΛ
      ^ (16 : ℕ) ∧ t3 = (3 : ℕ) ^ cc ∧ Cb = CM1 + (501 : ℕ) * Cg + t3 + (2 : ℕ) * cc +
      (20 : ℕ) + (16 : ℕ) * eΛ ∧ Cl = ⌈cm * (↑Cb : ℝ) ^ (59 : ℕ) + ce * (↑Cb : ℝ) ^ (18
      : ℕ) + ce2 + (3 : ℝ) * (10 : ℝ) ^ (11 : ℕ) * cQ⌉₊ + (59 : ℕ) * Cb + (4 : ℕ) * g +
      (8 : ℕ) * cc + (8 : ℕ))
    (A : ActiveSetup κ c₀)
    (bf : A.BasicFamilies)
    (k : ℕ)
    (η₀ : ℝ)
    (E : ℝ)
    (_ : A.AncClosed)
    (_ : ∀ I ∈ A.cells, ∀ (s s' : Fin (4 : ℕ)), s ≠ s' → PairSmall (dyadicGridLeft A.G I.1
      I.2) (dyadicGridLength A.G I.1) (A.w I) s s' (A.Y I s) (A.Y I s') ((2 : ℝ) * η₀))
    (_ : A.SubRootProps η₀ E)
    (_ : A.S = (2 : ℝ))
    (_ : A.η = (4 : ℝ) * η₀)
    (_ : (0 : ℝ) < η₀)
    (_ : A.cells.Nonempty)
    (q : ℝ)
    (hq2 : (2 : ℝ) < q)
    (hq3 : q < (3 : ℝ))
    (Nd : ℕ)
    (_ : A.DepthWin Nd)
    (p : Fin (3 : ℕ))
    (AD : bf.AttemptData p)
    (_ : bf.Vtx)
    (s : ℕ)
    (δ : ℝ)
    (ρ : ℝ)
    (kD : ℝ)
    (_ : (0 : ℝ) < δ)
    (_ : δ ≤ (1 / 8 : ℝ))
    (_ : (0 : ℝ) < ρ)
    (_ : ρ < (1 : ℝ))
    (_ : Real.log ((2 : ℝ) * A.colBudget) ≤ (↑k : ℝ) ^ cc)
    (_ : (↑((2 : ℕ) * A.famFuel + (2 : ℕ)) : ℝ) ≤ (↑cc : ℝ) * (Real.log (↑k : ℝ) + (1 : ℝ)))
    (_ : (1 : ℝ) ≤ (↑k : ℝ)),
  let fp : bf.FamParams :=
    AD.fp
  let dB : ℕ :=
    A.dBnd
  ∀ (_ : (↑fp.Lc : ℝ) + (6 : ℝ) ≤ (↑k : ℝ) ^ cc ∧ (↑fp.Hmax : ℝ) + (1 : ℝ) ≤ ((↑k : ℝ) *
      (↑fp.P : ℝ)) ^ cc ∧ (↑dB : ℝ) ≤ (↑k : ℝ) ^ cc ∧ Real.log fp.Hed ≤ (↑k : ℝ) ^ cc ∧
      Real.log A.Hsrc ≤ (↑k : ℝ) ^ cc ∧ Real.log (max A.H padW) ≤ (↑k : ℝ) ^ cc ∧ δ⁻¹ ≤
      Real.exp kD ∧ E ≤ (↑k : ℝ) ^ cc ∧ ρ⁻¹ ≤ (↑k : ℝ) ^ cc ∧ (2 : ℝ) + Real.log
      bumpConst + (100 : ℝ) ≤ (↑k : ℝ) ∧ (↑k : ℝ) ^ cc ≤ kD ∧ (2 : ℝ) ≤ (↑k : ℝ) ∧ (0 :
      ℝ) ≤ Real.log bumpConst)
    (_ : (8 : ℝ) * (↑dB : ℝ) * δ ≤ (1 : ℝ)),
  let Nl : ℝ :=
    AD.n (fp.Lc + (5 : ℕ))
  ∀ (_ : Real.log ((2 : ℝ) * ((8 : ℝ) * A.colBudget + ((1 : ℝ) + (↑AD.Mp : ℝ)) * Nl)) ≤ (↑k :
      ℝ) ^ cc)
    (_ : δ ^ (2 : ℕ) * Nl * A.colBudget ^ (2 : ℕ) ≤ (1 : ℝ))
    (_ : (2 : ℝ) ≤ A.colBudget)
    (_ : Monotone AD.n)
    (_ : (0 : ℝ) ≤ Nl),
  let Hm : ℝ :=
    max (max A.Hsrc (Real.exp (↑dB : ℝ))) (max ((5832 : ℝ) * max A.H padW ^ (4 : ℕ))
      ((↑dB : ℝ) * (bumpConst * (8 : ℝ) ^ (32 : ℕ) * ((2 : ℝ) / δ))))
  ∀ (_ : (1 : ℝ) ≤ Hm)
    (_ : ∀ (w : bf.Vtx), (bf.vtag w).dim ≤ dB)
    (_ : ∀ (w : bf.Vtx) (a c : Fin (bf.vtag w).dim), (↑(rationalHeight ((bf.vtag w).C a c)) :
      ℝ) ≤ fp.Hed)
    (S : ModeSchedule)
    (_ : S.dmax = (2 : ℕ) * dB + (2 : ℕ))
    (_ : S.Dstar = fp.modeStarG Dm0 dB Hm δ Nl kD δ)
    (_ : S.Dm = max (2 : ℝ) Nl)
    (_ : S.Q0 = fp.Q0bd dB)
    (_ : S.Valid (340 : ℕ) (5 : ℕ) (4 : ℕ) (600 : ℕ) (1 / 1024 : ℝ) (packetW S.dmax S.H))
    (_ : (8 : ℝ) * ((↑S.dmax : ℝ) + (1 : ℝ)) ^ (3 : ℕ) * Real.log ((2 : ℝ) * S.H) / Real.log
      (2 : ℝ) ≤ packetW S.dmax S.H)
    (_ : (2 : ℕ) ≤ S.dmax)
    (_ : (↑S.dmax : ℝ) ≤ S.Dstar)
    (_ : (2 : ℝ) ≤ S.Dstar)
    (_ : (2 : ℝ) ≤ S.Bstar)
    (_ : (1 : ℕ) ≤ S.Q0)
    (_ : ∀ (z : bf.Vtx), (1 : ℕ) ≤ clearInt (bf.vtag z).C ∧ clearInt (bf.vtag z).C ≤ S.Q0)
    (_ : (↑S.Q0 : ℝ) * (2 : ℝ) ^ (fp.Kstar Dm0 dB Hm δ Nl kD δ + (1 : ℕ)) ≤ S.Bstar)
    (_ : Real.log S.H ≤ Msch * ((↑((2 : ℕ) * dB + (2 : ℕ)) : ℝ) + Real.log (fp.modeStarG Dm0
      dB Hm δ Nl kD δ) + Real.log (fp.Bst Dm0 dB Hm δ Nl kD δ) + Real.log (max (2 : ℝ)
      Nl) + Real.log (↑(fp.Q0bd dB) : ℝ) + (1 : ℝ)) ^ (12 : ℕ))
    (_ : (↑S.K : ℝ) ≤ Msch * ((↑((2 : ℕ) * dB + (2 : ℕ)) : ℝ) + Real.log (fp.modeStarG Dm0 dB
      Hm δ Nl kD δ) + Real.log (fp.Bst Dm0 dB Hm δ Nl kD δ) + Real.log (max (2 : ℝ) Nl)
      + Real.log (↑(fp.Q0bd dB) : ℝ) + (1 : ℝ)) ^ (16 : ℕ))
    (_ : (1 : ℕ) ≤ S.K),
  let Lf : SearchLeaf :=
    leafAt A.famFuel fp.Lc (A.basicSlot p) s
  ∀ (_ : Lf = leafAt A.famFuel fp.Lc (A.basicSlot p) s),
  let ks : ℕ :=
    Lf.k
  let S0 : Finset (ℤ × ℤ) :=
    {I ∈ AD.Tc | ¬∃ c ∈ fp.failRoots, dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G
      c.1 c.2}
  ∀ (_ : S0 ⊆ AD.Tc)
    (_ : S0 ⊆ A.cells),
  let gs : ℤ × ℤ → Finset bf.Grp :=
    fun (I : ℤ × ℤ) => fp.groupsAt I ks
  let gset : Finset bf.Grp :=
    S0.biUnion gs
  ∀ (_ : ∀ I ∈ S0, ∀ G ∈ gs I, fp.Cert ks G I ∧ fp.ActualUse G I)
    (_ : ∀ G ∈ gset, ∃ (I : ℤ × ℤ), fp.ActualUse G I),
  let U : Fin (4 : ℕ) → bf.Grp → Finset (ℤ × ℤ) :=
    fun (_ : Fin (4 : ℕ)) (G : bf.Grp) => {I ∈ S0 | G ∈ gs I}
  ∀ (_ : ∀ (l : Fin (4 : ℕ)) (G : bf.Grp), ∀ I ∈ U l G, fp.ActualUse G I)
    (_ : ∀ (y : ℝ), ∑ l : Fin (4 : ℕ), ∑ G ∈ gset, (Finset.card ({I ∈ U l G | y ∈
      dyadicGridCell A.G I.1 I.2})) ≤ (4 : ℕ) * (AD.Mp * A.famVtxBound))
    (_ : ∀ (l : Fin (4 : ℕ)), (AD.cat l).length ≤ fp.Mc)
    (_ : ∀ (l : Fin (4 : ℕ)), ∀ I ∈ A.cells, (↑(mainLabels A.G fp.Mc (bf.origCols l) (AD.cat
      l) I (fp.brank (Lf.role l))).card : ℝ) ≤ Nl),
  ∃ (F : Fin (6 : ℕ) → Finset (ℤ × ℤ)), (∀ (i : Fin (6 : ℕ)), ∀ c ∈ F i,
    dyadicGridCell A.G c.1 c.2 ⊆ dyadicGridCell A.G A.R.1 A.R.2) ∧ (∀ (i : Fin (6 :
    ℕ)), dyadicRootLength A.G (F i) ≤ (2 : ℝ) * ρ * dyadicGridLength A.G A.R.1) ∧ ∀ cs
    ⊆ AD.Tc, (∀ I ∈ cs, ¬∃ c ∈ fp.failRoots, dyadicGridCell A.G I.1 I.2 ⊆
    dyadicGridCell A.G c.1 c.2) → (∀ I ∈ cs, ∀ (i : Fin (6 : ℕ)), ∀ e ∈ F i,
    ¬dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G e.1 e.2) → ∑ I ∈ cs,
    dyadicGridLength A.G I.1 * min A.η ‖∑ G ∈ fp.groupsAt I ks, (fp.Λc I : (Fin (4 :
    ℕ) → ↥(ColumnL2 (bf.Lab ⊕ Fin fp.Mc))) → ℂ) fun (l : Fin (4 : ℕ)) => (fp.ballFilt
    l (AD.cat l) I G (Lf.role l) : ↥(ColumnL2 (bf.Lab ⊕ Fin fp.Mc)) → ↥(ColumnL2
    (bf.Lab ⊕ Fin fp.Mc))) (fp.inputL AD.cat I (bf.patIn fp.Mc p I) Lf.layers l)‖ ≤
    leafBnd Cl kD fp.P k cc A.η η₀ AD.τ₃ δ (finiteDepthConstant κ q Nd) (nbCM κ hq2
    hq3 + nbCUM κ hq2 hq3) q (dyadicGridLength A.G A.R.1)




private theorem leaf_estimate_hstab : LeafEstimateHstabStatement := by
  classical
  intro κ c₀ cc Dm0 Msch Cg g cm ce ce2 cQ CΛ eΛ CM1 t3 Cb Cl A bf p AD d s δ kD fp dB Nl hNl0 Hm
    S hSd hSV hd2 hD2 hB2 hQ1 hK1 Lf ks S0 gs gset hlenMc mbs Ms hnotg hsch' hA6 qG hqG1 hD0 BN
    hPH hNq hBσG c cf D₀ hcat hhT hmbb hmbT mb' D
  let B₀ : (D₀.toLeafQ qG).BallData gset :=
    { hT := fun l e he => (AD.hT l e he).2.2
      htag := AD.htag
      dv := fun _ => d
      hPH := hPH
      N := BN
      hN := hNq }
  intro htagH
  let B : ((D₀.appendCat hcat mb').toLeafQ qG).BallData gset :=
    D₀.ballDataAppend hcat mb' qG B₀ (fun l e he => (hhT l e he).2.2.2) htagH
        (fun l e he => by
          rw [(hhT l e he).2.1]
          change fp.Lc + Lf.role l < fp.Lc + 5
          have! this := Lf.role_le l
          omega)
  intro hBσ1 G hG
  have! hqS : ((qG G : ℕ) : ℝ) ≤ S.Q0 := by exact_mod_cast (hqG1 G).2
  have! hmono : ∀ (B : ℝ), 1 ≤ B → ∀ (Q : ℝ), 0 ≤ Q → Q ≤ S.Q0 →
      2 * (Q * (3 * (B * B) ^ 2)) ^ 2 ≤ 2 * ((S.Q0 : ℝ) * (3 * (B * B) ^ 2)) ^ 2 := by
    intro B hB Q hQ0 hQ
    have! h3 : 0 ≤ 3 * (B * B) ^ 2 := by positivity
    have! h4 : Q * (3 * (B * B) ^ 2) ≤ (S.Q0 : ℝ) * (3 * (B * B) ^ 2) :=
      mul_le_mul_of_nonneg_right hQ h3
    have! h5 := pow_le_pow_left₀ (mul_nonneg hQ0 h3) h4 2
    linarith only [h5]
  have! hB1 : ∀ (B : ℝ), 1 ≤ B → 2 * ((S.Q0 : ℝ) * (3 * (1 * 1) ^ 2)) ^ 2 ≤
      2 * ((S.Q0 : ℝ) * (3 * (B * B) ^ 2)) ^ 2 := by
    intro B hB
    have! hBB : (1 : ℝ) * 1 ≤ B * B := mul_le_mul hB hB zero_le_one (by linarith only [hB])
    have! h1 : (1 * 1 : ℝ) ^ 2 ≤ (B * B) ^ 2 := pow_le_pow_left₀ (by norm_num) hBB 2
    have! hQ0 : (0 : ℝ) ≤ S.Q0 := Nat.cast_nonneg _
    have! h4 : (S.Q0 : ℝ) * (3 * (1 * 1) ^ 2) ≤ (S.Q0 : ℝ) * (3 * (B * B) ^ 2) :=
      mul_le_mul_of_nonneg_left (by linarith only [h1]) hQ0
    have! h5 := pow_le_pow_left₀ (by positivity) h4 2
    linarith only [h5]
  have! hbase : 2 * ((qG G : ℝ) * (3 * (1 * 1) ^ 2)) ^ 2 ≤ (⌊S.Dstar⌋₊ : ℝ) :=
    (hmono 1 le_rfl _ (Nat.cast_nonneg _) hqS).trans ((hB1 _ (hBσ1 0 G)).trans
      (hBσG 0 ⟨G, hG⟩))
  refine (D.withQ0 (qG G)).stab_of_valid (hSV.withQ0 hD0.le (le_trans zero_le_two hB2)
    (hqG1 G).2) (by norm_num) le_rfl hd2 hD2 hB2 (hqG1 G).1 rfl (fun l G' q' => ?_)
    (fun l G' => ?_) (fun l G' I => ?_)
  · change (D.Ms l G').dvOf q' + (D.Ms l G').zc.dim ≤ S.dmax
    rw [hSd]
    by_cases hG' : G' ∈ gset
    · exact (hsch' l G' hG').1 q'
    · exact (hnotg l G' hG').1 q'
  · change 2 * ((qG G : ℝ) * (3 * ((D.Ms l G').Bσ * (D.Ms l G').Bσ) ^ 2)) ^ 2 ≤
      (⌊S.Dstar⌋₊ : ℝ)
    by_cases hG' : G' ∈ gset
    · exact (hmono _ (hBσ1 l G') _ (Nat.cast_nonneg _) hqS).trans (hBσG l ⟨G', hG'⟩)
    · have! e : (D.Ms l G').Bσ = 1 := (hnotg l G' hG').2.1
      rw [e]
      exact hbase
  · change (((D.Ms l G').alive _).card : ℝ) ≤ S.Dstar
    by_cases hG' : G' ∈ gset
    · exact (hsch' l G' hG').2.2.2.2.2.1 _
    · have! e : ∀ V, (D.Ms l G').alive V = ∅ := (hnotg l G' hG').2.2
      rw [e, Finset.card_empty, Nat.cast_zero]
      exact hD0.le
-- the first tops in the form of the leaf bound



private theorem leaf_estimate_conclusion_88 : LeafEstimateConclusion88Statement := by
  classical
  intro κ c₀ cc Cl A bf k η₀ E hsub q hq2 hq3 Nd p AD d s δ ρ kD hρ1 fp Nl hNl0 S hK1 Lf ks S0 gs
    gset hlenMc mbs Ms hA6 qG c Cut hCutl cf D₀ hcat hmbb hmbT mb' D hrankH hroleD S1 hRl0 C C₂ S₂
    hη0 hBd cs hcs hno hnoF
  have! hsub : cs ⊆ ((S1.filter (fun I => ¬ ∃ e ∈ C,
      dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G e.1 e.2)).filter
      (fun I => ¬ ∃ e ∈ C₂, dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G e.1 e.2)) := by
    intro I hI
    have! hIc := AD.hTc (hcs hI)
    refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨hcs hI, hno I hI⟩, fun j e he hIe => ?_⟩, ?_⟩, ?_⟩
    · have! hlenR : dyadicGridCell A.G e.1 e.2 ⊆ dyadicGridCell A.G A.R.1 A.R.2 ∨
          dyadicGridCell A.G A.R.1 A.R.2 ⊆ dyadicGridCell A.G e.1 e.2 := by
        rcases le_total e.1 A.R.1 with h | h
        · rcases dyadicGridCell_nested_or_disjoint_of_le A.G h e.2 A.R.2 with hd | hs
          · exact absurd ((A.sub I hIc) (dyadicGridCell_left_mem A.G I.1 I.2))
              (Set.disjoint_left.mp hd (hIe (dyadicGridCell_left_mem A.G I.1 I.2)))
          · exact Or.inr hs
        · rcases dyadicGridCell_nested_or_disjoint_of_le A.G h A.R.2 e.2 with hd | hs
          · exact absurd (hIe (dyadicGridCell_left_mem A.G I.1 I.2))
              (Set.disjoint_left.mp hd ((A.sub I hIc) (dyadicGridCell_left_mem A.G I.1 I.2)))
          · exact Or.inl hs
      rcases hlenR with hR | hR
      · fin_cases j
        · exact hnoF I hI 2 e (Finset.mem_filter.mpr ⟨he, hR⟩) hIe
        · exact hnoF I hI 3 e (Finset.mem_filter.mpr ⟨he, hR⟩) hIe
        · exact hnoF I hI 4 e (Finset.mem_filter.mpr ⟨he, hR⟩) hIe
        · exact hnoF I hI 5 e (Finset.mem_filter.mpr ⟨he, hR⟩) hIe
      · have! h1 : dyadicGridLength A.G A.R.1 ≤ dyadicGridLength A.G e.1 := by
          have! this := dyadicGridCell_depth_le_of_subset A.G A.R e hR
          exact (dyadicGridLength_strictAnti A.G).antitone this
        have! h2 : dyadicGridLength A.G e.1 ≤ ρ * dyadicGridLength A.G A.R.1 :=
          (Finset.single_le_sum (f := fun c : ℤ × ℤ => dyadicGridLength A.G c.1)
            (fun c _ => (dyadicGridLength_pos A.G c.1).le) he).trans (hCutl j)
        have := hRl0
        nlinarith only [h1, h2, this, hρ1]
    · rintro ⟨e, he, hIe⟩
      obtain ⟨m, hm, hem⟩ := maximalDyadicCells_covers A.G C he
      exact hnoF I hI 0 m hm (hIe.trans hem)
    · rintro ⟨e, he, hIe⟩
      exact hnoF I hI 1 e he hIe
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub fun I _ _ =>
    mul_nonneg (dyadicGridLength_pos A.G I.1).le (le_min hη0 (norm_nonneg _)))
    (le_of_eq_of_le (Finset.sum_congr rfl fun I _ => ?_) hBd)
  refine congrArg (fun x => dyadicGridLength A.G I.1 * min A.η ‖x‖) ?_
  refine Finset.sum_congr rfl fun G _ => ?_
  refine congrArg (fp.Λc I) ?_
  funext l
  rw [D₀.toLeafQ_out_appendCat hcat mb' hrankH hroleD qG l G I]
  rfl



private theorem leaf_estimate_stage_8 : LeafEstimateStage8Statement := by
  classical
  intro κ c₀ cc hcc Dm0 Msch hMsch Cg g cT cL cK cMc cm ce ce2 cQ CΛ eΛ CM1 t3 Cb Cl hconst A bf k
    η₀ E hsub hS2 hη hη₀ q hq2 hq3 Nd p AD d s δ ρ kD hδ hδ8 hρ hρ1 hkb hkF fp dB Nl hkB hcb hNl0
    Hm S hSd hSDm hSV hd2 hD2 hB2 hQ1 hK1 Lf ks S0 gs gset hlenMc mbs Ms L hA6 qG Vl0 U MV hMV ε
    hεdef Ts hNl4 c Cut hCutl cf D₀ hcat hmbb hmbT mb' D hrankH hroleD S1 hS1c Nb hNb hRl0 hVl00
    Os hOs Cjg hCjg Γa hΓadef Γb hΓbdef ΓU hΓUdef Ee hEe0 hEeb hdB1 Gq hVl0 Mt hMt Iw C C₂ hC hlen
    hC₂ hlen₂ hdBk hEk hρk hkD hk2 u hu hVle hlD Λ hK hlogH hΛ0 hΛ hE0 hVl0nn TT hUdef hT0 T2v S₂
    hsum hexpD ι Qe hcEsum
  set! G0e := Real.exp ((4096 * (cc + 1) * (1024 * (cc + 1) + cc + 7) + cc ^ 2 + 3) *
    (1 + Real.log (2 * (k : ℝ))) ^ 2) with hG0e
  have! hG0e1 : 1 ≤ G0e := Real.one_le_exp (by positivity)
  set! W := G0e + Vl0 + E + 1 with hWdef
  have! hW1 : 1 ≤ W := by linarith only [hG0e1, hVl00, hE0]
  set! n : ℝ := (Nb : ℝ) with hn
  rewrite [← hn] at hΓadef hΓbdef
  have! hn1 : 1 ≤ n := by
    rw [hn, hNb]; push_cast
    have! this := Nat.cast_nonneg (α := ℝ) (Nat.log 2 S.K)
    linarith only [this]
  have! hCjg1 : 1 ≤ Cjg :=
    leaf_estimate_hCjg1 κ c₀ cc A k hCjg
  set! P3 := n ^ 3 * Cjg with hP3
  have! hP31 : 1 ≤ P3 := one_le_mul_of_one_le_of_one_le (one_le_pow₀ hn1) hCjg1
  have! hnP3 : n ≤ P3 := by
    have! this : n ≤ n ^ 3 := le_self_pow₀ hn1 (by norm_num)
    exact this.trans (le_mul_of_one_le_right (by positivity) hCjg1)
  have! hnCP3 : n * Cjg ≤ P3 := by
    have! this : n ≤ n ^ 3 := le_self_pow₀ hn1 (by norm_num)
    exact mul_le_mul_of_nonneg_right this (by linarith only [hCjg1])
  have! hOs0 : (0 : ℝ) ≤ Os.card := Nat.cast_nonneg _
  have hcapV : FamParams.capV A cc k = G0e * (4 * dyadicGridLength A.G A.R.1) := rfl
  have hsideB : FamParams.SideInput.sideB0 A cc k Vl0 =
      2 * ((20 * G0e + 32) * dyadicGridLength A.G A.R.1) + 2 * (Vl0 * dyadicGridLength A.G A.R.1) :=
    rfl
  have hR0 : dyadicGridLength A.G A.R.1 ≠ 0 := hRl0.ne'
  have! hG0W : G0e ≤ W := by linarith only [hVl00, hE0]
  have! hVW : Vl0 ≤ W := by linarith only [hG0e1, hE0]
  have! hEW : E ≤ W := by linarith only [hG0e1, hVl00]
  have! hsB : 40 * G0e + 64 + 2 * Vl0 ≤ 106 * W := by linarith only [hG0W, hVW, hW1]
  have! hΓa0 : Γa 0 ≤ 1874 * Os.card * P3 * W :=
    leaf_estimate_hΓa0 κ c₀ cc A k E S Vl0 hVl00 hG0e1 hW1 hΓadef hP3 hP31 hnP3 hnCP3 hOs0 hcapV
      hsideB hR0 hG0W hsB
  have! hΓb0 : Γb 0 ≤ 110 * Os.card * P3 * W :=
    leaf_estimate_hΓb0 κ c₀ cc A k E S Vl0 hG0e1 hW1 hΓbdef hP31 hnP3 hOs0 hcapV hsideB hR0 hG0W hsB
  have! hΓU0 : ΓU ≤ 8 * Os.card * P3 * W := by
    have! e : ΓU = Os.card * (8 * E) := by
      rw [hΓUdef, div_eq_iff hR0]; ring
    rw [e]
    have! this : E ≤ P3 * W := le_trans hEW (le_mul_of_one_le_left (by linarith only [hW1]) hP31)
    calc (Os.card : ℝ) * (8 * E) ≤ Os.card * (8 * (P3 * W)) :=
          mul_le_mul_of_nonneg_left (by linarith only [this]) hOs0
      _ = _ := by ring
  have! hΓa00 : 0 ≤ Γa 0 :=
    leaf_estimate_hΓa00 κ c₀ cc A k S Vl0 hRl0 hVl00 hΓadef hOs0 hcapV hsideB
  have! hΓb00 : 0 ≤ Γb 0 :=
    leaf_estimate_hΓb00 κ c₀ cc A k S Vl0 hRl0 hVl00 hΓbdef hOs0 hcapV hsideB
  have! hΓU00 : 0 ≤ ΓU :=
    leaf_estimate_hΓU00 κ c₀ A E hRl0 hΓUdef hE0 hOs0
  set! Γ := Γa 0 + Γb 0 + ΓU with hΓdef
  have! hΓle : Γ ≤ 2000 * Os.card * P3 * W := by
    have! this : (0 : ℝ) ≤ Os.card * P3 * W :=
      mul_nonneg (mul_nonneg hOs0 (by linarith only [hP31])) (by linarith only [hW1])
    linarith only [hΓa0, hΓb0, hΓU0, this]
  set! ZT := 4 * ((nbCM κ hq2 hq3 + nbCUM κ hq2 hq3) * (1 + finiteDepthConstant κ q Nd) *
          (1 + Real.log ((S.K : ℝ) + 2)) * ((S.K : ℝ) + 2) ^ (2 * (q - 2) / (q - 1)) *
          (64 * (2 * (2 * Real.sqrt 1)) * (2 * (2 * Real.sqrt 1)))) *
        (hullCutConstant (ρ / 64 / 2) * (Nb + 1 : ℕ) * (1 + Real.log (2 + ((Nb + 1 : ℕ) : ℝ) *
          ((Nb + 1 : ℕ) : ℝ) * ((FamParams.SideLeafM.nOs (2 ^ A.famFuel)
            (2 * A.famFuel + 2)).card * (AD.Mp : ℝ) * A.famVtxBound)))) *
        Γ / Real.sqrt fp.P * dyadicGridLength A.G A.R.1 with hZT
  have! hnear1 : ∀ a b e, (D.toLeafQ qG).nearBnd hq2 hq3 Nd Nb (2 ^ A.famFuel) (2 * A.famFuel + 2)
      (AD.Mp : ℝ) (2 * Real.sqrt 1) (ρ / 64) Γa Γb ΓU a b e ≤ ZT := by
    intro a b e
    rw [D.nearBnd_eq_F, hZT]
    exact nearBndF_le κ A hq2 hq3 fp.P D.S.K D.u Nd Nb (2 ^ A.famFuel) (2 * A.famFuel + 2)
      Γa Γb ΓU a b e (Nat.cast_nonneg _) (by positivity) (by positivity) (by linarith only [hρ1])
      (fun _ => ⟨hΓa00, by linarith only [hΓb00, hΓU00]⟩)
      (fun _ => ⟨hΓb00, by linarith only [hΓa00, hΓU00]⟩)
      ⟨hΓU00, by linarith only [hΓa00, hΓb00]⟩
  have! hnearS : ∑ a : Fin 4, ∑ b : Fin 4, ∑ e : Fin 4, (D.toLeafQ qG).nearBnd hq2 hq3 Nd Nb
      (2 ^ A.famFuel) (2 * A.famFuel + 2) (AD.Mp : ℝ) (2 * Real.sqrt 1) (ρ / 64) Γa Γb ΓU a b e ≤
      64 * ZT := by
    refine (Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => Finset.sum_le_sum
      fun e _ => hnear1 a b e).trans (le_of_eq ?_)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat]
    ring
  -- the explicit leaf bound, by `leaf_final`
  have! hEe00 : 0 ≤ Ee := le_trans (Finset.sum_nonneg fun I _ => Finset.sum_nonneg fun G _ =>
    Finset.sum_nonneg fun l _ => sq_nonneg _) hEe0
  have! hη0 : 0 ≤ A.η := by rw [hη]; positivity
  have! hJH : (S.Jstar : ℝ) ≤ Real.log S.H := hSV.Jstar_le_log_H (by norm_num) hd2 hD2 hB2 hQ1
  have! hH2 : 2 ≤ S.H := hSV.two_le_H hd2 hD2 hB2 hQ1
  have! hΛ' : Λ ≤ CΛ * (kD * fp.P) ^ eΛ := by rw [← hu]; exact hΛ
  have! hlD' : Real.log S.Dstar ≤ Cg * (kD * fp.P) ^ Cg := by rw [← hu]; exact hlD
  have! hBd := hsum.trans (leaf_final κ hq2 hq3 Nd hMsch hconst hcc hk2 hkD fp.hP hcb hNl4 hkB hkb
    hVle hkF hdB1 hdBk hE0 hEk hρ hρ1 hρk hδ hδ8 hη0 hη₀ AD.hτ₃ hRl0 S hD2 hH2 hK1 hSd hSDm
    hJH hΛ0 hΛ' hK hlogH hlD' hexpD rfl hVl0 hT0
    (TsideF_le A fp.P S.K (A.uslot p) (2 ^ A.famFuel) (2 * A.famFuel + 2) cc k (fun _ => Vl0)
      hS2 fp.hP Nat.one_le_two_pow hE0 hVl0nn hρ) hUdef hMV hεdef hMt
    (T2F_le _ _ cc k (fun _ => Vl0) hVl0nn hρ) (B0 := max (2 * Real.sqrt 1) A.S)
    (by rw [hS2, Real.sqrt_one]; norm_num) rfl rfl
    (D.coreM4_eq_F (δs := 1 / 1024) rfl 3 U ε _)
    (Finset.sum_congr rfl fun l _ => D.coreM3_eq_F (δs := 1 / 1024) rfl 3 1 Iw U ε _ l)
    hOs hΓle hnearS hcEsum hEe00 hEeb rfl)
  refine ⟨![maximalDyadicCells A.G C, C₂, (Cut 0).filter fun e => dyadicGridCell A.G e.1 e.2 ⊆
      dyadicGridCell A.G A.R.1 A.R.2, (Cut 1).filter fun e => dyadicGridCell A.G e.1 e.2 ⊆
      dyadicGridCell A.G A.R.1 A.R.2, (Cut 2).filter fun e => dyadicGridCell A.G e.1 e.2 ⊆
      dyadicGridCell A.G A.R.1 A.R.2, (Cut 3).filter fun e => dyadicGridCell A.G e.1 e.2 ⊆
      dyadicGridCell A.G A.R.1 A.R.2], ?_, ?_, ?_⟩
  · intro i c hc
    fin_cases i
    · exact A.sub c (hC (maximalDyadicCells_subset A.G C hc))
    · exact A.sub c (hS1c (hC₂ hc))
    all_goals exact (Finset.mem_filter.mp hc).2
  · have! hcut : ∀ j, dyadicRootLength A.G ((Cut j).filter fun e => dyadicGridCell A.G e.1 e.2 ⊆
        dyadicGridCell A.G A.R.1 A.R.2) ≤ 2 * ρ * dyadicGridLength A.G A.R.1 := by
      intro j
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        fun c _ _ => (dyadicGridLength_pos A.G c.1).le) ((hCutl j).trans ?_)
      have := hRl0
      nlinarith only [this, hρ]
    intro i
    fin_cases i
    · exact hlen
    · exact hlen₂.trans (by have := hRl0; nlinarith only [this, hρ])
    all_goals exact hcut _
  · expose_names
    exact @leaf_estimate_conclusion_88 κ c₀ cc Cl A bf k η₀ E hsub q hq2 hq3 Nd p AD d s δ ρ kD
      hρ1 hNl0 S hK1 hlenMc Ms hA6 c Cut hCutl hcat hmbb hmbT hrankH hroleD hRl0 C C₂ hη0 hBd



private theorem leaf_estimate_stage_7 : LeafEstimateStage7Statement := by
  classical
  intro κ c₀ cc hcc Dm0 Msch hMsch Cg g cT cL cK cMc cm ce ce2 cQ CΛ eΛ CM1 t3 Cb Cl hconst A bf k
    η₀ E hsub hS2 hη hη₀ hne q hq2 hq3 Nd p AD d s δ ρ kD hδ hδ8 hρ hρ1 hkb hkF hk1 fp dB Nl hkB
    hcb hNl0 Hm hHm1 S hSd hSDm hSV hd2 hD2 hB2 hQ1 hlogH hK hK1 Lf ks S0 gs gset hlenMc mbs Ms L
    hDS hsch' hA6 qG Vl0 U hUdef hD0 hD1 hU16 MV hMV ε hεdef hε0 Ts hNl4 hstar c hcB Cut hCutl cf
    D₀ hcat hmbb hmbT mb' D hrankH hroleD S1 hS1S0 hS1c hIB Nb hNb hRl0 hVl00 Os hOs Cjg hCjg Γa
    hΓadef Γb hΓbdef ΓU hΓUdef Ee hEe0 hEeb hMD' hdB1 hcD Gq hVl0 Mt hMt Iw C C₂ hC hlen hC₂ hlen₂
    hUs hsum hdBk hHedk hEk hρk hkD hk2 hCΛ heΛ hP1 u hu hu1 hku hNlexp hVle hmsG
  rw [← hu] at hmsG
  have! hlD : Real.log S.Dstar ≤ Cg * u ^ Cg := by rw [hDS]; exact hmsG.1
  have! hlD0 : 0 ≤ Real.log S.Dstar := Real.log_nonneg hD1
  have! hupow : ∀ e : ℕ, e ≤ eΛ → u ^ e ≤ u ^ eΛ := fun e he => pow_le_pow_right₀ hu1 he
  have! hkue : ∀ e : ℕ, (k : ℝ) ^ e ≤ u ^ e := fun e =>
    pow_le_pow_left₀ (by linarith only [hk1]) hku e
  have! hQ0l : Real.log (fp.Q0bd dB) ≤ (k : ℝ) ^ (3 * cc) + 1 :=
    leaf_estimate_hQ0l κ c₀ cc A bf k p AD hk1 hdB1 hdBk hHedk
  have! hQ0l0 : 0 ≤ Real.log (fp.Q0bd dB) :=
    Real.log_nonneg (by exact_mod_cast fp.one_le_Q0bd dB AD.hHed2)
  have! hmaxNl : Real.log (max 2 Nl) ≤ (k : ℝ) ^ cc := by
    rw [max_eq_right (by linarith only [hNl4])]
    calc Real.log Nl ≤ Real.log (Real.exp ((k : ℝ) ^ cc)) :=
          Real.log_le_log (by linarith only [hNl4]) hNlexp
      _ = _ := Real.log_exp _
  have! hmaxNl0 : 0 ≤ Real.log (max 2 Nl) :=
    Real.log_nonneg (le_trans (by norm_num) (le_max_left _ _))
  have! hBstl : Real.log (fp.Bst Dm0 dB Hm δ Nl kD δ) = Real.log (fp.Q0bd dB) +
      Real.log ((2 : ℝ) ^ (fp.Kstar Dm0 dB Hm δ Nl kD δ + 1)) := by
    unfold FamParams.Bst
    have! hq1 : (0 : ℝ) < fp.Q0bd dB := by
      exact_mod_cast lt_of_lt_of_le zero_lt_one (fp.one_le_Q0bd dB AD.hHed2)
    rw [Real.log_mul hq1.ne' (by positivity)]
  have! hlK0 : 0 ≤ Real.log ((2 : ℝ) ^ (fp.Kstar Dm0 dB Hm δ Nl kD δ + 1)) :=
    Real.log_nonneg (one_le_pow₀ (by norm_num))
  have hlDG : Real.log (fp.modeStarG Dm0 dB Hm δ Nl kD δ) ≤ Cg * u ^ Cg := hmsG.1
  have! hlDG0 : 0 ≤ Real.log (fp.modeStarG Dm0 dB Hm δ Nl kD δ) := by rw [← hDS]; exact hlD0
  set! Λ := ((2 * dB + 2 : ℕ) : ℝ) + Real.log (fp.modeStarG Dm0 dB Hm δ Nl kD δ) +
    Real.log (fp.Bst Dm0 dB Hm δ Nl kD δ) + Real.log (max 2 Nl) + Real.log (fp.Q0bd dB) + 1
    with hΛdef
  rewrite [← hΛdef] at hlogH hK
  have! hΛ0 : 0 ≤ Λ :=
    leaf_estimate_hΛ0 κ c₀ Dm0 A bf p AD δ kD hdB1 hmaxNl0 hBstl hlK0 hlDG0 hΛdef
  have! hΛ : Λ ≤ CΛ * u ^ eΛ := by
    rw [hΛdef, hBstl]
    have! h1 : (k : ℝ) ^ (3 * cc) ≤ u ^ eΛ := (hkue _).trans (hupow _ (by rw [heΛ]; omega))
    have! h2 : (k : ℝ) ^ cc ≤ u ^ eΛ := (hkue _).trans (hupow _ (by rw [heΛ]; omega))
    have! h3 : (Cg : ℝ) * u ^ Cg ≤ Cg * u ^ eΛ :=
      mul_le_mul_of_nonneg_left (hupow _ (by rw [heΛ]; omega)) (Nat.cast_nonneg _)
    have! h4 : (1 : ℝ) ≤ u ^ eΛ := one_le_pow₀ hu1
    have h5 := hmsG.2
    have hdBk' : (dB : ℝ) ≤ (k : ℝ) ^ cc := hdBk
    rw [hCΛ]
    push_cast
    linarith only [h1, h2, h3, h4, h5, hdBk', hlDG, hQ0l, hmaxNl]
  have! hE0 : 0 ≤ E :=
    leaf_estimate_hE0 κ c₀ A η₀ E hsub hRl0
  have! hVl0nn : ∀ l : Fin 4, 0 ≤ (fun _ : Fin 4 => Vl0) l ∧ (fun _ : Fin 4 => Vl0) l ≤ Vl0 :=
    fun _ => ⟨hVl00, le_rfl⟩
  set! TT := TsideF A fp.P S.K (A.uslot p) (2 ^ A.famFuel) (2 * A.famFuel + 2) 1 E cc k
    (fun _ => Vl0) ρ with hTT
  rewrite [← hTT] at hUdef
  have! hT0 : 0 ≤ TT :=
    leaf_estimate_hT0 κ c₀ cc A bf k E p AD ρ hρ S hK1 Vl0 hRl0 hVl00 hP1 hE0 hTT
  set! T2v := D.T2 cc k (fun _ => Vl0) ρ with hT2v
  rewrite [← hT2v] at hsum
  -- the core errors on the retained cells
  set! S₂ := (S1.filter (fun I => ¬ ∃ e ∈ C, dyadicGridCell A.G I.1 I.2 ⊆
      dyadicGridCell A.G e.1 e.2)).filter
      (fun I => ¬ ∃ e ∈ C₂, dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G e.1 e.2) with hS₂
  rewrite [← hS₂] at hUs hsum
  have! hS₂S1 : S₂ ⊆ S1 := fun I hI => (Finset.mem_filter.mp (Finset.mem_filter.mp hI).1).1
  have! hexpD : Real.exp kD ≤ S.Dstar :=
    (fp.le_modeStar Dm0 dB kD AD.hHed2 hHm1 hδ hNl0 (g := 0) le_rfl (j := 0)
      (by norm_num)).1.trans hstar
  have! hDinv : S.Dstar⁻¹ ≤ Real.exp (-kD) := by
    rw [Real.exp_neg]; exact inv_anti₀ (Real.exp_pos _) hexpD
  have! hsq : Real.sqrt (4 * S.Dstar ^ 2 * 1) = 2 * S.Dstar := by
    rw [mul_one, show (4 : ℝ) * S.Dstar ^ 2 = (2 * S.Dstar) ^ 2 by ring,
      Real.sqrt_sq (by linarith only [hD0])]
  have! hsD : Real.sqrt S.Dstar ^ 2 = S.Dstar := Real.sq_sqrt hD0.le
  have! hsD1 : 1 ≤ Real.sqrt S.Dstar := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt hD1
  have! h4pow : (S.Dstar * (Real.sqrt S.Dstar * Real.sqrt (4 * S.Dstar ^ 2 * 1))) ^ 4 =
      16 * S.Dstar ^ 10 := by
    rw [hsq]
    calc _ = 16 * S.Dstar ^ 8 * (Real.sqrt S.Dstar ^ 2) ^ 2 := by ring
      _ = _ := by rw [hsD]; ring
  have! h3pow : (S.Dstar * (Real.sqrt S.Dstar * Real.sqrt (4 * S.Dstar ^ 2 * 1) + 1)) ^ 4 ≤
      81 * S.Dstar ^ 10 :=
    leaf_estimate_h3pow S hD0 hD1 hsq hsD hsD1
  set! ι : ℝ := (S.Dstar ^ 100)⁻¹ * S.Dstar ^ 10 with hι
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
  have! hcoreE : ∀ I ∈ S₂, D.coreE qG gs 3 1 Iw U ε I ≤ (gs I).card * Qe :=
    leaf_estimate_hcoreE κ c₀ cc hcc Dm0 A bf hne p AD d s δ kD hNl0 S hD2 hK1 hlenMc Ms hsch' hA6
      U hD1 hU16 ε c hcB Cut hcat hmbb hmbT hS1S0 hS1c hIB hcD C C₂ hUs hS₂S1 h4pow h3pow hι hQe
  have! hQe0 : 0 ≤ Qe :=
    leaf_estimate_hQe0 κ S hD2 U hU16 ε hε0 hQe
  have! hcEsum : ∑ I ∈ S₂, dyadicGridLength A.G I.1 * D.coreE qG gs 3 1 Iw U ε I ≤
      Qe * (((AD.Mp * A.famVtxBound : ℕ) : ℝ) * dyadicGridLength A.G A.R.1) := by
    calc ∑ I ∈ S₂, dyadicGridLength A.G I.1 * D.coreE qG gs 3 1 Iw U ε I
        ≤ ∑ I ∈ S₂, dyadicGridLength A.G I.1 * ((gs I).card * Qe) :=
          Finset.sum_le_sum fun I hI =>
            mul_le_mul_of_nonneg_left (hcoreE I hI) (dyadicGridLength_pos A.G I.1).le
      _ = Qe * ∑ I ∈ S₂, dyadicGridLength A.G I.1 * (gs I).card := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun I _ => by ring
      _ ≤ Qe * ∑ I ∈ S1, dyadicGridLength A.G I.1 * (gs I).card :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg hS₂S1
            fun I _ _ => mul_nonneg (dyadicGridLength_pos A.G I.1).le (Nat.cast_nonneg _)) hQe0
      _ ≤ Qe * (((AD.Mp * A.famVtxBound : ℕ) : ℝ) * dyadicGridLength A.G A.R.1) :=
          mul_le_mul_of_nonneg_left hMD' hQe0
  -- the near bands
  expose_names
  exact @leaf_estimate_stage_8 κ c₀ cc hcc Dm0 Msch hMsch Cg g cT cL cK cMc cm ce ce2 cQ CΛ eΛ CM1
    t3 Cb Cl hconst A bf k η₀ E hsub hS2 hη hη₀ q hq2 hq3 Nd p AD d s δ ρ kD hδ hδ8 hρ hρ1 hkb hkF
    hkB hcb hNl0 S hSd hSDm hSV hd2 hD2 hB2 hQ1 hK1 hlenMc Ms L hA6 Vl0 U MV hMV ε hεdef hNl4 c
    Cut hCutl hcat hmbb hmbT hrankH hroleD hS1c hNb hRl0 hVl00 hOs hCjg hΓadef hΓbdef hΓUdef Ee
    hEe0 hEeb hdB1 hVl0 hMt C C₂ hC hlen hC₂ hlen₂ hdBk hEk hρk hkD hk2 u hu hVle hlD hK hlogH hΛ0
    hΛ hE0 hVl0nn hUdef hT0 hsum hexpD hcEsum



private theorem leaf_estimate_stage_6 : LeafEstimateStage6Statement := by
  classical
  intro κ c₀ cc hcc Dm0 Msch hMsch Cg hCg g cT cL cK cMc cm ce ce2 cQ CΛ eΛ CM1 t3 Cb Cl hconst A
    bf k η₀ E hanc hpairs hsub hS2 hη hη₀ hne q hq2 hq3 Nd hNd p AD d s δ ρ kD hδ hδ8 hρ hρ1 hkb
    hkF hk1 fp dB hstd Nl hkB hcb hn_mono hNl0 Hm hHm1 hC S hSd hSDm hSV hd2 hdD hD2 hB2 hQ1 hlogH
    hK hK1 Lf ks S0 hS0T gs gset hcu hlenMc mbs Ms L hDS hsch' hA6 qG hqG1 Vl0 U hUdef hD0 hD1
    hU16 hU0 MV hMV hMV0 ε hεdef hε0 hεU hThrM hThrC Ts hTsdef BN τb hτb hτb1 hτbN hHτb hroot' zc
    hPH hNl4 hNq hpathG hstar hLsl c hcB Rr hRr Cut hCutl cf D₀ gE hgE hcat hhT hmbb hmbT mb' D
    hrankH hroleD
  let B₀ : (D₀.toLeafQ qG).BallData gset :=
    { hT := fun l e he => (AD.hT l e he).2.2
      htag := AD.htag
      dv := fun _ => d
      hPH := hPH
      N := BN
      hN := hNq }
  intro htagH
  let B : ((D₀.appendCat hcat mb').toLeafQ qG).BallData gset :=
    D₀.ballDataAppend hcat mb' qG B₀ (fun l e he => (hhT l e he).2.2.2) htagH
        (fun l e he => by
          rw [(hhT l e he).2.1]
          change fp.Lc + Lf.role l < fp.Lc + 5
          have! this := Lf.role_le l
          omega)
  intro S1 hS1S0 hS1c hbk hIB hpassD hhpassD hτr hτH' hτ0 hNlD NH hNHD τ₂ hτ₂ hτ₂1 hτ₂' hHed₂ Nb
    hNb hKN hRl0 hVl00 Os hOs Cjg hCjg Γa hΓadef hΓa Γb hΓbdef hΓb ΓU hΓUdef hΓU hrepD Ee hEe0
    hEeb hEeD' hMD' hdB1 hprin hstab hcD Gq hVE hVl0 hGq Mt hMt hTopD hUD hUT
  let Iw : ℕ :=
    ⌊Real.logb (2 : ℝ) (S.Dstar ^ (250 : ℕ))⌋₊
  intro hIw12 hGc
  have! hDm2 : 2 ≤ S.Dm := by rw [hSDm]; exact le_max_left _ _
  have! hT1 : 1 ≤ S.T := hSV.one_le_T (by norm_num) hd2 hD2 hB2 hQ1
  have! hNp : ∀ c' d', (((D.toLeafQ qG).pe d').length * ((D.toLeafQ qG).pe c').length : ℝ) ≤
      ((2 : ℝ) ^ A.famFuel) ^ 2 := by
    intro c' d'
    have! h1 : (((D.toLeafQ qG).pe d').length : ℝ) ≤ (2 : ℝ) ^ A.famFuel := by
      exact_mod_cast (D.toLeafQ qG).pe_length_le rfl d'
    have! h2 : (((D.toLeafQ qG).pe c').length : ℝ) ≤ (2 : ℝ) ^ A.famFuel := by
      exact_mod_cast (D.toLeafQ qG).pe_length_le rfl c'
    rw [sq]
    exact mul_le_mul h1 h2 (Nat.cast_nonneg _) (by positivity)
  have! hLB := D.leaf_bound qG hq2 hq3 hanc hne (fuel := A.famFuel) (up₀ := A.basicSlot p) (s := s)
    rfl (le_of_eq AD.hmH.symm) hNd hKN S1 hS1c (fun I hI => A.sub I (hS1c hI)) gs gset
    (fun I hI => Finset.subset_biUnion_of_mem gs (hS1S0 hI)) (2 ^ A.famFuel)
    (2 * A.famFuel + 2) (A.treeDepth + 1) ks (fun I hI => hbk I (hS1c hI))
    (fun l => (D.toLeafQ qG).pe_length_le rfl l)
    (fun c' d' i i' => (D.toLeafQ qG).desc_tOf_length_le rfl c' d' i i') AD.Tc
    (fun I hI => ⟨hS0T (hS1S0 hI), fun G hG => hG⟩) (Mp := (AD.Mp : ℝ))
    (fun y => by exact_mod_cast card_cells_mem_le A.G AD.Tc AD.hmult y)
    (fun I hI G hG => (hcu I (hS1S0 hI) G hG).1) (fun I hI G hG => (hcu I (hS1S0 hI) G hG).2)
    hNp (τ := 2 * η₀) (by positivity) (fun I hI c' d' hcd _ _ => hpairs I (hS1c hI) c' d' hcd)
    (CF := 1) one_pos (fun l jb V hV => bf.normF l jb hV) hsub hpassD (hτ0 (fp.Lc + 5)) gE
    (fun I _ G hG => hgE I G hG) hhpassD hτ0 AD.n hn_mono AD.hn0 hτr hτH' (Sz := 2)
    (by rw [Real.sqrt_one, mul_one]) d hNlD hNHD hτ₂ hτ₂1 hτ₂' hHed₂ default B hroot' hτb hτb1
    hHτb hτbN cc hcc hk1 (fun l => hkB) hkb hkF hLsl (Vl := fun _ => Vl0)
    (fun l _ => D.hlin_of_family qG l gset (A.treeDepth + 1) (c l)
      (fun G hG => dite_eq_left hG) (by rw [hVl0]; exact hVE l))
    fp.hP Γa Γb ΓU hΓa hΓb hΓU L hrepD hEeD' hMD' hρ hρ1 (η := A.η)
    (by rw [hη]; positivity) (p := 1 - 1 / 1200) (by norm_num) (by norm_num) hρ hρ1
    hSV (by norm_num) le_rfl hd2 hD2 hB2 hQ1 rfl hdD hqG1 3 le_rfl 1 Iw le_rfl hIw12.2.le
    (hIw12.1.trans (by
      have! this : (0 : ℝ) ≤ S.Dstar ^ 250 := by positivity
      change S.Dstar ^ 250 ≤ 2 * S.Dstar ^ 250
      linarith only [this]))
    (fun G => bf.vtag (bf.grpCenter d G)) hGc (fun _ => δ) (fun _ => fp.Hed)
    (fp.Kstar Dm0 dB Hm δ Nl kD δ) (fp.Kstar Dm0 dB Hm δ Nl kD δ) hprin hstab
    (ModeSchedule.Valid.Dstar_pow_le S hSV (packetW_nonneg _ _) hT1 hD1)
    (hSV.two_le_Jstar (by norm_num) (by norm_num) (by norm_num) hd2 hD2 hDm2)
    (by norm_num : (0 : ℝ) < 1 / 1024) (by norm_num : (1 / 1024 : ℝ) ≤ 1 / 16)
    (ceil_four_delta_le S.Jstar)
    four_two_delta_quarter_lt_one (fun I _ G hG j => (hsch' j G hG).2.2.2.2.2.1 _)
    (fun j h t G => Rr j h t G) _
    (fun j h hh t G c' hc h1 h2 => by
      rw [hRr j h hh t G]
      exact (@Finset.mem_filter _ _ (fun _ => @instDecidableAnd _ _ (instDecidableEqNat _ _)
        (instDecidableEqNat _ _)) _ _).mpr ⟨hc, h1, h2⟩)
    (fun I hI => hIB I (hS1c hI)) Cut (fun I hI j e he => (Finset.mem_filter.mp hI).2 j e he)
    (dyThr ε U S.Dstar) hε0 hεU hThrM hTopD hpathG hUD hUT
  obtain ⟨C, C₂, hC, hlen, hC₂, hlen₂, hUs, hsum⟩ := hLB
  clear * - A AD Cb Cg Cjg Cl Cut CΛ D Dm0 D₀ E Ee Gq Hm Iw Msch Mt Nb Nd Nl Os S S1 Ts U Vl0 cK
    cL cMc cQ cT ce ce2 cm dB eΛ fp g gs gset hC hCg hCjg hCutl hD0 hD1 hD2 hDS hDm2 hEe0 hGq hHm1
    hIB hK hK1 hMD' hMsch hMt hNb hNl0 hNl4 hOs hQ1 hRl0 hS1S0 hS1c hS2 hSDm hSV hSd hThrC hTsdef
    hU0 hU16 hUdef hVl0 hVl00 hcB hcD hcat hcb hcc hd2 hdB1 hkB hkF hkb hlogH hq2 hq3 hrankH
    hroleD hsch' hstar hsub hΓUdef hΓadef hΓbdef hδ hδ8 hε0 hεdef hη hη₀ hρ hρ1 k kD mb' p q qG t3
    ΓU Γa Γb δ ε η₀ ρ MV hMV hMV0 hEeb hsum hUs C C₂ hC₂ hlen hlen₂ hk1 hB2 cc κ hNd hne hanc CM1
    hconst hstd
  obtain ⟨hLck, hHmk, hdBk, hHedk, hHsk, hHWk, hδk, hEk, hρk, hK0k, hkD, hk2, hlb⟩ := hstd
  -- the exponents of the bound for `Λ` (the other constants stay packed for `leaf_final`)
  have hCΛ := hconst.2.2.2.2.2.2.2.2.2.1
  have heΛ := hconst.2.2.2.2.2.2.2.2.2.2.1
  have! hP1 : (1 : ℝ) ≤ fp.P := by exact_mod_cast fp.hP
  have! hkcc0 : (k : ℝ) ≤ (k : ℝ) ^ cc := le_self_pow₀ hk1 (by omega)
  have! hkD1 : (1 : ℝ) ≤ kD := hk1.trans (hkcc0.trans hkD)
  have! hkD2 : (2 : ℝ) ≤ kD := hk2.trans (hkcc0.trans hkD)
  have! hobt : ∃ x : ℝ, x = kD * fp.P := ⟨_, rfl⟩
  obtain ⟨u, hu⟩ := hobt
  have! hu1 : 1 ≤ u := by rw [hu]; exact one_le_mul_of_one_le_of_one_le hkD1 hP1
  have! hku : (k : ℝ) ≤ u := by
    rw [hu]; exact (hkcc0.trans hkD).trans (le_mul_of_one_le_right (by linarith only [hkD1]) hP1)
  -- the standing bounds at the accuracy `k`
  have! hMp0 : (0 : ℝ) ≤ AD.Mp := Nat.cast_nonneg _
  have! hNl1 : 1 ≤ Nl := by linarith only [hNl4]
  have! hcbexp : 2 * A.colBudget ≤ Real.exp ((k : ℝ) ^ cc) := by
    rw [← Real.exp_log (show 0 < 2 * A.colBudget by linarith only [hcb])]
    exact Real.exp_le_exp.mpr hkb
  have! hbig : 2 * (8 * A.colBudget + (1 + AD.Mp) * Nl) ≤ Real.exp ((k : ℝ) ^ cc) :=
    leaf_estimate_hbig κ c₀ cc A bf k p AD hkB hcb hNl4
  have! hNlexp : Nl ≤ Real.exp ((k : ℝ) ^ cc) := by
    have! this : Nl ≤ (1 + (AD.Mp : ℝ)) * Nl :=
      le_mul_of_one_le_left hNl0 (by linarith only [hMp0])
    linarith only [this, hbig, hcb, Real.exp_pos ((k : ℝ) ^ cc)]
  have! hMpexp : (AD.Mp : ℝ) ≤ Real.exp ((k : ℝ) ^ cc) := by
    have! h1 : (AD.Mp : ℝ) ≤ (1 + (AD.Mp : ℝ)) * Nl := by nlinarith only [hNl1, hMp0]
    linarith only [h1, hbig, hcb, Real.exp_pos ((k : ℝ) ^ cc)]
  have! hVle : (A.famVtxBound : ℝ) ≤ 8 * A.colBudget + 1 := by
    unfold ActiveSetup.famVtxBound
    have! this := Nat.floor_le (show (0 : ℝ) ≤ 8 * A.colBudget by linarith only [hcb])
    push_cast
    linarith only [this]
  have! hVexp : (A.famVtxBound : ℝ) ≤ 5 * Real.exp ((k : ℝ) ^ cc) := by
    linarith only [hVle, hcbexp, hcb]
  have! hkcc1 : (1 : ℝ) ≤ (k : ℝ) ^ cc := one_le_pow₀ hk1
  have! hkDle : kD ≤ kD ^ (cc + 6) := le_self_pow₀ hkD1 (by omega)
  have! hkk : (k : ℝ) ^ cc ≤ kD ^ (cc + 6) := hkD.trans hkDle
  have! h64D : 64 * kD ≤ kD ^ (cc + 6) :=
    leaf_estimate_h64D cc hcc kD hkD1 hkD2
  have! h64 : 64 * (k : ℝ) ^ cc ≤ kD ^ (cc + 6) := by linarith only [h64D, hkD]
  have! hkK0 : Real.log bumpConst + 68 ≤ (k : ℝ) ^ cc := by
    have! this : (k : ℝ) ≤ (k : ℝ) ^ cc := le_self_pow₀ hk1 (by omega)
    linarith only [this, hK0k]
  -- the height of the modes
  have! hlogHm : Real.log Hm ≤ kD ^ (cc + 6) :=
    leaf_estimate_hlogHm κ c₀ cc A k δ kD hδ hHm1 hdBk hHsk hHWk hδk hkD hkD1 hkcc1 hkDle hkk h64D
      h64 hkK0
  -- `log D_*` and the cutoff, by `log_modeStarG_poly`
  have! hkDP : (1 : ℝ) ≤ kD * fp.P := one_le_mul_of_one_le_of_one_le hkD1 hP1
  have! hmsG := hCg fp dB (H := Hm) (δc := δ) (N := Nl) (k := kD) (δ := δ) hkD1
    (hLck.trans hkk)
    (hHmk.trans ((pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right (hkcc0.trans hkD)
      (by linarith only [hP1])) cc).trans (pow_le_pow_right₀ hkDP (by omega))))
    (hdBk.trans hkk) AD.hHed2 (hHedk.trans hkk) hHm1 hlogHm hδ
    (hδk.trans (Real.exp_le_exp.mpr hkDle)) hNl0 (hNlexp.trans (Real.exp_le_exp.mpr hkk))
    ((by linarith only [hcbexp, hcb] : A.colBudget ≤ Real.exp ((k : ℝ) ^ cc)).trans
      (Real.exp_le_exp.mpr hkk)) hδ (hδk.trans (Real.exp_le_exp.mpr hkDle))
  expose_names
  exact @leaf_estimate_stage_7 κ c₀ cc hcc Dm0 Msch hMsch Cg g cT cL cK cMc cm ce ce2 cQ CΛ eΛ CM1
    t3 Cb Cl hconst A bf k η₀ E hsub hS2 hη hη₀ hne q hq2 hq3 Nd p AD d s δ ρ kD hδ hδ8 hρ hρ1 hkb
    hkF hk1 hkB hcb hNl0 hHm1 S hSd hSDm hSV hd2 hD2 hB2 hQ1 hlogH hK hK1 hlenMc Ms L hDS hsch'
    hA6 Vl0 U hUdef hD0 hD1 hU16 MV hMV ε hεdef hε0 hNl4 hstar c hcB Cut hCutl hcat hmbb hmbT
    hrankH hroleD hS1S0 hS1c hIB hNb hRl0 hVl00 hOs hCjg hΓadef hΓbdef hΓUdef Ee hEe0 hEeb hMD'
    hdB1 hcD hVl0 hMt C C₂ hC hlen hC₂ hlen₂ hUs hsum hdBk hHedk hEk hρk hkD hk2 hCΛ heΛ hP1 u hu
    hu1 hku hNlexp hVle hmsG



private theorem leaf_estimate_stage_5 : LeafEstimateStage5Statement := by
  classical
  intro κ c₀ cc hcc Dm0 Msch hMsch Cg hCg g cT cL cK cMc cm ce ce2 cQ CΛ eΛ CM1 t3 Cb Cl hconst A
    bf k η₀ E hanc hpairs hsub hS2 hη hη₀ hne q hq2 hq3 Nd hNd p AD d s δ ρ kD hδ hδ8 hρ hρ1 hkb
    hkF hk1 fp dB hstd hdδ Nl hkB hcb hn_mono hNl0 Hm hHm1 hdim hC S hSd hSDm hSV hd2 hdD hD2 hB2
    hQ1 hbox hlogH hK hK1 Lf ks S0 hS0T gs gset hcu hlenMc mbs Ms L hexp hnotg hDS hsch' hA6 qG
    hqG1 Vl0 hVl0 U hUdef hU4 hD0 hD1 hU16 hU0 MV hMV hMV0 ε hεdef hε0 hεU hUD hThrD hThrM hThrC
    Ts hTsdef BN τb hτb hτb1 hτbN hHτb hroot' ρ₀ zc gsc hGz hMLE hPH hNl4 hNq hpathG hBσG hstar
    hLsl c hcB hVE Rr hRr Cut hCutl hTop cf D₀ gE hgE hcat hhT hmbb hmbT mb' D hrankH hroleD
  let B₀ : (D₀.toLeafQ qG).BallData gset :=
    { hT := fun l e he => (AD.hT l e he).2.2
      htag := AD.htag
      dv := fun _ => d
      hPH := hPH
      N := BN
      hN := hNq }
  intro htagH
  let B : ((D₀.appendCat hcat mb').toLeafQ qG).BallData gset :=
    D₀.ballDataAppend hcat mb' qG B₀ (fun l e he => (hhT l e he).2.2.2) htagH
        (fun l e he => by
          rw [(hhT l e he).2.1]
          change fp.Lc + Lf.role l < fp.Lc + 5
          have! this := Lf.role_le l
          omega)
  intro S1 hS1S0 hS1c hbk hIB hpassD hhpassD hτr hτH' hτ0 hNlD NH hNHD τ₂ hτ₂ hτ₂1 hτ₂' hHed₂ Nb
    hNb hKN hRl0 hVl00 Os hOs Cjg hCjg Γa hΓadef hΓa Γb hΓbdef hΓb ΓU hΓUdef hΓU hrepD Ee hEe0
    hEeb hEeD' hMD'
  have! hzc : ∀ l, ∀ G ∈ gset, (Ms l G).zc = bf.vtag (bf.grpCenter d G) := by
    intro l G hG
    obtain ⟨ρ₀, z, g, hGz, -, -, -, -, -, -, -, hzc, -⟩ := hexp l G hG
    rw [hzc]
    congr 1
    simp [ActiveSetup.BasicFamilies.grpCenter, hGz]
  have! hgrpE : ∀ l, ∀ G ∈ gset, (Ms l G).δc = δ ∧ (Ms l G).cl = slotCoeff l ∧
      ∀ i, (Ms l G).ρ i ∈ Set.Icc (0 : ℝ) 1 := by
    intro l G hG
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hδc', hcl, hρM, -⟩ := hexp l G hG
    exact ⟨hδc', hcl, hρM⟩
  have! hdB1 : 1 ≤ dB := by
    have! hW2 : Real.exp 2 ≤ max A.H ActiveSetup.padW :=
      le_trans (le_max_left _ _) (le_max_right _ _)
    have! h1 : (2 : ℝ) ≤ Real.log (max A.H ActiveSetup.padW) := by
      rw [Real.le_log_iff_exp_le (lt_of_lt_of_le (Real.exp_pos 2) hW2)]
      exact hW2
    have! h2 : (2 : ℝ) ≤ dB := h1.trans (Nat.le_ceil _)
    exact_mod_cast (show (1 : ℝ) ≤ dB by linarith only [h2])
  have! hprin : ∀ G ∈ gset, (D.withQ0 (qG G)).PrinOK G δ fp.Hed (fp.Kstar Dm0 dB Hm δ Nl kD δ)
      (fp.Kstar Dm0 dB Hm δ Nl kD δ) :=
    leaf_estimate_hprin κ c₀ Dm0 A bf p AD d s δ ρ kD hδ hδ8 hρ hdδ hNl0 hHm1 hdim hC S hSd hbox
      hK1 hlenMc Ms hDS hsch' hA6 hqG1 c hcat hmbb hmbT hzc hgrpE hdB1
  -- the stabilization of the modes of every group of the leaf
  have! hBσ1 : ∀ l G, 1 ≤ (Ms l G).Bσ := fun l G => (Ms l G).one_le_Bσ
  have! hstab : ∀ G ∈ gset, (D.withQ0 (qG G)).Stab := by
    expose_names
    exact @leaf_estimate_hstab κ c₀ cc Dm0 Msch Cg g cm ce ce2 cQ CΛ eΛ CM1 t3 Cb Cl A bf p AD d s
      δ kD hNl0 S hSd hSV hd2 hD2 hB2 hQ1 hK1 hlenMc Ms hnotg hsch' hA6 hqG1 hD0 hPH hNq hBσG c
      hcat hhT hmbb hmbT htagH hBσ1
  have! hcD : ∀ j (G : {G // G ∈ gset}), D.c j G.1 = c j G := fun j G => dite_eq_left G.2
  set! Gq : ℝ := Real.exp ((6144 * (cc + 1) * (1024 * (cc + 1) + cc + 7) + 4) *
    (1 + Real.log (2 * (k : ℝ))) ^ 2) with hGq
  rewrite [← hGq] at hVl0 hVE hTop
  set! Mt : ℝ := 24 * (2 * Gq + 2 * S.K * Vl0) *
    (Finset.range (S.Jstar + 1) ×ˢ Ts ×ˢ dyThr ε U S.Dstar).card / ρ with hMt
  have! hTopD : ∀ j y, ∀ h ∈ ModeComponents.upperHeights D.SP.Jst D.SP.δs,
      ∀ t ∈ Finset.range (Nat.log 2 ⌊D.S.Dstar⌋₊ + 1) ×ˢ
        Finset.range (Nat.log 2 ⌊D.S.Dstar⌋₊ + 1), ∀ σ ∈ dyThr ε U S.Dstar,
      (∑ G : {G // G ∈ gset}, (((fp.useInst G.1 D.S.K (Rr j h t G).Nd).filter fun p =>
          (∀ e ∈ Cut j, ¬ dyadicGridCell A.G p.1.1 p.1.2 ⊆ dyadicGridCell A.G e.1 e.2) ∧
          y ∈ dyadicGridCell A.G p.1.1 p.1.2 ∧
            σ ^ 2 ≤ (D.Ms j G.1).nodeSize (D.withQ0 (qG G.1)).S D.hA D.SP (D.c j G.1) h p).image
          fun p => (Rr j h t G).rep p.2).card : ℝ) ≤ Mt * σ ^ (-2 : ℝ) := by
    intro j y h hh t ht σ hσ
    have! hhJ : h ∈ Finset.range (S.Jstar + 1) := (Finset.mem_filter.mp hh).1
    have! hσ0 : 0 < σ := lt_of_lt_of_le (inv_pos.mpr hD0) (hThrD σ hσ)
    simp only [hcD]
    refine ((hTop j y h hhJ t ht σ hσ).trans (min_le_right _ _)).trans (le_of_eq ?_)
    rw [hMt, hVl0, Real.rpow_neg hσ0.le, Real.rpow_two]
    exact (div_div _ _ _).symm.trans (div_eq_mul_inv _ _)
  -- the class sizes
  have! hUD : ∀ I ∈ S1, ∀ G ∈ gs I, ∀ h ∈ ModeComponents.upperHeights D.SP.Jst D.SP.δs, ∀ j,
      ∀ F ∈ (D.withQ0 (qG G)).goodCls G I j h, (D.withQ0 (qG G)).clsSize G I j F ≤ U :=
    leaf_estimate_hUD κ c₀ cc hcc Dm0 A bf p AD d s δ kD hcb hNl0 S hK1 hlenMc Ms L hexp hsch' hA6
      U hU4 hD0 hD1 gsc hMLE c hcB Cut hcat hmbb hmbT hS1S0 hS1c hIB hcD
  have! hUT :
      Real.sqrt (D.Tside qG (2 ^ A.famFuel) (2 * A.famFuel + 2) 1 E cc k (fun _ => Vl0) ρ) ≤
      U := by
    rw [D.Tside_eq_F, hUdef]
    exact le_max_right _ _
  -- the core constants
  set! Iw : ℕ := ⌊Real.logb 2 (S.Dstar ^ 250)⌋₊ with hIw
  have! hIw12 := two_pow_floor_logb (one_le_pow₀ hD1 : (1 : ℝ) ≤ S.Dstar ^ 250)
  have! hΞ : ∀ x : ℝ, 2 ≤ x → 8 * x ≤ x ^ 1000 :=
    leaf_estimate_hΞ
  have! hGc : ∀ G ∈ gset, (∀ j, 8 * (D.Ms j G).Λ ≤ D.S.Ξ) ∧
      (∀ j, (D.Ms j G).zc = bf.vtag (bf.grpCenter d G)) ∧
      (bf.vtag (bf.grpCenter d G)).dim ≤ D.S.dmax := by
    intro G hG
    refine ⟨fun j => ?_, fun j => hzc j G hG, ?_⟩
    · change 8 * (Ms j G).Λ ≤ S.Dstar ^ 1000
      have! this := (hsch' j G hG).2.1
      linarith only [this, hΞ S.Dstar hD2]
    · change _ ≤ S.dmax
      rw [hSd]
      have! this := hdim (bf.grpCenter d G)
      omega
  -- the leaf bound
  expose_names
  exact @leaf_estimate_stage_6 κ c₀ cc hcc Dm0 Msch hMsch Cg hCg g cT cL cK cMc cm ce ce2 cQ CΛ eΛ
    CM1 t3 Cb Cl hconst A bf k η₀ E hanc hpairs hsub hS2 hη hη₀ hne q hq2 hq3 Nd hNd p AD d s δ ρ
    kD hδ hδ8 hρ hρ1 hkb hkF hk1 hstd hkB hcb hn_mono hNl0 hHm1 hC S hSd hSDm hSV hd2 hdD hD2 hB2
    hQ1 hlogH hK hK1 hS0T hcu hlenMc Ms L hDS hsch' hA6 hqG1 Vl0 U hUdef hD0 hD1 hU16 hU0 MV hMV
    hMV0 ε hεdef hε0 hεU hThrM hThrC hTsdef hτb hτb1 hτbN hHτb hroot' zc hPH hNl4 hNq hpathG hstar
    hLsl c hcB Rr hRr Cut hCutl hgE hcat hhT hmbb hmbT hrankH hroleD htagH hS1S0 hS1c hbk hIB
    hpassD hhpassD hτr hτH' hτ0 hNlD hNHD hτ₂ hτ₂1 hτ₂' hHed₂ hNb hKN hRl0 hVl00 hOs hCjg hΓadef
    hΓa hΓbdef hΓb hΓUdef hΓU hrepD Ee hEe0 hEeb hEeD' hMD' hdB1 hprin hstab hcD hVE hVl0 hGq hMt
    hTopD hUD hUT hIw12 hGc



private theorem leaf_estimate_stage_4 : LeafEstimateStage4Statement := by
  classical
  intro κ c₀ cc hcc Dm0 Msch hMsch Cg hCg g cT cL cK cMc cm ce ce2 cQ CΛ eΛ CM1 t3 Cb Cl hconst A
    bf k η₀ E hanc hpairs hsub hS2 hη hη₀ hne q hq2 hq3 Nd hNd p AD d s δ ρ kD hδ hδ8 hρ hρ1 hkb
    hkF hk1 fp dB hstd hdδ Nl hkB hcb hn_mono hNl0 Hm hHm1 hdim hC S hSd hSDm hSV hd2 hdD hD2 hB2
    hQ1 hbox hlogH hK hK1 Lf ks S0 hS0T gs gset hcu U_1 hlenMc mbs Ms L hexp hnotg herrW hDS hsch'
    hA6 qG hqG1 Vl0 hVl0 U hUdef hU4 hD0 hD1 hU16 hU0 MV hMV hMV0 ε hεdef hε0 hεU hUD hThrD hThrM
    hThrC Ts hTsdef BN τb hτb hτb1 hτbN hHτb hroot' ρ₀ zc gsc hGz hMLE hPH hNl4 hNq hpathG hBσG
    hstar hLsl c hcrep hcB hVE Rr hRr Cut hCutl hTop cf D₀ gE hgE hcat hhT hTmpl hmbb hmbT mb' D
    hrankH hroleD
  let B₀ : (D₀.toLeafQ qG).BallData gset :=
    { hT := fun l e he => (AD.hT l e he).2.2
      htag := AD.htag
      dv := fun _ => d
      hPH := hPH
      N := BN
      hN := hNq }
  intro htagH
  let B : ((D₀.appendCat hcat mb').toLeafQ qG).BallData gset :=
    D₀.ballDataAppend hcat mb' qG B₀ (fun l e he => (hhT l e he).2.2.2) htagH
        (fun l e he => by
          rw [(hhT l e he).2.1]
          change fp.Lc + Lf.role l < fp.Lc + 5
          have! this := Lf.role_le l
          omega)
  intro S1 hS1S0 hS1c hbk hIB hpassD hhpassD hτr hτH' hτ0 hNlD
  have! hNHD : ∀ I ∈ S1, ∀ a, ∀ M : bf.Vtx → Prop,
      ((mainLabelsM A.G fp.Mc (bf.origCols a) (D.cat a) I (fp.Lc + 5) M d).card : ℝ) ≤
        2 * A.colBudget + (1 + AD.Mp) * Nl := by
    intro I _ a M
    have! h1 := mainLabelsM_subset (G := A.G) (Mc := fp.Mc) (O := bf.origCols a) (D.cat a) I
      (fp.Lc + 5) M d
    refine le_trans (Nat.cast_le.mpr (Finset.card_le_card h1)) ?_
    refine (bf.card_mainLabels_le_tmpl a (D.cat a) I (fp.Lc + 5)).trans ?_
    have! h2 : (bf.tmplPath (D.cat a) (dyadicGridLeft A.G I.1 I.2) : ℝ) ≤ (1 + AD.Mp) * Nl :=
      hTmpl a _
    linarith only [h2]
  -- the residual threshold of the helper tests
  set! NH : ℝ := 2 * A.colBudget + (1 + AD.Mp) * Nl with hNH
  rewrite [← hNH] at hNHD
  set! τ₂ : ℝ := AD.τ₃ / (1 + A.colBudget * Real.sqrt (AD.n (fp.Lc + 4)) *
    (A.colBudget * Real.sqrt NH)) with hτ₂def
  have! hden : 0 < 1 + A.colBudget * Real.sqrt (AD.n (fp.Lc + 4)) *
      (A.colBudget * Real.sqrt NH) :=
    leaf_estimate_hden κ c₀ A bf p AD hcb hNl4
  have! hτ₂ : 0 < τ₂ := div_pos AD.hτ₃ hden
  have! hτ₂1 : τ₂ ≤ 1 :=
    leaf_estimate_hτ₂1 κ c₀ A bf p AD hcb hNl4 hτ₂def hden
  have! hτ₂' : τ₂ * (A.colBudget * Real.sqrt (AD.n (fp.Lc + 4)) * (A.colBudget * Real.sqrt NH)) ≤
      AD.τ₃ :=
    leaf_estimate_hτ₂' κ c₀ A bf p AD hcb hNl4 hτ₂def hden
  have hHed₂ : Real.exp (A.Dg * (1 + Real.log A.Hsrc + Real.log τ₂⁻¹) ^ A.Dg) ≤ fp.Hed :=
    AD.hHedτ₂
  -- the stack energies of the near bands
  set! Nb : ℕ := Nat.log 2 S.K + 1 with hNb
  have! hKN : S.K ≤ 2 ^ Nb := (Nat.lt_pow_succ_log_self (by norm_num) S.K).le
  have! hRl0 : 0 < dyadicGridLength A.G A.R.1 := dyadicGridLength_pos A.G A.R.1
  have! hcapV0 : 0 ≤ FamParams.capV A cc k :=
    leaf_estimate_hcapV0 κ c₀ cc A k hRl0
  have! hVl00 : 0 ≤ Vl0 :=
    leaf_estimate_hVl00 cc k S Vl0 hVl0
  have! hB00 : 0 ≤ FamParams.SideInput.sideB0 A cc k Vl0 :=
    leaf_estimate_hB00 κ c₀ cc A k Vl0 hRl0 hVl00
  set! Os := FamParams.SideLeafM.nOs (2 ^ A.famFuel) (2 * A.famFuel + 2) with hOs
  set! Cjg : ℝ := (((2 * A.famFuel + 2 : ℕ) : ℝ) + 1) ^ 2 * Real.exp (2 * (1024 * (cc + 1) *
    (1024 * (cc + 1) + cc + 7) * (1 + Real.log (2 * (k : ℝ))) ^ 2)) with hCjg
  set! Γa : Fin 4 → ℝ := fun _ => (Os.card * (Nb * (2 * FamParams.capV A cc k +
    16 * (Cjg * FamParams.SideInput.sideB0 A cc k Vl0) + 16 * (Nb * (Cjg * (Nb *
      FamParams.capV A cc k)))) + FamParams.SideInput.sideB0 A cc k Vl0)) /
    dyadicGridLength A.G A.R.1
    with hΓadef
  have! hΓa : ∀ a, D.u ≠ some a → fp.stackEA Os (D.cat a) (D.mbs a) (D.toLeafQ qG).Dpre Nb
      (FamParams.capV A cc k) (FamParams.SideInput.sideB0 A cc k ((fun _ => Vl0) a)) ≤
        (fp.P + 2) * Γa a * dyadicGridLength A.G A.R.1 := by
    intro a _
    have! h := fp.stackEA_le_G0 Os (D.cat a) (D.mbs a) (D.toLeafQ qG).Dpre Nb hcapV0 hB00
      (2 * A.famFuel + 2) cc hk1 hkB hkF (fun ω _ => (D.toLeafQ qG).Dpre_length_le rfl ω)
    dsimp only at h
    refine h.trans (le_of_eq ?_)
    simp only [hΓadef]
    rw [mul_assoc ((fp.P : ℝ) + 2), div_mul_cancel₀ _ hRl0.ne', hCjg]
  set! Γb : Fin 4 → ℝ := fun _ => Os.card * (Nb * FamParams.capV A cc k +
      FamParams.SideInput.sideB0 A cc k Vl0) /
    dyadicGridLength A.G A.R.1 with hΓbdef
  have! hΓb : ∀ b, D.u ≠ some b → (Os.card : ℝ) * (Nb * FamParams.capV A cc k +
      FamParams.SideInput.sideB0 A cc k ((fun _ => Vl0) b)) ≤
      Γb b * dyadicGridLength A.G A.R.1 := by
    intro b _
    simp only [hΓbdef]
    exact (div_mul_cancel₀ _ hRl0.ne').ge
  set! ΓU : ℝ := Os.card * (2 * (4 * E * dyadicGridLength A.G A.R.1)) /
    dyadicGridLength A.G A.R.1 with hΓUdef
  have! hΓU : (Os.card : ℝ) * (2 * (4 * E * dyadicGridLength A.G A.R.1)) ≤
      ΓU * dyadicGridLength A.G A.R.1 := by
    rw [hΓUdef]
    exact (div_mul_cancel₀ _ hRl0.ne').ge
  -- the representations of the frozen families and the physical errors
  have! hrepD : ∀ I ∈ S1, ∀ G ∈ gs I, ∀ l, D.u ≠ some l → (D.withQ0 (qG G)).RepAt L l G I := by
    intro I hI G hG l _
    have! hGs : G ∈ gset := Finset.mem_biUnion.mpr ⟨I, hS1S0 hI, hG⟩
    refine (D₀.repAt_appendCat hcat mb' hanc hrankH hroleD (qG G) L l G I).mpr ?_
    exact D₀.repAt_of_family qG L l gset _ (c l) (fun G' hG' => dite_eq_left hG') (hcrep l)
      hGs (hIB I (hS1c hI))
  have hEeD := D₀.errAt_energy_le qG L S1 gs gset
    (fun I hI => Finset.subset_biUnion_of_mem gs (hS1S0 hI)) (le_trans (by
      refine Finset.sum_le_sum fun l _ => Finset.sum_le_sum fun G _ => ?_
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_
        (fun I _ _ => integral_nonneg fun y => sq_nonneg _)
      intro I hI
      obtain ⟨hI1, hG⟩ := Finset.mem_filter.mp hI
      exact Finset.mem_filter.mpr ⟨hS1S0 hI1, hG⟩) herrW.down)
  have! hobt : ∃ Ee : ℝ,
      ∑ I ∈ S1, ∑ G ∈ gs I, ∑ l, ‖(D₀.withQ0 (qG G)).errAt L l G I‖ ^ 2 ≤ Ee ∧
      Ee ≤ (8 * dB * δ + 2 * δ ^ 2) * (4 * Nl * A.colBudget ^ 2 * 1) *
        ((4 * (AD.Mp * A.famVtxBound) : ℕ) : ℝ) * dyadicGridLength A.G A.R.1 :=
    ⟨_, hEeD, le_rfl⟩
  obtain ⟨Ee, hEe0, hEeb⟩ := hobt
  have! hEeD' : ∑ I ∈ S1, ∑ G ∈ gs I, ∑ l, ‖(D.withQ0 (qG G)).errAt L l G I‖ ^ 2 ≤ Ee := by
    refine le_of_eq_of_le (Finset.sum_congr rfl fun I hI => Finset.sum_congr rfl fun G _ =>
      Finset.sum_congr rfl fun l _ => ?_) hEe0
    rw [D₀.errAt_appendCat hcat mb' hanc hrankH hroleD (qG G) L l G (hS1c hI)]
  have! hMD' : ∑ I ∈ S1, dyadicGridLength A.G I.1 * (gs I).card ≤
      (AD.Mp * A.famVtxBound : ℕ) * dyadicGridLength A.G A.R.1 := by
    refine integrated_cap_le A.G S1 (fun I => ((gs I).card : ℝ)) A.R
      (fun I hI => A.sub I (hS1c hI)) fun x => ?_
    have! hcard : ((S1.filter fun I => x ∈ dyadicGridCell A.G I.1 I.2).card : ℝ) ≤ AD.Mp :=
      by exact_mod_cast le_trans (Finset.card_le_card (Finset.filter_subset_filter _
        (hS1S0.trans hS0T))) (card_cells_mem_le A.G AD.Tc AD.hmult x)
    calc ∑ I ∈ S1.filter (fun I => x ∈ dyadicGridCell A.G I.1 I.2), ((gs I).card : ℝ)
        ≤ ∑ _I ∈ S1.filter (fun I => x ∈ dyadicGridCell A.G I.1 I.2), (A.famVtxBound : ℝ) :=
          Finset.sum_le_sum fun I _ => by exact_mod_cast fp.card_groupsAt_le I ks
      _ = (S1.filter fun I => x ∈ dyadicGridCell A.G I.1 I.2).card * (A.famVtxBound : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ AD.Mp * A.famVtxBound := mul_le_mul_of_nonneg_right hcard (Nat.cast_nonneg _)
      _ = ((AD.Mp * A.famVtxBound : ℕ) : ℝ) := by push_cast; ring
  -- the centers of the groups and the principal-bin data
  expose_names
  exact @leaf_estimate_stage_5 κ c₀ cc hcc Dm0 Msch hMsch Cg hCg g cT cL cK cMc cm ce ce2 cQ CΛ eΛ
    CM1 t3 Cb Cl hconst A bf k η₀ E hanc hpairs hsub hS2 hη hη₀ hne q hq2 hq3 Nd hNd p AD d s δ ρ
    kD hδ hδ8 hρ hρ1 hkb hkF hk1 hstd hdδ hkB hcb hn_mono hNl0 hHm1 hdim hC S hSd hSDm hSV hd2 hdD
    hD2 hB2 hQ1 hbox hlogH hK hK1 hS0T hcu hlenMc Ms L hexp hnotg hDS hsch' hA6 hqG1 Vl0 hVl0 U
    hUdef hU4 hD0 hD1 hU16 hU0 MV hMV hMV0 ε hεdef hε0 hεU hUD hThrD hThrM hThrC hTsdef hτb hτb1
    hτbN hHτb hroot' ρ₀ zc gsc hGz hMLE hPH hNl4 hNq hpathG hBσG hstar hLsl c hcB hVE Rr hRr Cut
    hCutl hTop hgE hcat hhT hmbb hmbT hrankH hroleD htagH hS1S0 hS1c hbk hIB hpassD hhpassD hτr
    hτH' hτ0 hNlD hNHD hτ₂ hτ₂1 hτ₂' hHed₂ hNb hKN hRl0 hVl00 hOs hCjg hΓadef hΓa hΓbdef hΓb
    hΓUdef hΓU hrepD Ee hEe0 hEeb hEeD' hMD'



private theorem leaf_estimate_stage_3 : LeafEstimateStage3Statement := by
  classical
  intro κ c₀ cc hcc Dm0 Msch hMsch Cg hCg g cT cL cK cMc cm ce ce2 cQ CΛ eΛ CM1 t3 Cb Cl hconst A
    bf k η₀ E hanc hpairs hsub hS2 hη hη₀ hne q hq2 hq3 Nd hNd p AD d s δ ρ kD hδ hδ8 hρ hρ1 hkb
    hkF hk1 fp dB hstd hdδ Nl hkB hcb hn_mono hNl0 Hm hHm1 hdim hC S hSd hSDm hSV hd2 hdD hD2 hB2
    hQ1 hbox hlogH hK hK1 Lf ks S0 hS0T hS0c gs gset hcu U_1 hlenMc mbs Ms L hexp hnotg herrW hDS
    hsch' hA6 qG hqG1 Vl0 hVl0 U hUdef hU4 hD0 hD1 hU16 hU0 MV hMV hMV0 ε hεdef hε0 hεU hUD hThrD
    hThrM hThrC Ts hTsdef BN τb hτb hτb1 hτbN hHτb hroot' ρ₀ zc gsc hGz hMLE hPH hNl4 hNq hpathG
    hBσG hstar hLsl c hcrep hcB hVE Rr hRr Cut hCutl hTop
  let cf : (l : Fin (4 : ℕ)) → (G : bf.Grp) → ℤ → ℤ × ℤ → (Ms l G).Md → ℂ :=
    fun (l : Fin (4 : ℕ)) (G : bf.Grp) => if hG : G ∈ gset then c l ⟨G, hG⟩ else fun _ _
      _ => (0 : ℂ)
  let D₀ : fp.SideInput :=
    { cat := AD.cat, mbs := mbs, Lf := Lf, u := A.uslot p, S := S, hA := hA6,
      SP := S.sideParams (1 / 1024 : ℝ), hK := hK1,
      n := Fintype.card (bf.Lab ⊕ Fin fp.Mc), Ms := Ms, c := cf }
  intro gE hgE Wm main hmainR
  have! hpassW : ∀ i : Wm, (main i).2.2.Pass A.G (bf.origCols (main i).1) (main i).2.1 A.csrc
      A.Hsrc bf.vtag (A.w (main i).2.1) (catThreshold A.famVtxBound AD.τ₃ AD.n (main i).2.2.r)
      fp.mH (AD.cat (main i).1) :=
    fun i => AD.hpassM i.1.1 i.1.2.1.1 i.1.2.1.2 i.1.2.2
  -- the helper catalogs on the whole side states
  have! hMcH : ∀ l, (AD.cat l).length + AD.Tc.card * AD.Tmax ≤ fp.Mc := fun l => by
    have! h1 := AD.hlen l
    have h2 : fp.Mc = AD.Tc.card * AD.Tmax + AD.Tc.card * AD.Tmax := AD.hMc
    omega
  have! hobt := FamParams.helper_sides_closure AD.Dst fp
    AD.Tc AD.hTc AD.hst (Fin A.famVtxBound) AD.cat (fun l i I => (D₀.toLeafQ qG).sv l (gE I i) I)
    (fun l i I => by
      rw [D₀.toLeafQ_sv_restrict qG l (gE I i) I]
      exact D₀.toLeafQ_sv_fresh qG l (gE I i) I)
    main hmainR (fun i => catThreshold A.famVtxBound AD.τ₃ AD.n (main i).2.2.r) hpassW
    A.exp_two_le_Hsrc AD.hτ₃ AD.hMp1 AD.hKh AD.hn0 AD.hgrow AD.hcapH hMcH
  obtain ⟨hcat, hhp, hmp, hball, hcum, hhcount, hhT⟩ := hobt
  -- the main budgets of the extended catalogs
  have! hTmpl : ∀ l y, (bf.tmplPath (AD.cat l ++ hcat l) y : ℝ) ≤ (1 + AD.Mp) * Nl := by
    intro l y
    rw [bf.tmplPath_append, Nat.cast_add]
    have! h1 := bf.tmplPath_le fp.Mc (AD.cat l) (hlenMc l) l (fun e he => AD.hTc (AD.hT l e he).1)
      (r := fp.Lc + 5) (fun e he => (AD.hT l e he).2.1) hNl0 (fun I _ => AD.hlab l I _ le_rfl) y
    have! h2 := bf.tmplPath_le_of_births (hcat l) AD.Tc (fun e he => (hhT l e he).1) hNl0
      (card_cells_mem_le A.G AD.Tc AD.hmult) (fun J hJ => hhcount l J hJ) y
    linarith only [h1, h2]
  have! hmbb : ∀ l, ∀ e ∈ AD.cat l ++ hcat l, e.birth ∈ A.cells := fun l e he => by
    rcases List.mem_append.mp he with h | h
    · exact AD.hTc (AD.hT l e h).1
    · exact AD.hTc (hhT l e h).1
  have! hmbT : ∀ l y, 8 * A.colBudget + bf.tmplPath (AD.cat l ++ hcat l) y ≤
      8 * A.colBudget + (1 + AD.Mp) * Nl := fun l y => by linarith only [hTmpl l y]
  let mb' : ∀ l, bf.MainBudget (AD.cat l ++ hcat l) := fun l =>
    { hb := hmbb l, B := 8 * A.colBudget + (1 + AD.Mp) * Nl, hTp := hmbT l }
  -- the side input of the leaf
  let D : fp.SideInput := D₀.appendCat hcat mb'
  have! hrankH : ∀ l, ∀ e ∈ hcat l, fp.hrank ≤ e.rank := fun l e he => by
    rw [(hhT l e he).2.1]; rfl
  have! hroleD : ∀ l, D₀.Lf.role l ≤ 4 := fun l => Lf.role_le l
  -- the ball data
  let B₀ : (D₀.toLeafQ qG).BallData gset :=
    { hT := fun l e he => (AD.hT l e he).2.2
      htag := AD.htag
      dv := fun _ => d
      hPH := hPH
      N := BN
      hN := hNq }
  have! htagH : ∀ l, ∀ e ∈ hcat l, bf.occAvail e.tag.2.1 e.tag.1 := by
    intro l e he
    obtain ⟨hb, -, ⟨M, hM⟩, -⟩ := hhT l e he
    exact FamParams.occAvail_of_mem_X (AD.hTc hb) (fp.maskOf_mem_X e.birth M hM)
  let B := D₀.ballDataAppend hcat mb' qG B₀ (fun l e he => (hhT l e he).2.2.2) htagH
    (fun l e he => by
      rw [(hhT l e he).2.1]
      change fp.Lc + Lf.role l < fp.Lc + 5
      have! this := Lf.role_le l
      omega)
  -- the retained cells of the leaf: below no failure root and no first-top cut
  set! S1 := S0.filter fun I => ∀ j, ∀ e ∈ Cut j,
    ¬ dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G e.1 e.2 with hS1
  have! hS1S0 : S1 ⊆ S0 := Finset.filter_subset _ _
  have! hS1c : S1 ⊆ A.cells := hS1S0.trans hS0c
  have! hIR : ∀ I ∈ A.cells, A.R.1 ≤ I.1 := fun I hI =>
    dyadicGridCell_depth_le_of_subset A.G I A.R (A.sub I hI)
  have! hbk : ∀ I ∈ A.cells, ((I.1 - A.R.1) / (S.K : ℤ)).toNat < A.treeDepth + 1 := by
    intro I hI
    have! h1 : (I.1 - A.R.1).toNat ≤ A.treeDepth :=
      Finset.le_sup (f := fun I : ℤ × ℤ => (I.1 - A.R.1).toNat) hI
    have! h0 : 0 ≤ I.1 - A.R.1 := by have := hIR I hI; omega
    have! h2 : ((I.1 - A.R.1) / (S.K : ℤ)).toNat ≤ (I.1 - A.R.1).toNat :=
      Int.toNat_le_toNat (Int.ediv_le_self _ h0)
    omega
  have! hIB : ∀ I ∈ A.cells, A.blkStart S.K I.1 ∈ (Finset.range (A.treeDepth + 1)).image
      (fun β : ℕ => A.R.1 + ((S.K * β : ℕ) : ℤ)) := fun I hI =>
    FamParams.blkStart_mem_blocks (A := A) hK1 (hIR I hI) (hbk I hI)
  -- the main and helper tests of the leaf on the extended catalogs
  have! hpassD : ∀ I ∈ S1, ∀ l, D.u ≠ some l → ∀ w : fp.TestName I Unit, fp.MainRk w →
      (fp.testOf l I (fun _ => bf.basicIn fp.Mc l I) w).Pass A.G (bf.origCols l) I A.csrc
        A.Hsrc bf.vtag (A.w I) (catThreshold A.famVtxBound AD.τ₃ AD.n
          (fp.testOf l I (fun _ => bf.basicIn fp.Mc l I) w).r) fp.mH (D.cat l) := by
    intro I hI l hl w hw
    have! h := hmp ⟨⟨l, ⟨I, hS0T (hS1S0 hI)⟩, w⟩, hw⟩
    have! e : bf.patIn fp.Mc p I l = bf.basicIn fp.Mc l I := bf.patIn_of_ne fp.Mc p I hl
    simp only [main, e] at h
    exact h
  have! hhpassD : ∀ I ∈ S1, ∀ a, ∀ w : fp.HelperName I (Fin A.famVtxBound),
      (fp.helperOf a I (fun i => (D.toLeafQ qG).sv a (gE I i) I) w).Pass A.G (bf.origCols a) I
        A.csrc A.Hsrc bf.vtag (A.w I)
        (catThreshold A.famVtxBound AD.τ₃ AD.n (fp.Lc + 5)) fp.mH (D.cat a) :=
    fun I hI a w => D₀.hhpass_appendCat hcat mb' hanc hrankH hroleD qG gE (hS1c hI) a w
      (hhp a I (hS0T (hS1S0 hI)) w)
  have! hn_pos : ∀ r, 0 < AD.n r := fun r =>
    lt_of_lt_of_le (by linarith only [hcb]) (AD.hn0.trans (hn_mono (Nat.zero_le r)))
  have! hVcb : A.colBudget ≤ (A.famVtxBound : ℝ) := by
    unfold ActiveSetup.famVtxBound
    have! h1 := Nat.lt_floor_add_one (8 * A.colBudget)
    push_cast
    linarith only [h1, hcb]
  have! hτr : ∀ R, 1 ≤ R → R ≤ fp.Lc + 4 → catThreshold A.famVtxBound AD.τ₃ AD.n R *
      (A.colBudget * Real.sqrt (AD.n (R - 1))) ≤ AD.τ₃ := fun R _ _ =>
    catThreshold_mul_le AD.n R AD.hτ₃.le (lt_of_lt_of_le two_pos hcb) hVcb (hn_pos _)
  have! hτH' : catThreshold A.famVtxBound AD.τ₃ AD.n (fp.Lc + 5) *
      (A.colBudget * Real.sqrt (AD.n (fp.Lc + 4))) ≤ AD.τ₃ :=
    catThreshold_mul_le AD.n (fp.Lc + 5) AD.hτ₃.le (lt_of_lt_of_le two_pos hcb) hVcb (hn_pos _)
  have! hτ0 : ∀ R, 0 ≤ catThreshold A.famVtxBound AD.τ₃ AD.n R := fun R => by
    unfold catThreshold
    exact div_nonneg AD.hτ₃.le (mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _))
  -- the label counts of the extended catalogs
  have! hNlD : ∀ I ∈ S1, ∀ l, ∀ r ≤ fp.Lc + 4, ∀ M : bf.Vtx → Prop,
      ((mainLabelsM A.G fp.Mc (bf.origCols l) (D.cat l) I r M d).card : ℝ) ≤ AD.n r := by
    intro I _ l r hr M
    have! h1 := mainLabelsM_subset (G := A.G) (Mc := fp.Mc) (O := bf.origCols l) (D.cat l) I r M d
    have! h2 : mainLabels A.G fp.Mc (bf.origCols l) (D.cat l) I r =
        mainLabels A.G fp.Mc (bf.origCols l) (AD.cat l) I r :=
      FamParams.mainLabels_append_highRank A.G fp.Mc (bf.origCols l) (AD.cat l)
        (hcat l) I r (fun e he => by rw [(hhT l e he).2.1]; show r < fp.Lc + 5; omega)
    refine le_trans (Nat.cast_le.mpr (Finset.card_le_card h1)) ?_
    rw [h2]
    exact AD.hlab l I r (by change r ≤ fp.Lc + 5; omega)
  expose_names
  exact @leaf_estimate_stage_4 κ c₀ cc hcc Dm0 Msch hMsch Cg hCg g cT cL cK cMc cm ce ce2 cQ CΛ eΛ
    CM1 t3 Cb Cl hconst A bf k η₀ E hanc hpairs hsub hS2 hη hη₀ hne q hq2 hq3 Nd hNd p AD d s δ ρ
    kD hδ hδ8 hρ hρ1 hkb hkF hk1 hstd hdδ hkB hcb hn_mono hNl0 hHm1 hdim hC S hSd hSDm hSV hd2 hdD
    hD2 hB2 hQ1 hbox hlogH hK hK1 hS0T hcu hlenMc Ms L hexp hnotg herrW hDS hsch' hA6 hqG1 Vl0
    hVl0 U hUdef hU4 hD0 hD1 hU16 hU0 MV hMV hMV0 ε hεdef hε0 hεU hUD hThrD hThrM hThrC hTsdef hτb
    hτb1 hτbN hHτb hroot' ρ₀ zc gsc hGz hMLE hPH hNl4 hNq hpathG hBσG hstar hLsl c hcrep hcB hVE
    Rr hRr Cut hCutl hTop hgE hcat hhT hTmpl hmbb hmbT hrankH hroleD htagH hS1S0 hS1c hbk hIB
    hpassD hhpassD hτr hτH' hτ0 hNlD



private theorem leaf_estimate_stage_2 : LeafEstimateStage2Statement := by
  classical
  intro κ c₀ cc hcc Dm0 Msch hMsch Cg hCg g cT cL cK cMc cm ce ce2 cQ CΛ eΛ CM1 t3 Cb Cl hconst A
    bf k η₀ E hanc hpairs hsub hS2 hη hη₀ hne q hq2 hq3 Nd hNd p AD d s δ ρ kD hδ hδ8 hρ hρ1 hkb
    hkF hk1 fp dB hstd hdδ Nl hkB hcb hn_mono hNl0 Hm hHm1 hdim hC S hSd hSDm hSQ hSV hSW hd2 hdD
    hD2 hB2 hQ1 hbox hlogH hK hK1 Lf hLf ks S0 hS0T hS0c gs gset hcu U_1 hlenMc mbs hNlab Ms L
    hexp hnotg herrW hDS hsch' hA6 qG hqG1 Vl0 hVl0 U hUdef hU4 hD0 hD1 hU16 hU0 MV hMV hMV0 ε
    hεdef hε0 hεU hUD hThr0 hThrD hThrM hThrC Ts hTsdef hTs0 BN τb hτb hτb1 hτbN hHτb hroot' ρ₀ zc
    gsc hGz hMLE hεM hδcG hcolG hPH
  have! hNl4 : (4 : ℝ) ≤ Nl := by
    have! this := (AD.hn0).trans (hn_mono (Nat.zero_le (fp.Lc + 5)))
    linarith only [this, hcb]
  have! hM1 : 1 ≤ ⌈Nl⌉₊ :=
    Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr (by linarith only [hNl4])).ne'
  have! hMD : (⌈Nl⌉₊ : ℝ) ≤ 2 * S.Dm := by
    rw [hSDm]
    have! h1 := (Nat.ceil_lt_add_one hNl0).le
    have! h2 : Nl ≤ max 2 Nl := le_max_right _ _
    have! h3 : 2 ≤ max 2 Nl := le_max_left _ _
    linarith only [h1, h2, h3]
  have! hBs : ∀ b ∈ (Finset.range (A.treeDepth + 1)).image
      (fun β : ℕ => A.R.1 + ((S.K * β : ℕ) : ℤ)), (S.K : ℤ) ∣ b - A.R.1 := by
    intro b hb
    obtain ⟨β, -, rfl⟩ := Finset.mem_image.mp hb
    refine ⟨β, ?_⟩
    push_cast
    ring
  have! hNq : ∀ l y, ((Finset.univ : Finset ({G // G ∈ gset} × (bf.Lab ⊕ Fin fp.Mc))).filter
      fun q => ∃ I ∈ A.cells, (∃ k', fp.Cert k' q.1.1 I) ∧ ∃ p : Fin fp.P,
        y ∈ dyadicGridCell A.G I.1 I.2 ∧
        q.2 ∈ mainLabelsM A.G fp.Mc (bf.origCols l) (AD.cat l) I (fp.brank (Lf.role l))
          (fp.bmask I q.1.1 (Lf.role l) (p + 1)) d).card ≤ BN :=
    leaf_estimate_hNq κ c₀ A bf q p AD d s hNl0 hlenMc hcolG hPH
  -- the per-group schedule facts on the subtype of the groups
  have! hdimG : ∀ l (G : {G // G ∈ gset}) q, (Ms l G.1).dvOf q + (Ms l G.1).zc.dim ≤ S.dmax :=
    fun l G q => by rw [hSd]; exact (hsch' l G.1 G.2).1 q
  have! hkeysG : ∀ l (G : {G // G ∈ gset}) (V : ℤ × ℤ),
      (((Ms l G.1).alive V).image (Ms l G.1).keyOf).card ≤ ⌈Nl⌉₊ := fun l G V =>
    Nat.cast_le.mp (((hsch' l G.1 G.2).2.2.2.2.2.2 V).trans (Nat.le_ceil _))
  have! hpathG : ∀ l y, (∑ G : {G // G ∈ gset}, ((Ms l G.1).ptSet y).card : ℝ) ≤ S.Dstar := by
    intro l y
    rw [hDS]
    have! h := fp.modes_path_le hanc (Lf.role_le l) kD gset (Ms l) (L l) (hexp l) hδ AD.hHed2 hHm1
      hδ hNl0 y
    refine le_of_eq_of_le ?_ h
    exact Finset.sum_coe_sort gset (fun G => (((Ms l G).ptSet y).card : ℝ))
  have! hQ0bd : (S.Q0 : ℝ) ≤ fp.Hed ^ (dB * dB) + 1 := by
    rw [hSQ]; exact fp.Q0bd_le dB AD.hHed2
  have! hBσG : ∀ l (G : {G // G ∈ gset}),
      2 * (S.Q0 * (3 * ((Ms l G.1).Bσ * (Ms l G.1).Bσ) ^ 2)) ^ 2 ≤ (⌊S.Dstar⌋₊ : ℝ) := by
    intro l G
    rw [hDS]
    exact FamParams.ModeExports.hBσ_le fp (Lf.role_le l) kD (hexp l G.1 G.2) hδ AD.hHed2 hHm1 hδ
      hNl0 (Nat.cast_nonneg _) hQ0bd
  have! hstar : fp.modeStar Dm0 dB Hm δ Nl kD ≤ S.Dstar := by
    rw [hDS]; exact (fp.le_modeStarG Dm0 dB kD hδ AD.hHed2 hHm1 hδ hNl0).2.1
  have! hCFD : 24 * (1 : ℝ) ≤ S.Dstar ^ 55 := by
    calc 24 * (1 : ℝ) ≤ 2 ^ 55 := by norm_num
      _ ≤ S.Dstar ^ 55 := pow_le_pow_left₀ (by norm_num) hD2 55
  have! hDmq : ∀ l, Real.log (2 * (mbs l).B) ≤ (k : ℝ) ^ cc := by
    intro l
    refine le_trans (Real.log_le_log (by
      change 0 < 2 * (8 * A.colBudget + Nl)
      linarith only [hcb, hNl0]) ?_) hkB
    change 2 * (8 * A.colBudget + Nl) ≤ 2 * (8 * A.colBudget + (1 + AD.Mp) * Nl)
    have! this : Nl ≤ (1 + AD.Mp) * Nl := le_mul_of_one_le_left hNl0 (by
      have! this : (0 : ℝ) ≤ AD.Mp := Nat.cast_nonneg _
      linarith only [this])
    linarith only [this]
  have! hLsl : ∀ l, ((Lf.layers l).length : ℝ) ≤ cc * (Real.log k + 1) := by
    intro l
    refine le_trans ?_ hkF
    have! h := leafAt_layers_length_le A.famFuel fp.Lc (A.basicSlot p) s l
    rw [← hLf] at h
    exact_mod_cast (show (Lf.layers l).length ≤ 2 * A.famFuel + 2 by omega)
  -- frozen families and first tops of every role
  have! htop := fun l : Fin 4 => fp.first_top_count_main l (AD.cat l)
    (fun e he => (AD.hT l e he).2.2) (AD.htag l) d (mbs l) hne hanc
    (ι := {G // G ∈ gset}) Subtype.val Subtype.val_injective ks hcolG (Lf.role_le l) (hPH l)
    (Lf.layers l) S hSV hA6 le_rfl le_rfl le_rfl (by norm_num) (by norm_num) hd2 hD2 hB2 hQ1
    (by rw [hSDm]; exact le_max_left _ _) hSW Dm0 dB AD.hHed2 hHm1 hδ hNl0 (hNlab l)
    (fun G => Ms l G.1) (fun G => qG G.1) (fun G => hqG1 G.1) (fun G => L l G.1) (gsc l) (hMLE l)
    (hεM l) (hdimG l) hM1 hMD (hkeysG l) (fun G => by rw [hδcG l G]; exact hδ)
    (fun G => (hsch' l G.1 G.2).2.1) (fp.Kstar Dm0 dB Hm δ Nl kD δ)
    (fun G => (hsch' l G.1 G.2).2.2.1) (fun G => (hsch' l G.1 G.2).2.2.2.1) hbox
    (fun G => (hsch' l G.1 G.2).2.2.2.2.1) (fun G => (hsch' l G.1 G.2).2.2.2.2.2.1) (hpathG l)
    (hBσG l) hstar zero_le_one hCFD (fun jb V hV => bf.normF l jb hV) A.R.1
    ((Finset.range (A.treeDepth + 1)).image (fun β : ℕ => A.R.1 + ((S.K * β : ℕ) : ℤ))) hBs
    hroot' hτb hτb1 hHτb (hNq l) hτbN cc hcc hk1 (hDmq l) hkb (hLsl l) Ts (dyThr ε U S.Dstar) hThrD
    hTs0 hThr0
    hρ hρ1
  choose c hcrep hcB hVE Rr hRr Cut hCutl hTop using htop
  -- the side input before the helper catalogs
  let cf : ∀ l G, ℤ → ℤ × ℤ → (Ms l G).Md → ℂ := fun l G =>
    if hG : G ∈ gset then c l ⟨G, hG⟩ else fun _ _ _ => 0
  let D₀ : fp.SideInput := ⟨AD.cat, mbs, Lf, A.uslot p, S, hA6, S.sideParams (1 / 1024), hK1,
    Fintype.card (bf.Lab ⊕ Fin fp.Mc), Ms, cf⟩
  -- an enumeration of the current groups of every cell by `famVtxBound` base names
  let gE : ℤ × ℤ → Fin A.famVtxBound → bf.Grp := fun I i =>
    if h : (i : ℕ) < (gs I).card then ((gs I).equivFin.symm ⟨i, h⟩).1 else default
  have! hgE : ∀ I, ∀ G ∈ gs I, ∃ i, gE I i = G := by
    intro I G hG
    have! hc := fp.card_groupsAt_le I ks
    refine ⟨⟨(gs I).equivFin ⟨G, hG⟩, lt_of_lt_of_le ((gs I).equivFin ⟨G, hG⟩).2 hc⟩, ?_⟩
    simp only [gE]
    rw [dite_eq_left ((gs I).equivFin ⟨G, hG⟩).2]
    simp
  -- the main tests of main rank of the attempt
  let Wm : Type := {x : Σ l : Fin 4, Σ I : AD.Tc, fp.TestName I.1 Unit // fp.MainRk x.2.2}
  let main : Wm → Fin 4 × (ℤ × ℤ) × MainTest bf.Vtx bf.Lab fp.Mc := fun x =>
    (x.1.1, x.1.2.1.1,
      fp.testOf x.1.1 x.1.2.1.1 (fun _ : Unit => bf.patIn fp.Mc p x.1.2.1.1 x.1.1) x.1.2.2)
  have! hmainR : ∀ i : Wm, (main i).2.2.r ≤ fp.Lc + 4 ∧
      ∀ l' < (main i).2.2.m, (main i).2.2.hr l' ≤ fp.Lc + 4 := by
    intro i
    refine ⟨i.2.1, fun l' hl' => ?_⟩
    change (if h : l' < i.1.2.2.2.2.1.1 then ((i.1.2.2.2.2.1.2 ⟨l', h⟩).1 : ℕ) else 0) ≤
      fp.Lc + 4
    split_ifs with h
    · exact i.2.2 _
    · exact Nat.zero_le _
  expose_names
  exact @leaf_estimate_stage_3 κ c₀ cc hcc Dm0 Msch hMsch Cg hCg g cT cL cK cMc cm ce ce2 cQ CΛ eΛ
    CM1 t3 Cb Cl hconst A bf k η₀ E hanc hpairs hsub hS2 hη hη₀ hne q hq2 hq3 Nd hNd p AD d s δ ρ
    kD hδ hδ8 hρ hρ1 hkb hkF hk1 hstd hdδ hkB hcb hn_mono hNl0 hHm1 hdim hC S hSd hSDm hSV hd2 hdD
    hD2 hB2 hQ1 hbox hlogH hK hK1 hS0T hS0c hcu hlenMc Ms L hexp hnotg herrW hDS hsch' hA6 hqG1
    Vl0 hVl0 U hUdef hU4 hD0 hD1 hU16 hU0 MV hMV hMV0 ε hεdef hε0 hεU hUD hThrD hThrM hThrC hTsdef
    hτb hτb1 hτbN hHτb hroot' ρ₀ zc gsc hGz hMLE hPH hNl4 hNq hpathG hBσG hstar hLsl c hcrep hcB
    hVE Rr hRr Cut hCutl hTop hgE hmainR



private theorem leaf_estimate_stage_1 : LeafEstimateStage1Statement := by
  classical
  intro κ c₀ cc hcc Dm0 hmodes Msch hMsch Cg hCg g cT cL cK cMc cm ce ce2 cQ CΛ eΛ CM1 t3 Cb Cl
    hconst A bf k η₀ E hanc hpairs hsub hS2 hη hη₀ hne q hq2 hq3 Nd hNd p AD d s δ ρ kD hδ hδ8 hρ
    hρ1 hkb hkF hk1 fp dB hstd hdδ Nl hkB hδN hcb hn_mono hNl0 Hm hHm1 hdim hC S hSd hSD hSDm hSQ
    hSV hSW hd2 hdD hD2 hB2 hQ1 hclr hbox hlogH hK hK1 Lf hLf ks S0 hS0T hS0c gs gset hcu hgsetU U
    hUuse hpathU hlenMc
  let mbs : (l : Fin (4 : ℕ)) → bf.MainBudget (AD.cat l) :=
    fun l => MainBudget.ofCounts bf fp.Mc (AD.cat l) (hlenMc l) l (fun e he => AD.hTc
      (AD.hT l e he).1) (fun e he => (AD.hT l e he).2.1) hNl0 (fun I _ => AD.hlab l I _
      le_rfl)
  intro hNlab
  have! hHs : A.Hsrc ≤ Hm := le_trans (le_max_left _ _) (le_max_left _ _)
  have! hdz : (dB : ℝ) ≤ Real.log Hm := by
    rw [Real.le_log_iff_exp_le (lt_of_lt_of_le one_pos hHm1)]
    exact le_trans (le_max_right _ _) (le_max_left _ _)
  have! hCz : ∀ (w : bf.Vtx) (l : Fin 4) i k',
      (chartRationalHeight ((((-slotCoeff l : ℤ) : ℚ) • (bf.vtag w).C) i k') : ℝ) ≤ Hm :=
    fun w l i k' => (bf.vtag_scaled_height_le w l i k').trans
      (le_trans (le_max_left _ _) (le_max_right _ _))
  have! hHδ : (dB : ℝ) * (bumpConst * 8 ^ 32 * (2 / δ)) ≤ Hm :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  have! hobt := hmodes A bf fp AD.cat (fun l e he => (AD.hT l e he).2.2)
    AD.htag mbs (fun l => Lf.role l) (fun l => Lf.layers l) d gset hgsetU hanc (K := S.K)
    (fun I => A.blkStart S.K I.1) (fun I => A.blkStart_bounds hK1 I.1) U hUuse hpathU AD.hHed2
    hdim hC hδ hδ8
    hdδ hHs hdz hCz hHδ hδ hNl0 zero_le_one hNlab hδN (fun l jb V hV => bf.normF l jb hV)
  obtain ⟨Ms, L, hexp, hnotg, herr⟩ := hobt
  clear hmodes
  have! herrW := PLift.up herr
  clear herr
  -- the schedule facts of the modes of the groups
  have hDS : S.Dstar = fp.modeStarG Dm0 dB Hm δ Nl kD δ := hSD
  have! hsch' : ∀ l, ∀ G ∈ gset,
      (∀ q, (Ms l G).dvOf q + (Ms l G).zc.dim ≤ 2 * dB + 2) ∧
      (Ms l G).Λ ≤ S.Dstar ∧ gaugeSqNorm (Ms l G).zc.dim (Ms l G).δc ≤ S.Dstar ∧
      2 * gaugeTail (Ms l G).zc.dim (Ms l G).δc / 2 ^ fp.Kstar Dm0 dB Hm δ Nl kD δ *
        S.Dstar ^ 300 ≤ 1 ∧
      (∀ m, S.Dstar⁻¹ ≤ (Ms l G).L.εM m) ∧
      (∀ V : ℤ × ℤ, (((Ms l G).alive V).card : ℝ) ≤ S.Dstar) ∧
      ∀ V : ℤ × ℤ, ((((Ms l G).alive V).image (Ms l G).keyOf).card : ℝ) ≤ Nl := by
    intro l G hG
    rw [hDS]
    exact FamParams.ModeExports.sched fp (Lf.role_le l) kD (hexp l G hG) hδ
      (le_trans hδ8 (by norm_num)) AD.hHed2
      hHm1 hδ hNl0 hdim (hNlab l)
  have! hA6 : 6 ≤ S.A0 := hSV.six_le_A0 (by norm_num) hd2 hD2 hB2
  -- the clearing integers of the group centers
  set! qG : bf.Grp → ℕ := fun G => clearInt (bf.vtag (bf.grpCenter d G)).C with hqG
  have! hqG1 : ∀ G, 1 ≤ qG G ∧ qG G ≤ S.Q0 := fun G => hclr _
  -- the linear-side energy bound, the side cap and the thresholds
  have! hobt : ∃ v : ℝ, v = 24 * (⌊180 * S.dmax * Real.log (2 * S.Dm) / (1 / 1024 : ℝ)⌋₊ +
      1) * (Real.exp ((6144 * (cc + 1) * (1024 * (cc + 1) + cc + 7) + 4) *
        (1 + Real.log (2 * (k : ℝ))) ^ 2) + 2 * 1 / S.Dstar ^ 394) := ⟨_, rfl⟩
  obtain ⟨Vl0, hVl0⟩ := hobt
  have! hobt : ∃ U : ℝ, U = max (2 * (A.colBudget + 2) * S.Dstar ^ 2)
      (Real.sqrt (TsideF A fp.P S.K
      (A.uslot p) (2 ^ A.famFuel) (2 * A.famFuel + 2) 1 E cc k (fun _ => Vl0) ρ)) := ⟨_, rfl⟩
  obtain ⟨U, hUdef⟩ := hobt
  have! hU4 : 2 * (A.colBudget + 2) * S.Dstar ^ 2 ≤ U := hUdef ▸ le_max_left _ _
  have! hD0 : (0 : ℝ) < S.Dstar := lt_of_lt_of_le two_pos hD2
  have! hD1 : (1 : ℝ) ≤ S.Dstar := le_trans one_le_two hD2
  have! hU16 : 16 ≤ U :=
    leaf_estimate_hU16 κ c₀ A hcb S hD2 U hU4
  have! hU0 : 0 < U := lt_of_lt_of_le (by norm_num) hU16
  have! hobt : ∃ x : ℝ, x = (AD.Mp : ℝ) * A.famVtxBound := ⟨_, rfl⟩
  obtain ⟨MV, hMV⟩ := hobt
  have! hMV0 : 0 ≤ MV :=
    leaf_estimate_hMV0 κ c₀ A bf p AD MV hMV
  have! hobt : ∃ ε : ℝ, ε = (U ^ 3 * S.Dstar ^ 5 * Real.exp k * (1 + MV))⁻¹ :=
    ⟨_, rfl⟩
  obtain ⟨ε, hεdef⟩ := hobt
  have! hε0 : 0 < ε :=
    leaf_estimate_hε0 k S hD2 U hU16 MV hMV0 ε hεdef
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
  have! hobt := dyThr_spec hε0 hεU hUD
  obtain ⟨hThr0, hThrD, hThrM, hThrC⟩ := hobt
  set! Ts : Finset (ℕ × ℕ) := Finset.range (Nat.log 2 ⌊S.Dstar⌋₊ + 1) ×ˢ
    Finset.range (Nat.log 2 ⌊S.Dstar⌋₊ + 1) with hTsdef
  have! hTs0 : Ts.Nonempty := ⟨(0, 0), Finset.mem_product.mpr
    ⟨Finset.mem_range.mpr (Nat.succ_pos _), Finset.mem_range.mpr (Nat.succ_pos _)⟩⟩
  -- the joint ball variation threshold
  set! BN : ℕ := ⌈8 * A.colBudget + Nl⌉₊ with hBN
  set! τb : ℝ := 1 / (1 + BN * A.colBudget ^ 2) with hτbdef
  have! hτb : 0 < τb :=
    leaf_estimate_hτb κ c₀ A bf p AD
  have! hτb1 : τb ≤ 1 :=
    leaf_estimate_hτb1 κ c₀ A bf p AD hτbdef
  have! hτbN : τb * BN * A.colBudget ^ 2 ≤ 1 :=
    leaf_estimate_hτbN κ c₀ A bf p AD hτbdef
  have! hHτb : Real.exp (A.Dg * (1 + Real.log A.Hsrc + Real.log τb⁻¹) ^ A.Dg) ≤ fp.Hed := by
    have! e : τb⁻¹ = 1 + (BN : ℝ) * A.colBudget ^ 2 := by rw [hτbdef, one_div, inv_inv]
    rw [e]
    exact AD.hHedτ'
  have! hroot' : ∀ I ∈ A.cells, dyadicGridCell A.G I.1 I.2 ⊆ Set.Icc
      (dyadicGridLeft A.G A.R.1 A.R.2)
      (dyadicGridLeft A.G A.R.1 A.R.2 + dyadicGridLength A.G A.R.1) :=
    fun I hI => (A.sub I hI).trans Set.Ico_subset_Icc_self
  -- the exports of the modes of the groups of the leaf
  have! hME : ∀ (l : Fin 4) (G : {G // G ∈ gset}), ∃ ρ₀ z g, G.1.2.1 = some (ρ₀, z, g) ∧ 0 ≤ g ∧
      fp.MainLiftExports l (AD.cat l) G.1 (Lf.role l) d Dm0 dB Hm g (L l G.1) (Ms l G.1).wave
        (Ms l G.1).cellOf ∧ (∀ m, (L l G.1).εM m = (Ms l G.1).L.εM m) ∧ (Ms l G.1).δc = δ := by
    intro l G
    obtain ⟨ρ₀, z, g, h1, h2, h3, h4, -, -, -, -, -, hδc', -⟩ := hexp l G.1 G.2
    exact ⟨ρ₀, z, g, h1, h2, h3, h4, hδc'⟩
  choose ρ₀ zc gsc hGz hgsc hMLE hεM hδcG using hME
  have! hcolG : ∀ G : {G // G ∈ gset}, G.1.1 = ks := by
    intro G
    obtain ⟨I, -, hG⟩ := Finset.mem_biUnion.mp G.2
    exact fp.groupsAt_color hG
  have! hPH : ∀ l, fp.bbase (Lf.role l) + fp.P ≤ fp.Hmax := fun l => by
    have! this := fp.bbase_le (Lf.role_le l) (le_refl fp.P)
    omega
  expose_names
  exact @leaf_estimate_stage_2 κ c₀ cc hcc Dm0 Msch hMsch Cg hCg g cT cL cK cMc cm ce ce2 cQ CΛ eΛ
    CM1 t3 Cb Cl hconst A bf k η₀ E hanc hpairs hsub hS2 hη hη₀ hne q hq2 hq3 Nd hNd p AD d s δ ρ
    kD hδ hδ8 hρ hρ1 hkb hkF hk1 hstd hdδ hkB hcb hn_mono hNl0 hHm1 hdim hC S hSd hSDm hSQ hSV hSW
    hd2 hdD hD2 hB2 hQ1 hbox hlogH hK hK1 hLf hS0T hS0c hcu hlenMc hNlab Ms L hexp hnotg herrW hDS
    hsch' hA6 hqG1 Vl0 hVl0 U hUdef hU4 hD0 hD1 hU16 hU0 MV hMV hMV0 ε hεdef hε0 hεU hUD hThr0
    hThrD hThrM hThrC hTsdef hTs0 hτb hτb1 hτbN hHτb hroot' ρ₀ zc gsc hGz hMLE hεM hδcG hcolG hPH


open Classical in
/-- Blueprint lines 2838-2851 on one leaf of the guarded search of an attempt (stages: schedule,
offsets and modes, frozen families and first tops, helper catalogs, leaf bound, and the explicit
form of `eq:before-absorption` on the leaf). For a degree `c` of the standing bounds there are `C`
and `K₀` such that, when `log` of the main counts and of the budget, `L + 6`, `H_max + 1`, `d_B`,
`log H_ed`, `log H_src`, `log max(H, padW)`, `E` and `ρ⁻¹` are at most `k^c` (resp. `(kP)^c`) and
`k^c ≤ k_D`, `log δ⁻¹ ≤ k_D`, the weighted minima of the leaf over the test cells outside the
failure roots and six cut families of root length at most `2ρ|R|` are at most
`C u^C G^C (η^{1/1200} + η₀ + (P+1)² τ₃ + e^{C k^c} (√δ + e^{-k_D})) |R| + C e^{-k} |R|`
plus the near-band term `C (1 + C_N) C_q (C u^C + 2)^{2(q-2)/(q-1)} (2 + log(C u^C + 2))⁶ G^C
P^{-1/2} |R|`, where `u = k_D P`, `G = exp((1 + log 2k)²)` and `k_D` is the accuracy of the
enlarged budget. -/
theorem leaf_estimate (κ : LocalKernelClass) (c₀ cc : ℕ) (hcc : 1 ≤ cc) :
    ∃ Cl : ℕ, ∃ K₀ : ℝ, 1 ≤ Cl ∧ 2 ≤ K₀ ∧
    ∀ {A : ActiveSetup κ c₀} (bf : A.BasicFamilies) (k : ℕ) {η₀ E : ℝ}, A.AncClosed →
      (∀ I ∈ A.cells, ∀ s s', s ≠ s' → PairSmall (dyadicGridLeft A.G I.1 I.2)
        (dyadicGridLength A.G I.1) (A.w I) s s' (A.Y I s) (A.Y I s') (2 * η₀)) →
      A.SubRootProps η₀ E → A.S = 2 → A.η = 4 * η₀ → 0 < η₀ →
      A.cells.Nonempty → ∀ {q : ℝ} (hq2 : 2 < q) (hq3 : q < 3) {Nd : ℕ}, A.DepthWin Nd →
      ∀ (p : Fin 3) (AD : bf.AttemptData p)
      (_ : bf.Vtx) (s : ℕ) {δ ρ kD : ℝ}, 0 < δ → δ ≤ 1 / 8 → 8 * A.dBnd * δ ≤ 1 →
      δ ^ 2 * AD.n (AD.fp.Lc + 5) * A.colBudget ^ 2 ≤ 1 → 0 < ρ → ρ < 1 → K₀ ≤ k →
      (k : ℝ) ^ cc ≤ kD →
      Real.log (2 * (8 * A.colBudget + (1 + AD.Mp) * AD.n (AD.fp.Lc + 5))) ≤ (k : ℝ) ^ cc →
      Real.log (2 * A.colBudget) ≤ (k : ℝ) ^ cc →
      ((2 * A.famFuel + 2 : ℕ) : ℝ) ≤ cc * (Real.log k + 1) →
      (AD.fp.Lc : ℝ) + 6 ≤ (k : ℝ) ^ cc → (AD.fp.Hmax : ℝ) + 1 ≤ ((k : ℝ) * AD.fp.P) ^ cc →
      (A.dBnd : ℝ) ≤ (k : ℝ) ^ cc → Real.log AD.fp.Hed ≤ (k : ℝ) ^ cc →
      Real.log A.Hsrc ≤ (k : ℝ) ^ cc → Real.log (max A.H ActiveSetup.padW) ≤ (k : ℝ) ^ cc →
      δ⁻¹ ≤ Real.exp kD → E ≤ (k : ℝ) ^ cc → ρ⁻¹ ≤ (k : ℝ) ^ cc →
      ∃ F : Fin 6 → Finset (ℤ × ℤ),
        (∀ i, ∀ c ∈ F i, dyadicGridCell A.G c.1 c.2 ⊆ dyadicGridCell A.G A.R.1 A.R.2) ∧
        (∀ i, dyadicRootLength A.G (F i) ≤ 2 * ρ * dyadicGridLength A.G A.R.1) ∧
        ∀ cs ⊆ AD.Tc, (∀ I ∈ cs, ¬ ∃ c ∈ AD.fp.failRoots,
          dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G c.1 c.2) →
          (∀ I ∈ cs, ∀ i, ∀ e ∈ F i, ¬ dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G e.1 e.2) →
          ∑ I ∈ cs, dyadicGridLength A.G I.1 * min A.η ‖∑ G ∈ AD.fp.groupsAt I
              (leafAt A.famFuel AD.fp.Lc (A.basicSlot p) s).k,
            AD.fp.Λc I (fun l => AD.fp.ballFilt l (AD.cat l) I G
              ((leafAt A.famFuel AD.fp.Lc (A.basicSlot p) s).role l)
              (AD.fp.inputL AD.cat I (bf.patIn AD.fp.Mc p I)
                (leafAt A.famFuel AD.fp.Lc (A.basicSlot p) s).layers l))‖ ≤
            leafBnd Cl kD AD.fp.P k cc A.η η₀ AD.τ₃ δ (finiteDepthConstant κ q Nd)
              (nbCM κ hq2 hq3 + nbCUM κ hq2 hq3) q (dyadicGridLength A.G A.R.1) := by
  have! hobt := exists_leaf_modes κ c₀
  obtain ⟨Dm0, hDm0, hmodes⟩ := hobt
  have! hobt := FamParams.exists_leaf_schedule 340 5 4 600
    (δs := 1 / 1024) (by norm_num) (by norm_num)
  obtain ⟨Msch, hMsch, hsch⟩ := hobt
  have! hobt := log_modeStarG_poly (cc + 6) Dm0
  obtain ⟨Cg, hCg⟩ := hobt
  -- the constants of the explicit bound (packed, so that `linarith` does not see them)
  have! hobt :
      ∃ (g : ℕ) (cT cL cK cMc cm ce ce2 cQ : ℝ) (CΛ eΛ CM1 t3 Cb Cl : ℕ),
      g = 8192 * (cc + 1) * (1024 * (cc + 1) + cc + 7) + cc ^ 2 + 8 ∧
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
      Cl = ⌈cm * Cb ^ 59 + ce * Cb ^ 18 + ce2 + 3 * 10 ^ 11 * cQ⌉₊ + 59 * Cb + 4 * g + 8 * cc + 8 :=
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
      rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨g, cT, cL, cK, cMc, cm, ce, ce2, cQ, CΛ, eΛ, CM1, t3, Cb, Cl, hconst⟩ := hobt
  have! hCl1 : 1 ≤ Cl := by rw [hconst.2.2.2.2.2.2.2.2.2.2.2.2.2.2]; omega
  have! hlb := Real.log_nonneg one_le_bumpConst
  refine ⟨Cl, 2 + Real.log bumpConst + 100, hCl1, by linarith only [hlb], ?_⟩
  intro A bf k η₀ E hanc hpairs hsub hS2 hη hη₀ hne q hq2 hq3 Nd hNd p AD d s δ ρ kD hδ hδ8 hdδ
    hδN hρ hρ1 hK0k hkD hkB hkb hkF hLck hHmk hdBk hHedk hHsk hHWk hδk hEk hρk
  have! hk2 : (2 : ℝ) ≤ k := le_trans (by linarith only [hlb]) hK0k
  have! hk1 : (1 : ℝ) ≤ k := by linarith only [hk2]
  -- the standing bounds of the explicit form (packed until they are used)
  have! hstd := And.intro hLck <| And.intro hHmk <| And.intro hdBk <| And.intro hHedk <|
    And.intro hHsk <| And.intro hHWk <| And.intro hδk <| And.intro hEk <| And.intro hρk <|
      And.intro hK0k <| And.intro hkD <| And.intro hk2 hlb
  clear hLck hHmk hdBk hHedk hHsk hHWk hδk hEk hρk hK0k hkD hk2 hlb
  set! fp := AD.fp with hfp
  rewrite [← hfp] at hδN hkB hstd ⊢
  set! dB := A.dBnd with hdB
  rewrite [← hdB] at hdδ hstd
  set! Nl : ℝ := AD.n (fp.Lc + 5) with hNl
  rewrite [← hNl] at hδN hkB
  have hcb := A.two_le_colBudget
  have! hn_mono : Monotone AD.n :=
    leaf_estimate_hn_mono κ c₀ A bf p AD hcb
  have! hNl0 : 0 ≤ Nl :=
    le_trans (by linarith only [hcb]) ((AD.hn0).trans (hn_mono (Nat.zero_le _)))
  -- the mode height
  set! Hm : ℝ := max (max A.Hsrc (Real.exp dB)) (max (5832 * max A.H ActiveSetup.padW ^ 4)
    (dB * (bumpConst * 8 ^ 32 * (2 / δ)))) with hHm
  have! hHm1 : 1 ≤ Hm :=
    le_trans (Real.one_le_exp (Nat.cast_nonneg _)) (le_trans (le_max_right _ _) (le_max_left _ _))
  have hdim : ∀ w : bf.Vtx, (bf.vtag w).dim ≤ dB := bf.vtag_dim_le
  have! hC : ∀ (w : bf.Vtx) a c, (rationalHeight ((bf.vtag w).C a c) : ℝ) ≤ fp.Hed :=
    fun w a c => (bf.vtag_height_le w a c).trans AD.hHedV
  -- the schedule
  have! hS := hsch fp Dm0 dB (H := Hm) (δc := δ) (N := Nl) kD (δ := δ) (Dm := max 2 Nl) hδ
    AD.hHed2 hHm1 hδ hNl0 (le_max_left _ _) hdim hC
  dsimp only at hS
  obtain ⟨S, hSd, hSD, hSB, hSDm, hSQ, hSV, hSW, hd2, hdD, hD2, hB2, hQ1, hQD, hclr, hbox, hlogH,
    hlogT, hK⟩ := hS
  clear hsch
  have! hK1 : 1 ≤ S.K := by
    obtain ⟨κ', hκ'⟩ := hSV.K_dyadic
    rw [hκ']
    exact Nat.one_le_two_pow
  -- the leaf, its groups and their uses on the test cells below no failure root
  set! Lf := leafAt A.famFuel fp.Lc (A.basicSlot p) s with hLf
  rewrite [← hLf] at ⊢
  set! ks := Lf.k with hks
  rewrite [← hks] at ⊢
  set! S0 := AD.Tc.filter fun I => ¬ ∃ c ∈ fp.failRoots,
    dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G c.1 c.2 with hS0
  have! hS0T : S0 ⊆ AD.Tc := Finset.filter_subset _ _
  have! hS0c : S0 ⊆ A.cells := hS0T.trans AD.hTc
  have! hsucc : ∀ I ∈ S0, ∀ w ∈ bf.admT.X (bf.admAt I),
      fp.K.Success (fp.K.colorData (bf.admT.st (bf.admAt I)) w) := fun I hI =>
    (fp.failure_cut AD.hcol).2.2.2 I (hS0c hI) (Finset.mem_filter.mp hI).2
  set! gs : ℤ × ℤ → Finset bf.Grp := fun I => fp.groupsAt I ks with hgs
  set! gset := S0.biUnion gs with hgset
  have! hcu : ∀ I ∈ S0, ∀ G ∈ gs I, fp.Cert ks G I ∧ fp.ActualUse G I :=
    fun I hI G hG => fp.groupsAt_cert_use (hS0c hI) hG (hsucc I hI)
  have! hgsetU : ∀ G ∈ gset, ∃ I, fp.ActualUse G I := by
    intro G hG
    obtain ⟨I, hI, hGI⟩ := Finset.mem_biUnion.mp hG
    exact ⟨I, (hcu I hI G hGI).2⟩
  set! U : Fin 4 → bf.Grp → Finset (ℤ × ℤ) := fun _ G => S0.filter fun I => G ∈ gs I with hU
  have! hUuse : ∀ l G, ∀ I ∈ U l G, fp.ActualUse G I := by
    intro l G I hI
    obtain ⟨hI0, hGI⟩ := Finset.mem_filter.mp hI
    exact (hcu I hI0 G hGI).2
  have! hpathU : ∀ y, ∑ l, ∑ G ∈ gset, ((U l G).filter fun I : ℤ × ℤ =>
      y ∈ dyadicGridCell A.G I.1 I.2).card ≤ 4 * (AD.Mp * A.famVtxBound) :=
    leaf_estimate_hpathU κ c₀ A bf p AD s hS0T hU
  -- the main budgets of the main catalogs
  have! hlenMc : ∀ l, (AD.cat l).length ≤ fp.Mc := fun l => by
    have! h1 := AD.hlen l
    have h2 : fp.Mc = AD.Tc.card * AD.Tmax + AD.Tc.card * AD.Tmax := AD.hMc
    omega
  let mbs : ∀ l, bf.MainBudget (AD.cat l) := fun l =>
    MainBudget.ofCounts bf fp.Mc (AD.cat l) (hlenMc l) l (fun e he => AD.hTc (AD.hT l e he).1)
      (fun e he => (AD.hT l e he).2.1) hNl0 (fun I _ => AD.hlab l I _ le_rfl)
  -- the offsets and fixed modes
  have! hNlab : ∀ l, ∀ I ∈ A.cells, ((mainLabels A.G fp.Mc (bf.origCols l) (AD.cat l) I
      (fp.brank (Lf.role l))).card : ℝ) ≤ Nl := by
    intro l I _
    have! hr : fp.brank (Lf.role l) ≤ fp.Lc + 5 := by
      have! this := Lf.role_le l
      unfold FamParams.brank; omega
    exact (AD.hlab l I _ hr).trans (hn_mono hr)
  expose_names
  exact @leaf_estimate_stage_1 κ c₀ cc hcc Dm0 hmodes Msch hMsch Cg hCg g cT cL cK cMc cm ce ce2
    cQ CΛ eΛ CM1 t3 Cb Cl hconst A bf k η₀ E hanc hpairs hsub hS2 hη hη₀ hne q hq2 hq3 Nd hNd p AD
    d s δ ρ kD hδ hδ8 hρ hρ1 hkb hkF hk1 hstd hdδ hkB hδN hcb hn_mono hNl0 hHm1 hdim hC S hSd hSD
    hSDm hSQ hSV hSW hd2 hdD hD2 hB2 hQ1 hclr hbox hlogH hK hK1 hLf hS0T hS0c hcu hgsetU hUuse
    hpathU hlenMc hNlab

end ActiveSetup.BasicFamilies

end TrilinearHT.Auto

end
