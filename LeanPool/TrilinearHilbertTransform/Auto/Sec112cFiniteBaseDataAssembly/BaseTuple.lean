/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

/- Adapted for Lean Pool from roos-j/lean-trilinearht at
7b4209609e6a7fb9d9935973ee8541495f943660. Imports, names, proof organization and
Mathlib interfaces have been updated; original authorship is retained above. -/

public import LeanPool.TrilinearHilbertTransform.Auto.Sec112cFiniteBaseDataAssembly.BaseBottom

/-!
# Trilinear Hilbert transform: baseTuple
-/

@[expose] public section

section
namespace TrilinearHT.Auto
open MeasureTheory Metric
open scoped FourierTransform ComplexConjugate ENNReal

open scoped Classical in
private def BaseTupleHbpackStatement : Prop :=
  ∀ (κ : LocalKernelClass)
    (c₂ : ℕ)
    (cp : ℕ)
    (Wp : ℝ)
    (c₁ : ℕ)
    (C₁ : ℕ)
    (c₂a : ℕ)
    (Ca : ℕ)
    (Cqa : ℝ)
    (G : RealDyadicGrid)
    (J : ℤ × ℤ)
    (N : ℕ)
    (w : ℤ × ℤ → ℝ × ℝ → ℂ)
    (f : Fin (4 : ℕ) → ℝ → ℂ)
    (Bf : ℕ → ℝ)
    (seg : ℕ → ℤ × ℤ → ℤ × ℤ)
    (u : ℕ)
    (t : ℕ)
    (hut : u < t)
    (Hc : ℝ)
    (η₀ : ℝ)
    (Bp : ℝ)
    (ε : ℝ)
    (K₀ : ℕ)
    (ka : ℕ)
    (kb : ℕ),
  let H : ℝ :=
    max Hc Wp ^ (6 : ℕ)
  let D : ℝ :=
    max H (Real.exp ((↑C₁ : ℝ) * ((1 : ℝ) + Bp + Real.log H) ^ C₁))
  let i : Fin (4 : ℕ) :=
    stagPos u
  let k : Fin (4 : ℕ) :=
    stagPos t
  ∀ (sa : Fin (4 : ℕ))
    (sb : Fin (4 : ℕ)),
  let la : ℕ :=
    StaggerCell.lastLevel sa t
  ∀ (hla2 : la < t),
  let lb : ℕ :=
    StaggerCell.lastLevel sb t
  ∀ (hlb2 : lb < t),
  let Lset : Finset ℕ :=
    {u, u - (4 : ℕ), t, t - (4 : ℕ), la, lb}
  ∀ (hLne : Lset.Nonempty),
  let Rf : ℤ × ℤ → ℤ × ℤ :=
    firstRoot seg Lset hLne
  ∀ (hHl : ∀ ℓ ≤ t, max (Bf ℓ) Wp ^ (6 : ℕ) ≤ H)
    (X : (ℓ : ℕ) → (R : ℤ × ℤ) → R ∈ dyadicFiniteTree G J N → LowList G J N R (max c₂ cp)
      (max (Bf ℓ) Wp ^ (6 : ℕ))),
  let Y : (ℓ : ℕ) → ℓ ≤ t → (R : ℤ × ℤ) → R ∈ dyadicFiniteTree G J N → LowList G J N R (max c₂
      cp) H :=
    fun ℓ hℓ R hR => (X ℓ R hR).mono le_rfl (hHl ℓ hℓ)
  ∀ (hu4 : u - (4 : ℕ) ≤ t)
    (ht4 : t - (4 : ℕ) ≤ t),
  let Xi : (R : ℤ × ℤ) → R ∈ dyadicFiniteTree G J N → LowList G J N R (max c₂ cp) H :=
    fun R hR => if u ≤ 4 then Y u hut.le R hR else (Y u hut.le R hR).sub (Y (u - 4) hu4
      R hR)
  let Xk : (R : ℤ × ℤ) → R ∈ dyadicFiniteTree G J N → LowList G J N R (max c₂ cp) H :=
    fun R hR => if t ≤ 4 then Y t le_rfl R hR else (Y t le_rfl R hR).sub (Y (t - 4) ht4
      R hR)
  let Xga : (R : ℤ × ℤ) → R ∈ dyadicFiniteTree G J N → LowList G J N R (max c₂ cp) H :=
    fun R hR => if 1 ≤ la then Y la hla2.le R hR else LowList.empty
  let Xgb : (R : ℤ × ℤ) → R ∈ dyadicFiniteTree G J N → LowList G J N R (max c₂ cp) H :=
    fun R hR => if 1 ≤ lb then Y lb hlb2.le R hR else LowList.empty
  ∀ (_ : ∀ (T : Finset (ℤ × ℤ)), (∀ I ∈ T, I ∈ dyadicFiniteTree G J N) → ∑ R ∈ Finset.image
      Rf T, dyadicGridLength G R.1 ≤ (8 : ℝ) * dyadicGridLength G J.1),
  let d₀ : ℤ :=
    J.1 + (↑N : ℤ) + (1 : ℤ) - (↑K₀ : ℤ)
  let Bot : Finset (ℤ × ℤ) :=
    {I ∈ dyadicFiniteTree G J N | ¬I.1 + (↑K₀ : ℤ) ≤ J.1 + (↑N : ℤ) ∧ kernelHull G J N w
      I}
  ∀ (_ : ∀ I ∈ Bot, I ∈ dyadicFiniteTree G J N ∧ d₀ ≤ I.1 ∧ kernelHull G J N w I),
  let anc : ℤ × ℤ → ℤ × ℤ :=
    fun I => if h : d₀ ≤ I.1 then (d₀, Classical.choose (dyadicGridCell_ancestor G h
      I.2)) else I
  ∀ (_ : ∀ (I : ℤ × ℤ), d₀ ≤ I.1 → (anc I).1 = d₀ ∧ dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell
      G (anc I).1 (anc I).2),
  let Rb : ℤ × ℤ → ℤ × ℤ :=
    fun (I : ℤ × ℤ) => if d₀ ≤ (Rf I).1 then Rf I else anc I
  ∀ (_ : ∀ I ∈ dyadicFiniteTree G J N, d₀ ≤ I.1 → Rb I ∈ dyadicFiniteTree G J N ∧ d₀ ≤ (Rb
      I).1 ∧ dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G (Rb I).1 (Rb I).2 ∧
      dyadicGridCell G (Rb I).1 (Rb I).2 ⊆ dyadicGridCell G (Rf I).1 (Rf I).2),
  let Bs : Finset (ℤ × ℤ) :=
    Finset.image Rb Bot
  ∀ (hQ : ∀ R' ∈ Bs, Rf R' ∈ dyadicFiniteTree G J N)
    (AB : (R' : ℤ × ℤ) → R' ∈ Bs → ActiveSetup κ (max (max c₁ (max c₂ cp)) c₂a))
    (_ : ∀ (R' : ℤ × ℤ) (hR' : R' ∈ Bs), (AB R' hR').G = G ∧ (AB R' hR').R = R' ∧ (AB R'
      hR').cells = {I ∈ Bot | Rb I = R'} ∧ (AB R' hR').w = w ∧ (AB R' hR').a = sa ∧ (AB
      R' hR').b = sb ∧ (AB R' hR').H = max D (max (fitBudget Cqa Ca ka) (fitBudget Cqa
      Ca kb)) ∧ (AB R' hR').Dc = √ε⁻¹ ∧ (AB R' hR').S = (2 : ℝ) ∧ (AB R' hR').η = (4 :
      ℝ) * η₀ ∧ Fintype.card (AB R' hR').L = Fintype.card ((Xi (Rf R') (hQ R'
      hR')).reroot (hQ R' hR')).Λ + Fintype.card ((Xk (Rf R') (hQ R' hR')).reroot (hQ R'
      hR')).Λ + Fintype.card ((Xga (Rf R') (hQ R' hR')).reroot (hQ R' hR')).Λ +
      Fintype.card ((Xgb (Rf R') (hQ R' hR')).reroot (hQ R' hR')).Λ ∧ (∀ I ∈ {I ∈ Bot |
      Rb I = R'}, (AB R' hR').Y I = slots4 sa i k (f sa - ((Xga (Rf R') (hQ R'
      hR')).reroot (hQ R' hR')).val I) (((Xi (Rf R') (hQ R' hR')).reroot (hQ R'
      hR')).val I) (((Xk (Rf R') (hQ R' hR')).reroot (hQ R' hR')).val I) (f sb - ((Xgb
      (Rf R') (hQ R' hR')).reroot (hQ R' hR')).val I)) ∧ (∀ I ∈ {I ∈ Bot | Rb I = R'}, ∀
      (s s' : Fin (4 : ℕ)), s ≠ s' → PairSmall (dyadicGridLeft G I.1 I.2)
      (dyadicGridLength G I.1) (w I) s s' ((AB R' hR').Y I s) ((AB R' hR').Y I s') η₀) ∧
      (∀ I ∈ {I ∈ Bot | Rb I = R'}, ∀ (l : Fin (4 : ℕ)), (eLpNorm ((AB R' hR').Y I l) (2
      : ℝ≥0∞) ((AB R' hR').μ I)).toReal ≤ (2 : ℝ)) ∧ (∀ (l : Fin (4 : ℕ)), ∑ I ∈ Bot
      with Rb I = R', dyadicGridLength G I.1 * (eLpNorm ((AB R' hR').U l I) (2 : ℝ≥0∞)
      ((AB R' hR').μ I)).toReal ^ (2 : ℕ) ≤ (↑K₀ : ℝ) ^ (2 : ℕ) * dyadicGridLength G
      R'.1) ∧ ∑ I ∈ Bot with Rb I = R', dyadicGridLength G I.1 * ‖(AB R' hR').Hf I ((AB
      R' hR').z (3 : Fin (4 : ℕ)) I)‖ ≤ η₀ * ((↑K₀ : ℝ) ^ (2 : ℕ) * dyadicGridLength G
      R'.1) ∧ (AB R' hR').HasColumnRep (1 : ℝ) ∧ (AB R' hR').SubRootProps η₀ ((↑K₀ : ℝ)
      ^ (2 : ℕ))),
  ∑ R' : ↥Bs, dyadicGridLength G (AB (↑R' : ℤ × ℤ) R'.property).R.1 ≤ (9 : ℝ) *
    dyadicGridLength G J.1

open scoped Classical in
private def BaseTupleHcardsStatement : Prop :=
  ∀ (c₂ : ℕ)
    (cp : ℕ)
    (Wp : ℝ)
    (C₁ : ℕ)
    (G : RealDyadicGrid)
    (J : ℤ × ℤ)
    (N : ℕ)
    (Bf : ℕ → ℝ)
    (M : ℕ → ℕ)
    (u : ℕ)
    (t : ℕ)
    (hut : u < t)
    (Hc : ℝ)
    (Mt : ℕ)
    (_ : ∀ ℓ ≤ t, M ℓ ≤ Mt)
    (Bp : ℝ)
    (Ma : ℕ)
    (Mb : ℕ),
  let H : ℝ :=
    max Hc Wp ^ (6 : ℕ)
  let D : ℝ :=
    max H (Real.exp ((↑C₁ : ℝ) * ((1 : ℝ) + Bp + Real.log H) ^ C₁))
  let Wa : ℕ :=
    (2 : ℕ) * Mt * ((2 : ℕ) * Mt) * ⌊D⌋₊ + Ma
  let Wb : ℕ :=
    (2 : ℕ) * Mt * ((2 : ℕ) * Mt) * ⌊D⌋₊ + Mb
  ∀ (sa : Fin (4 : ℕ))
    (sb : Fin (4 : ℕ)),
  let la : ℕ :=
    StaggerCell.lastLevel sa t
  ∀ (hla2 : la < t),
  let lb : ℕ :=
    StaggerCell.lastLevel sb t
  ∀ (hlb2 : lb < t)
    (hHl : ∀ ℓ ≤ t, max (Bf ℓ) Wp ^ (6 : ℕ) ≤ H)
    (X : (ℓ : ℕ) → (R : ℤ × ℤ) → R ∈ dyadicFiniteTree G J N → LowList G J N R (max c₂ cp)
      (max (Bf ℓ) Wp ^ (6 : ℕ))),
  let Y : (ℓ : ℕ) → ℓ ≤ t → (R : ℤ × ℤ) → R ∈ dyadicFiniteTree G J N → LowList G J N R (max c₂
      cp) H :=
    fun ℓ hℓ R hR => (X ℓ R hR).mono le_rfl (hHl ℓ hℓ)
  ∀ (_ : ∀ (ℓ : ℕ) (hℓ : ℓ ≤ t) (R : ℤ × ℤ) (hR : R ∈ dyadicFiniteTree G J N), Fintype.card
      (Y ℓ hℓ R hR).Λ = M ℓ)
    (hu4 : u - (4 : ℕ) ≤ t)
    (ht4 : t - (4 : ℕ) ≤ t),
  let Xi : (R : ℤ × ℤ) → R ∈ dyadicFiniteTree G J N → LowList G J N R (max c₂ cp) H :=
    fun R hR => if u ≤ 4 then Y u hut.le R hR else (Y u hut.le R hR).sub (Y (u - 4) hu4
      R hR)
  let Xk : (R : ℤ × ℤ) → R ∈ dyadicFiniteTree G J N → LowList G J N R (max c₂ cp) H :=
    fun R hR => if t ≤ 4 then Y t le_rfl R hR else (Y t le_rfl R hR).sub (Y (t - 4) ht4
      R hR)
  let Xga : (R : ℤ × ℤ) → R ∈ dyadicFiniteTree G J N → LowList G J N R (max c₂ cp) H :=
    fun R hR => if 1 ≤ la then Y la hla2.le R hR else LowList.empty
  let Xgb : (R : ℤ × ℤ) → R ∈ dyadicFiniteTree G J N → LowList G J N R (max c₂ cp) H :=
    fun R hR => if 1 ≤ lb then Y lb hlb2.le R hR else LowList.empty
  ∀ (R : ℤ × ℤ) (hRT : R ∈ dyadicFiniteTree G J N), Fintype.card (Xi R hRT).Λ ≤ (2 :
    ℕ) * Mt ∧ Fintype.card (Xk R hRT).Λ ≤ (2 : ℕ) * Mt ∧ Fintype.card (Xga R hRT).Λ ≤
    Mt ∧ Fintype.card (Xgb R hRT).Λ ≤ Mt ∧ Fintype.card (Xi R hRT).Λ * Fintype.card
    (Xk R hRT).Λ * ⌊D⌋₊ + Ma ≤ Wa ∧ Fintype.card (Xi R hRT).Λ * Fintype.card (Xk R
    hRT).Λ * ⌊D⌋₊ + Mb ≤ Wb

open scoped Classical in
private def BaseTupleHslotsStatement : Prop :=
  ∀ (c₂ : ℕ)
    (cp : ℕ)
    (Wp : ℝ)
    (G : RealDyadicGrid)
    (J : ℤ × ℤ)
    (N : ℕ)
    (w : ℤ × ℤ → ℝ × ℝ → ℂ)
    (f : Fin (4 : ℕ) → ℝ → ℂ)
    (Bf : ℕ → ℝ)
    (seg : ℕ → ℤ × ℤ → ℤ × ℤ)
    (g : ℕ → ℤ × ℤ → ℝ → ℂ)
    (u : ℕ)
    (t : ℕ)
    (hut : u < t)
    (Hc : ℝ),
  let H : ℝ :=
    max Hc Wp ^ (6 : ℕ)
  let i : Fin (4 : ℕ) :=
    stagPos u
  ∀ (_ : i = stagPos u),
  let k : Fin (4 : ℕ) :=
    stagPos t
  ∀ (_ : i ≠ k)
    (_ : k = stagPos t)
    (sa : Fin (4 : ℕ))
    (sb : Fin (4 : ℕ))
    (_ : sa ≠ sb)
    (_ : sa ≠ i)
    (_ : sa ≠ k)
    (_ : sb ≠ i)
    (_ : sb ≠ k),
  let la : ℕ :=
    StaggerCell.lastLevel sa t
  ∀ (hla2 : la < t)
    (_ : la = StaggerCell.lastLevel sa t),
  let lb : ℕ :=
    StaggerCell.lastLevel sb t
  ∀ (hlb2 : lb < t)
    (_ : lb = StaggerCell.lastLevel sb t),
  let Lset : Finset ℕ :=
    {u, u - (4 : ℕ), t, t - (4 : ℕ), la, lb}
  ∀ (hLne : Lset.Nonempty),
  let Rf : ℤ × ℤ → ℤ × ℤ :=
    firstRoot seg Lset hLne
  ∀ (hRtree : ∀ I ∈ dyadicFiniteTree G J N, Rf I ∈ dyadicFiniteTree G J N ∧ dyadicGridCell G I.1
      I.2 ⊆ dyadicGridCell G (Rf I).1 (Rf I).2)
    (hHl : ∀ ℓ ≤ t, max (Bf ℓ) Wp ^ (6 : ℕ) ≤ H)
    (X : (ℓ : ℕ) → (R : ℤ × ℤ) → R ∈ dyadicFiniteTree G J N → LowList G J N R (max c₂ cp)
      (max (Bf ℓ) Wp ^ (6 : ℕ))),
  let Y : (ℓ : ℕ) → ℓ ≤ t → (R : ℤ × ℤ) → R ∈ dyadicFiniteTree G J N → LowList G J N R (max c₂
      cp) H :=
    fun ℓ hℓ R hR => (X ℓ R hR).mono le_rfl (hHl ℓ hℓ)
  ∀ (_ : ∀ (ℓ : ℕ) (hℓ : ℓ ≤ t) (R : ℤ × ℤ) (hR : R ∈ dyadicFiniteTree G J N), ∀ I ∈
      dyadicFiniteTree G J N, dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G R.1 R.2 → seg
      ℓ I = seg ℓ R → kernelHull G J N w I → ∀ (y : ℝ), (Y ℓ hℓ R hR).val I y = g ℓ I y)
    (hu4 : u - (4 : ℕ) ≤ t)
    (ht4 : t - (4 : ℕ) ≤ t),
  let Xi : (R : ℤ × ℤ) → R ∈ dyadicFiniteTree G J N → LowList G J N R (max c₂ cp) H :=
    fun R hR => if u ≤ 4 then Y u hut.le R hR else (Y u hut.le R hR).sub (Y (u - 4) hu4
      R hR)
  let Xk : (R : ℤ × ℤ) → R ∈ dyadicFiniteTree G J N → LowList G J N R (max c₂ cp) H :=
    fun R hR => if t ≤ 4 then Y t le_rfl R hR else (Y t le_rfl R hR).sub (Y (t - 4) ht4
      R hR)
  let Xga : (R : ℤ × ℤ) → R ∈ dyadicFiniteTree G J N → LowList G J N R (max c₂ cp) H :=
    fun R hR => if 1 ≤ la then Y la hla2.le R hR else LowList.empty
  let Xgb : (R : ℤ × ℤ) → R ∈ dyadicFiniteTree G J N → LowList G J N R (max c₂ cp) H :=
    fun R hR => if 1 ≤ lb then Y lb hlb2.le R hR else LowList.empty
  ∀ (_ : u ∈ Lset)
    (_ : u - (4 : ℕ) ∈ Lset)
    (_ : t ∈ Lset)
    (_ : t - (4 : ℕ) ∈ Lset)
    (_ : la ∈ Lset)
    (_ : lb ∈ Lset)
    (_ : ∀ I ∈ dyadicFiniteTree G J N, ∀ ℓ ∈ Lset, seg ℓ I = seg ℓ (Rf I)),
  ∀ (I : ℤ × ℤ) (hI : I ∈ dyadicFiniteTree G J N), kernelHull G J N w I → slots4 sa i
    k (f sa - (Xga (Rf I) (hRtree I hI).left).val I) ((Xi (Rf I) (hRtree I
    hI).left).val I) ((Xk (Rf I) (hRtree I hI).left).val I) (f sb - (Xgb (Rf I)
    (hRtree I hI).left).val I) = stagTuple f g u t I

open scoped Classical in
private def BaseTupleConclusion39Statement : Prop :=
  ∀ (κ : LocalKernelClass)
    (c₂ : ℕ)
    (cp : ℕ)
    (Wp : ℝ)
    (c₁ : ℕ)
    (C₁ : ℕ)
    (c₂a : ℕ)
    (Ca : ℕ)
    (Cqa : ℝ)
    (G : RealDyadicGrid)
    (J : ℤ × ℤ)
    (N : ℕ)
    (w : ℤ × ℤ → ℝ × ℝ → ℂ)
    (f : Fin (4 : ℕ) → ℝ → ℂ)
    (Bf : ℕ → ℝ)
    (M : ℕ → ℕ)
    (seg : ℕ → ℤ × ℤ → ℤ × ℤ)
    (u : ℕ)
    (t : ℕ)
    (hut : u < t)
    (Hc : ℝ)
    (Mt : ℕ)
    (η₀ : ℝ)
    (Bp : ℝ)
    (ε : ℝ)
    (K₀ : ℕ)
    (ka : ℕ)
    (kb : ℕ)
    (Ma : ℕ)
    (Mb : ℕ)
    (_ : (0 : ℝ) < ε),
  let H : ℝ :=
    max Hc Wp ^ (6 : ℕ)
  let D : ℝ :=
    max H (Real.exp ((↑C₁ : ℝ) * ((1 : ℝ) + Bp + Real.log H) ^ C₁))
  let Wa : ℕ :=
    (2 : ℕ) * Mt * ((2 : ℕ) * Mt) * ⌊D⌋₊ + Ma
  let Wb : ℕ :=
    (2 : ℕ) * Mt * ((2 : ℕ) * Mt) * ⌊D⌋₊ + Mb
  let S₀ : ℝ :=
    (1 : ℝ) + (6 : ℝ) * (↑Mt : ℝ)
  let Sp : ℝ :=
    (↑Wa : ℝ) * √((2 : ℝ) ^ K₀ / ε) + (1 : ℝ)
  let i : Fin (4 : ℕ) :=
    stagPos u
  let k : Fin (4 : ℕ) :=
    stagPos t
  ∀ (sa : Fin (4 : ℕ))
    (sb : Fin (4 : ℕ)),
  let la : ℕ :=
    StaggerCell.lastLevel sa t
  ∀ (hla2 : la < t),
  let lb : ℕ :=
    StaggerCell.lastLevel sb t
  ∀ (hlb2 : lb < t),
  let Lset : Finset ℕ :=
    {u, u - (4 : ℕ), t, t - (4 : ℕ), la, lb}
  ∀ (hLne : Lset.Nonempty)
    (_ : SegData G J N seg Lset),
  let Rf : ℤ × ℤ → ℤ × ℤ :=
    firstRoot seg Lset hLne
  let Tup : Finset (ℤ × ℤ) :=
    {I ∈ dyadicFiniteTree G J N | I.1 + (↑K₀ : ℤ) ≤ J.1 + (↑N : ℤ) ∧ kernelHull G J N w
      I}
  let Rs : Finset (ℤ × ℤ) :=
    Finset.image Rf Tup
  ∀ (_ : ∀ I ∈ dyadicFiniteTree G J N, Rf I ∈ dyadicFiniteTree G J N ∧ dyadicGridCell G I.1
      I.2 ⊆ dyadicGridCell G (Rf I).1 (Rf I).2)
    (hRsT : ∀ R ∈ Rs, R ∈ dyadicFiniteTree G J N)
    (hHl : ∀ ℓ ≤ t, max (Bf ℓ) Wp ^ (6 : ℕ) ≤ H)
    (X : (ℓ : ℕ) → (R : ℤ × ℤ) → R ∈ dyadicFiniteTree G J N → LowList G J N R (max c₂ cp)
      (max (Bf ℓ) Wp ^ (6 : ℕ))),
  let Y : (ℓ : ℕ) → ℓ ≤ t → (R : ℤ × ℤ) → R ∈ dyadicFiniteTree G J N → LowList G J N R (max c₂
      cp) H :=
    fun ℓ hℓ R hR => (X ℓ R hR).mono le_rfl (hHl ℓ hℓ)
  ∀ (hu4 : u - (4 : ℕ) ≤ t)
    (ht4 : t - (4 : ℕ) ≤ t),
  let Xi : (R : ℤ × ℤ) → R ∈ dyadicFiniteTree G J N → LowList G J N R (max c₂ cp) H :=
    fun R hR => if u ≤ 4 then Y u hut.le R hR else (Y u hut.le R hR).sub (Y (u - 4) hu4
      R hR)
  let Xk : (R : ℤ × ℤ) → R ∈ dyadicFiniteTree G J N → LowList G J N R (max c₂ cp) H :=
    fun R hR => if t ≤ 4 then Y t le_rfl R hR else (Y t le_rfl R hR).sub (Y (t - 4) ht4
      R hR)
  let Xga : (R : ℤ × ℤ) → R ∈ dyadicFiniteTree G J N → LowList G J N R (max c₂ cp) H :=
    fun R hR => if 1 ≤ la then Y la hla2.le R hR else LowList.empty
  let Xgb : (R : ℤ × ℤ) → R ∈ dyadicFiniteTree G J N → LowList G J N R (max c₂ cp) H :=
    fun R hR => if 1 ≤ lb then Y lb hlb2.le R hR else LowList.empty
  ∀ (P : (R : ℤ × ℤ) → R ∈ Rs → Finset ((ℤ × ℤ) × ℤ × ℤ))
    (A : (R : ℤ × ℤ) → (hR : R ∈ Rs) → ↥(P R hR) → ActiveSetup κ (max (max c₁ (max c₂ cp))
      c₂a))
    (_ : ∀ (R : ℤ × ℤ) (hR : R ∈ Rs), ∑ p : ↥(P R hR), dyadicGridLength G (A R hR p).R.1 ≤ (8
      / 3 : ℝ) * dyadicGridLength G R.1 ∧ (∀ I ∈ {I ∈ Tup | Rf I = R}, ∃ (p : ↥(P R
      hR)), I ∈ (A R hR p).cells) ∧ (∀ (p p' : ↥(P R hR)), ∀ I ∈ (A R hR p).cells, I ∈
      (A R hR p').cells → p = p') ∧ ∀ (p : ↥(P R hR)), (A R hR p).cells ⊆ {I ∈ Tup | Rf
      I = R} ∧ (∀ I ∈ (A R hR p).cells, ∀ J' ∈ {I ∈ Tup | Rf I = R}, dyadicGridCell G
      I.1 I.2 ⊆ dyadicGridCell G J'.1 J'.2 → dyadicGridCell G J'.1 J'.2 ⊆ dyadicGridCell
      G (A R hR p).R.1 (A R hR p).R.2 → J' ∈ (A R hR p).cells) ∧ (A R hR p).G = G ∧ (A R
      hR p).w = w ∧ (A R hR p).a = sa ∧ (A R hR p).b = sb ∧ (A R hR p).R ∈
      dyadicFiniteTree G J N ∧ dyadicGridCell G (A R hR p).R.1 (A R hR p).R.2 ⊆
      dyadicGridCell G R.1 R.2 ∧ (A R hR p).H = max (max H (Real.exp ((↑C₁ : ℝ) * ((1 :
      ℝ) + Bp + Real.log H) ^ C₁))) (max (fitBudget Cqa Ca ka) (fitBudget Cqa Ca kb)) ∧
      (A R hR p).Dc = √ε⁻¹ ∧ (A R hR p).S = (2 : ℝ) ∧ (A R hR p).η = (4 : ℝ) * η₀ ∧
      Fintype.card (A R hR p).L = Fintype.card (Xi R (hRsT R hR)).Λ + Fintype.card (Xk R
      (hRsT R hR)).Λ + (Fintype.card (Xi R (hRsT R hR)).Λ * Fintype.card (Xk R (hRsT R
      hR)).Λ * ⌊max H (Real.exp ((↑C₁ : ℝ) * ((1 : ℝ) + Bp + Real.log H) ^ C₁))⌋₊ + Ma +
      Fintype.card (Xga R (hRsT R hR)).Λ) + (Fintype.card (Xi R (hRsT R hR)).Λ *
      Fintype.card (Xk R (hRsT R hR)).Λ * ⌊max H (Real.exp ((↑C₁ : ℝ) * ((1 : ℝ) + Bp +
      Real.log H) ^ C₁))⌋₊ + Mb + Fintype.card (Xgb R (hRsT R hR)).Λ) ∧ ∑ I ∈ (A R hR
      p).cells, dyadicGridLength G I.1 * ‖localProgressionForm (dyadicGridLength G I.1)
      (w I) (slots4 sa i k (f sa - (Xga R (hRsT R hR)).val I) ((Xi R (hRsT R hR)).val I)
      ((Xk R (hRsT R hR)).val I) (f sb - (Xgb R (hRsT R hR)).val I)) - (A R hR p).Hf I
      ((A R hR p).Y I)‖ ≤ baseErr κ (Fintype.card (Xi R (hRsT R hR)).Λ) (Fintype.card
      (Xk R (hRsT R hR)).Λ) (max H (Real.exp ((↑C₁ : ℝ) * ((1 : ℝ) + Bp + Real.log H) ^
      C₁))) Bp ε K₀ (Fintype.card (Xi R (hRsT R hR)).Λ * Fintype.card (Xk R (hRsT R
      hR)).Λ * ⌊max H (Real.exp ((↑C₁ : ℝ) * ((1 : ℝ) + Bp + Real.log H) ^ C₁))⌋₊ + Ma)
      (Fintype.card (Xi R (hRsT R hR)).Λ * Fintype.card (Xk R (hRsT R hR)).Λ * ⌊max H
      (Real.exp ((↑C₁ : ℝ) * ((1 : ℝ) + Bp + Real.log H) ^ C₁))⌋₊ + Mb)
      (fitOpponentConst (M la)) (fitOpponentConst (M lb)) * dyadicGridLength G (A R hR
      p).R.1 ∧ (∀ I ∈ (A R hR p).cells, ∀ (s s' : Fin (4 : ℕ)), s ≠ s' → PairSmall
      (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1) (w I) s s' ((A R hR p).Y I s)
      ((A R hR p).Y I s') (η₀ + ((2 : ℝ) + (2 : ℝ) * ((1 : ℝ) + (↑(Fintype.card (Xi R
      (hRsT R hR)).Λ) : ℝ) + (↑(Fintype.card (Xk R (hRsT R hR)).Λ) : ℝ) +
      (↑(Fintype.card (Xga R (hRsT R hR)).Λ) : ℝ) + (↑(Fintype.card (Xgb R (hRsT R
      hR)).Λ) : ℝ))) * (Real.exp (-(↑ka : ℝ)) + Real.exp (-(↑kb : ℝ))) + ((1 : ℝ) +
      ((↑(Fintype.card (Xi R (hRsT R hR)).Λ * Fintype.card (Xk R (hRsT R hR)).Λ * ⌊max H
      (Real.exp ((↑C₁ : ℝ) * ((1 : ℝ) + Bp + Real.log H) ^ C₁))⌋₊ + Ma) : ℝ) * √((2 : ℝ)
      ^ K₀ / ε) + (1 : ℝ))) * Real.exp (-(↑kb : ℝ)))) ∧ (∀ I ∈ (A R hR p).cells, ∀ (l :
      Fin (4 : ℕ)), (eLpNorm ((A R hR p).Y I l) (2 : ℝ≥0∞) ((A R hR p).μ I)).toReal ≤ (2
      : ℝ)) ∧ (∀ (l : Fin (4 : ℕ)), ∑ I ∈ (A R hR p).cells, dyadicGridLength G I.1 *
      (eLpNorm ((A R hR p).U l I) (2 : ℝ≥0∞) ((A R hR p).μ I)).toReal ^ (2 : ℕ) ≤ (↑K₀ :
      ℝ) ^ (2 : ℕ) * dyadicGridLength G (A R hR p).R.1) ∧ ∑ I ∈ (A R hR p).cells,
      dyadicGridLength G I.1 * ‖(A R hR p).Hf I ((A R hR p).z (3 : Fin (4 : ℕ)) I)‖ ≤ η₀
      * ((↑K₀ : ℝ) ^ (2 : ℕ) * dyadicGridLength G (A R hR p).R.1) ∧ (A R hR
      p).HasColumnRep (1 : ℝ) ∧ (A R hR p).SubRootProps η₀ ((↑K₀ : ℝ) ^ (2 : ℕ))),
  let ιt : Type :=
    Σ R : Rs, (P R.1 R.2)
  let A' : ιt → ActiveSetup κ (max (max c₁ (max c₂ cp)) c₂a) :=
    fun x => A x.1.1 x.1.2 x.2
  ∀ (_ : ∀ (R : ℤ × ℤ) (hR : R ∈ Rs) (p : ↥(P R hR)), ∀ I ∈ (A R hR p).cells, I ∈
      dyadicFiniteTree G J N ∧ I.1 + (↑K₀ : ℤ) ≤ J.1 + (↑N : ℤ) ∧ Rf I = R ∧ kernelHull
      G J N w I)
    (_ : ∀ (R : ℤ × ℤ) (hRT : R ∈ dyadicFiniteTree G J N), Fintype.card (Xi R hRT).Λ ≤ (2 :
      ℕ) * Mt ∧ Fintype.card (Xk R hRT).Λ ≤ (2 : ℕ) * Mt ∧ Fintype.card (Xga R hRT).Λ ≤
      Mt ∧ Fintype.card (Xgb R hRT).Λ ≤ Mt ∧ Fintype.card (Xi R hRT).Λ * Fintype.card
      (Xk R hRT).Λ * ⌊D⌋₊ + Ma ≤ Wa ∧ Fintype.card (Xi R hRT).Λ * Fintype.card (Xk R
      hRT).Λ * ⌊D⌋₊ + Mb ≤ Wb),
  let d₀ : ℤ :=
    J.1 + (↑N : ℤ) + (1 : ℤ) - (↑K₀ : ℤ)
  let Bot : Finset (ℤ × ℤ) :=
    {I ∈ dyadicFiniteTree G J N | ¬I.1 + (↑K₀ : ℤ) ≤ J.1 + (↑N : ℤ) ∧ kernelHull G J N w
      I}
  ∀ (_ : ∀ I ∈ Bot, I ∈ dyadicFiniteTree G J N ∧ d₀ ≤ I.1 ∧ kernelHull G J N w I),
  let anc : ℤ × ℤ → ℤ × ℤ :=
    fun I => if h : d₀ ≤ I.1 then (d₀, Classical.choose (dyadicGridCell_ancestor G h
      I.2)) else I
  ∀ (_ : ∀ (I : ℤ × ℤ), d₀ ≤ I.1 → (anc I).1 = d₀ ∧ dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell
      G (anc I).1 (anc I).2),
  let Rb : ℤ × ℤ → ℤ × ℤ :=
    fun (I : ℤ × ℤ) => if d₀ ≤ (Rf I).1 then Rf I else anc I
  ∀ (_ : ∀ I ∈ dyadicFiniteTree G J N, d₀ ≤ I.1 → ∀ I' ∈ dyadicFiniteTree G J N,
      dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G I'.1 I'.2 → dyadicGridCell G I'.1 I'.2
      ⊆ dyadicGridCell G (Rb I).1 (Rb I).2 → Rb I' = Rb I),
  let Bs : Finset (ℤ × ℤ) :=
    Finset.image Rb Bot
  ∀ (_ : ∀ R' ∈ Bs, R' ∈ dyadicFiniteTree G J N ∧ d₀ ≤ R'.1)
    (hQ : ∀ R' ∈ Bs, Rf R' ∈ dyadicFiniteTree G J N)
    (_ : ∀ R' ∈ Bs, ∀ I ∈ {I ∈ Bot | Rb I = R'}, I ∈ dyadicFiniteTree G J N ∧ kernelHull G J
      N w I ∧ Rf I = Rf R' ∧ dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G R'.1 R'.2 ∧ I.1
      < R'.1 + (↑K₀ : ℤ))
    (AB : (R' : ℤ × ℤ) → R' ∈ Bs → ActiveSetup κ (max (max c₁ (max c₂ cp)) c₂a))
    (_ : ∀ (R' : ℤ × ℤ) (hR' : R' ∈ Bs), (AB R' hR').G = G ∧ (AB R' hR').R = R' ∧ (AB R'
      hR').cells = {I ∈ Bot | Rb I = R'} ∧ (AB R' hR').w = w ∧ (AB R' hR').a = sa ∧ (AB
      R' hR').b = sb ∧ (AB R' hR').H = max D (max (fitBudget Cqa Ca ka) (fitBudget Cqa
      Ca kb)) ∧ (AB R' hR').Dc = √ε⁻¹ ∧ (AB R' hR').S = (2 : ℝ) ∧ (AB R' hR').η = (4 :
      ℝ) * η₀ ∧ Fintype.card (AB R' hR').L = Fintype.card ((Xi (Rf R') (hQ R'
      hR')).reroot (hQ R' hR')).Λ + Fintype.card ((Xk (Rf R') (hQ R' hR')).reroot (hQ R'
      hR')).Λ + Fintype.card ((Xga (Rf R') (hQ R' hR')).reroot (hQ R' hR')).Λ +
      Fintype.card ((Xgb (Rf R') (hQ R' hR')).reroot (hQ R' hR')).Λ ∧ (∀ I ∈ {I ∈ Bot |
      Rb I = R'}, (AB R' hR').Y I = slots4 sa i k (f sa - ((Xga (Rf R') (hQ R'
      hR')).reroot (hQ R' hR')).val I) (((Xi (Rf R') (hQ R' hR')).reroot (hQ R'
      hR')).val I) (((Xk (Rf R') (hQ R' hR')).reroot (hQ R' hR')).val I) (f sb - ((Xgb
      (Rf R') (hQ R' hR')).reroot (hQ R' hR')).val I)) ∧ (∀ I ∈ {I ∈ Bot | Rb I = R'}, ∀
      (s s' : Fin (4 : ℕ)), s ≠ s' → PairSmall (dyadicGridLeft G I.1 I.2)
      (dyadicGridLength G I.1) (w I) s s' ((AB R' hR').Y I s) ((AB R' hR').Y I s') η₀) ∧
      (∀ I ∈ {I ∈ Bot | Rb I = R'}, ∀ (l : Fin (4 : ℕ)), (eLpNorm ((AB R' hR').Y I l) (2
      : ℝ≥0∞) ((AB R' hR').μ I)).toReal ≤ (2 : ℝ)) ∧ (∀ (l : Fin (4 : ℕ)), ∑ I ∈ Bot
      with Rb I = R', dyadicGridLength G I.1 * (eLpNorm ((AB R' hR').U l I) (2 : ℝ≥0∞)
      ((AB R' hR').μ I)).toReal ^ (2 : ℕ) ≤ (↑K₀ : ℝ) ^ (2 : ℕ) * dyadicGridLength G
      R'.1) ∧ ∑ I ∈ Bot with Rb I = R', dyadicGridLength G I.1 * ‖(AB R' hR').Hf I ((AB
      R' hR').z (3 : Fin (4 : ℕ)) I)‖ ≤ η₀ * ((↑K₀ : ℝ) ^ (2 : ℕ) * dyadicGridLength G
      R'.1) ∧ (AB R' hR').HasColumnRep (1 : ℝ) ∧ (AB R' hR').SubRootProps η₀ ((↑K₀ : ℝ)
      ^ (2 : ℕ))),
  let ι : Type :=
    ιt ⊕ ↥Bs
  let Atot : ι → ActiveSetup κ (max (max c₁ (max c₂ cp)) c₂a) :=
    Sum.elim A' fun R' => AB R'.1 R'.2
  ∀ (p : ι), (Atot p).cells ⊆ dyadicFiniteTree G J N ∧ (∀ I ∈ (Atot p).cells,
    kernelHull G J N w I) ∧ (∀ I ∈ (Atot p).cells, ∀ (J' : ℤ × ℤ), dyadicGridCell G
    I.1 I.2 ⊆ dyadicGridCell G J'.1 J'.2 → dyadicGridCell G J'.1 J'.2 ⊆ dyadicGridCell
    G (Atot p).R.1 (Atot p).R.2 → J' ∈ (Atot p).cells) ∧ (Atot p).G = G ∧ (Atot p).w =
    w ∧ (Atot p).R ∈ dyadicFiniteTree G J N ∧ (Atot p).H = max D (max (fitBudget Cqa
    Ca ka) (fitBudget Cqa Ca kb)) ∧ (Atot p).Dc = √ε⁻¹ ∧ (Atot p).S = (2 : ℝ) ∧ (Atot
    p).η = (4 : ℝ) * η₀ ∧ Fintype.card (Atot p).L ≤ (6 : ℕ) * Mt + Wa + Wb ∧ (∀ I ∈
    (Atot p).cells, ∀ (s s' : Fin (4 : ℕ)), s ≠ s' → PairSmall (dyadicGridLeft G I.1
    I.2) (dyadicGridLength G I.1) (w I) s s' ((Atot p).Y I s) ((Atot p).Y I s') (η₀ +
    ((2 : ℝ) + (2 : ℝ) * S₀) * (Real.exp (-(↑ka : ℝ)) + Real.exp (-(↑kb : ℝ))) + ((1 :
    ℝ) + Sp) * Real.exp (-(↑kb : ℝ)))) ∧ (∀ I ∈ (Atot p).cells, ∀ (l : Fin (4 : ℕ)),
    (eLpNorm ((Atot p).Y I l) (2 : ℝ≥0∞) ((Atot p).μ I)).toReal ≤ (2 : ℝ)) ∧ (∀ (l :
    Fin (4 : ℕ)), ∑ I ∈ (Atot p).cells, dyadicGridLength G I.1 * (eLpNorm ((Atot p).U
    l I) (2 : ℝ≥0∞) ((Atot p).μ I)).toReal ^ (2 : ℕ) ≤ (↑K₀ : ℝ) ^ (2 : ℕ) *
    dyadicGridLength G (Atot p).R.1) ∧ ∑ I ∈ (Atot p).cells, dyadicGridLength G I.1 *
    ‖(Atot p).Hf I ((Atot p).z (3 : Fin (4 : ℕ)) I)‖ ≤ η₀ * ((↑K₀ : ℝ) ^ (2 : ℕ) *
    dyadicGridLength G (Atot p).R.1) ∧ (Atot p).HasColumnRep (1 : ℝ) ∧ (Atot
    p).SubRootProps η₀ ((↑K₀ : ℝ) ^ (2 : ℕ))

open scoped Classical in
private def BaseTupleConclusion40Statement : Prop :=
  ∀ (κ : LocalKernelClass)
    (c₂ : ℕ)
    (cp : ℕ)
    (Wp : ℝ)
    (c₁ : ℕ)
    (C₁ : ℕ)
    (c₂a : ℕ)
    (Ca : ℕ)
    (q : ℝ)
    (Cqa : ℝ)
    (G : RealDyadicGrid)
    (J : ℤ × ℤ)
    (N : ℕ)
    (w : ℤ × ℤ → ℝ × ℝ → ℂ)
    (f : Fin (4 : ℕ) → ℝ → ℂ)
    (Bf : ℕ → ℝ)
    (kk : ℕ → ℕ)
    (M : ℕ → ℕ)
    (roots : ℕ → Finset (ℤ × ℤ))
    (seg : ℕ → ℤ × ℤ → ℤ × ℤ)
    (n : ℕ → ℤ × ℤ → ℕ)
    (a : ℕ → ℤ × ℤ → ℕ → ℝ → ℂ)
    (g : ℕ → ℤ × ℤ → ℝ → ℂ)
    (cnt : ℕ → ℤ × ℤ → ℤ × ℤ → ℕ)
    (atm : ℕ → ℤ × ℤ → ℤ × ℤ → ℕ → ℝ → ℂ)
    (_ : ∀ (ℓ : ℕ), IsAdaptiveFit c₂ (Bf ℓ) G J N w (stagPos ℓ) q (f (stagPos ℓ)) (kk ℓ) (M
      ℓ) (roots ℓ) (seg ℓ) (n ℓ) (a ℓ) (g ℓ) ∧ IsAttemptData c₂ (Bf ℓ) G J N (M ℓ)
      (roots ℓ) (seg ℓ) (n ℓ) (a ℓ) (cnt ℓ) (atm ℓ) ∧ IsFitOpponent G J N (f (stagPos
      ℓ)) (roots ℓ) (seg ℓ) (g ℓ) (fitOpponentConst (M ℓ)) (max (2 : ℝ) (↑(M ℓ) : ℝ)) c₂
      (Bf ℓ))
    (u : ℕ)
    (t : ℕ)
    (hut : u < t)
    (Hc : ℝ)
    (Mt : ℕ)
    (_ : ∀ ℓ ≤ t, M ℓ ≤ Mt)
    (η₀ : ℝ)
    (Bp : ℝ)
    (ε : ℝ)
    (K₀ : ℕ)
    (ka : ℕ)
    (kb : ℕ)
    (Ma : ℕ)
    (Mb : ℕ),
  let H : ℝ :=
    max Hc Wp ^ (6 : ℕ)
  let D : ℝ :=
    max H (Real.exp ((↑C₁ : ℝ) * ((1 : ℝ) + Bp + Real.log H) ^ C₁))
  let Wa : ℕ :=
    (2 : ℕ) * Mt * ((2 : ℕ) * Mt) * ⌊D⌋₊ + Ma
  let Wb : ℕ :=
    (2 : ℕ) * Mt * ((2 : ℕ) * Mt) * ⌊D⌋₊ + Mb
  let E : ℝ :=
    baseErr κ ((2 : ℕ) * Mt) ((2 : ℕ) * Mt) D Bp ε K₀ Wa Wb (fitOpponentConst Mt)
      (fitOpponentConst Mt)
  let i : Fin (4 : ℕ) :=
    stagPos u
  let k : Fin (4 : ℕ) :=
    stagPos t
  ∀ (sa : Fin (4 : ℕ))
    (sb : Fin (4 : ℕ)),
  let la : ℕ :=
    StaggerCell.lastLevel sa t
  ∀ (hla2 : la < t),
  let lb : ℕ :=
    StaggerCell.lastLevel sb t
  ∀ (hlb2 : lb < t),
  let Lset : Finset ℕ :=
    {u, u - (4 : ℕ), t, t - (4 : ℕ), la, lb}
  ∀ (hLne : Lset.Nonempty),
  let Rf : ℤ × ℤ → ℤ × ℤ :=
    firstRoot seg Lset hLne
  let Tup : Finset (ℤ × ℤ) :=
    {I ∈ dyadicFiniteTree G J N | I.1 + (↑K₀ : ℤ) ≤ J.1 + (↑N : ℤ) ∧ kernelHull G J N w
      I}
  let Rs : Finset (ℤ × ℤ) :=
    Finset.image Rf Tup
  ∀ (hRtree : ∀ I ∈ dyadicFiniteTree G J N, Rf I ∈ dyadicFiniteTree G J N ∧ dyadicGridCell G I.1
      I.2 ⊆ dyadicGridCell G (Rf I).1 (Rf I).2)
    (hRsT : ∀ R ∈ Rs, R ∈ dyadicFiniteTree G J N)
    (hHl : ∀ ℓ ≤ t, max (Bf ℓ) Wp ^ (6 : ℕ) ≤ H)
    (_ : (1 : ℝ) ≤ H)
    (X : (ℓ : ℕ) → (R : ℤ × ℤ) → R ∈ dyadicFiniteTree G J N → LowList G J N R (max c₂ cp)
      (max (Bf ℓ) Wp ^ (6 : ℕ))),
  let Y : (ℓ : ℕ) → ℓ ≤ t → (R : ℤ × ℤ) → R ∈ dyadicFiniteTree G J N → LowList G J N R (max c₂
      cp) H :=
    fun ℓ hℓ R hR => (X ℓ R hR).mono le_rfl (hHl ℓ hℓ)
  ∀ (hu4 : u - (4 : ℕ) ≤ t)
    (ht4 : t - (4 : ℕ) ≤ t),
  let Xi : (R : ℤ × ℤ) → R ∈ dyadicFiniteTree G J N → LowList G J N R (max c₂ cp) H :=
    fun R hR => if u ≤ 4 then Y u hut.le R hR else (Y u hut.le R hR).sub (Y (u - 4) hu4
      R hR)
  let Xk : (R : ℤ × ℤ) → R ∈ dyadicFiniteTree G J N → LowList G J N R (max c₂ cp) H :=
    fun R hR => if t ≤ 4 then Y t le_rfl R hR else (Y t le_rfl R hR).sub (Y (t - 4) ht4
      R hR)
  let Xga : (R : ℤ × ℤ) → R ∈ dyadicFiniteTree G J N → LowList G J N R (max c₂ cp) H :=
    fun R hR => if 1 ≤ la then Y la hla2.le R hR else LowList.empty
  let Xgb : (R : ℤ × ℤ) → R ∈ dyadicFiniteTree G J N → LowList G J N R (max c₂ cp) H :=
    fun R hR => if 1 ≤ lb then Y lb hlb2.le R hR else LowList.empty
  ∀ (_ : ∀ (I : ℤ × ℤ) (hI : I ∈ dyadicFiniteTree G J N), kernelHull G J N w I → slots4 sa i
      k (f sa - (Xga (Rf I) (hRtree I hI).left).val I) ((Xi (Rf I) (hRtree I
      hI).left).val I) ((Xk (Rf I) (hRtree I hI).left).val I) (f sb - (Xgb (Rf I)
      (hRtree I hI).left).val I) = stagTuple f g u t I)
    (P : (R : ℤ × ℤ) → R ∈ Rs → Finset ((ℤ × ℤ) × ℤ × ℤ))
    (A : (R : ℤ × ℤ) → (hR : R ∈ Rs) → ↥(P R hR) → ActiveSetup κ (max (max c₁ (max c₂ cp))
      c₂a))
    (_ : ∀ (R : ℤ × ℤ) (hR : R ∈ Rs), ∑ p : ↥(P R hR), dyadicGridLength G (A R hR p).R.1 ≤ (8
      / 3 : ℝ) * dyadicGridLength G R.1 ∧ (∀ I ∈ {I ∈ Tup | Rf I = R}, ∃ (p : ↥(P R
      hR)), I ∈ (A R hR p).cells) ∧ (∀ (p p' : ↥(P R hR)), ∀ I ∈ (A R hR p).cells, I ∈
      (A R hR p').cells → p = p') ∧ ∀ (p : ↥(P R hR)), (A R hR p).cells ⊆ {I ∈ Tup | Rf
      I = R} ∧ (∀ I ∈ (A R hR p).cells, ∀ J' ∈ {I ∈ Tup | Rf I = R}, dyadicGridCell G
      I.1 I.2 ⊆ dyadicGridCell G J'.1 J'.2 → dyadicGridCell G J'.1 J'.2 ⊆ dyadicGridCell
      G (A R hR p).R.1 (A R hR p).R.2 → J' ∈ (A R hR p).cells) ∧ (A R hR p).G = G ∧ (A R
      hR p).w = w ∧ (A R hR p).a = sa ∧ (A R hR p).b = sb ∧ (A R hR p).R ∈
      dyadicFiniteTree G J N ∧ dyadicGridCell G (A R hR p).R.1 (A R hR p).R.2 ⊆
      dyadicGridCell G R.1 R.2 ∧ (A R hR p).H = max (max H (Real.exp ((↑C₁ : ℝ) * ((1 :
      ℝ) + Bp + Real.log H) ^ C₁))) (max (fitBudget Cqa Ca ka) (fitBudget Cqa Ca kb)) ∧
      (A R hR p).Dc = √ε⁻¹ ∧ (A R hR p).S = (2 : ℝ) ∧ (A R hR p).η = (4 : ℝ) * η₀ ∧
      Fintype.card (A R hR p).L = Fintype.card (Xi R (hRsT R hR)).Λ + Fintype.card (Xk R
      (hRsT R hR)).Λ + (Fintype.card (Xi R (hRsT R hR)).Λ * Fintype.card (Xk R (hRsT R
      hR)).Λ * ⌊max H (Real.exp ((↑C₁ : ℝ) * ((1 : ℝ) + Bp + Real.log H) ^ C₁))⌋₊ + Ma +
      Fintype.card (Xga R (hRsT R hR)).Λ) + (Fintype.card (Xi R (hRsT R hR)).Λ *
      Fintype.card (Xk R (hRsT R hR)).Λ * ⌊max H (Real.exp ((↑C₁ : ℝ) * ((1 : ℝ) + Bp +
      Real.log H) ^ C₁))⌋₊ + Mb + Fintype.card (Xgb R (hRsT R hR)).Λ) ∧ ∑ I ∈ (A R hR
      p).cells, dyadicGridLength G I.1 * ‖localProgressionForm (dyadicGridLength G I.1)
      (w I) (slots4 sa i k (f sa - (Xga R (hRsT R hR)).val I) ((Xi R (hRsT R hR)).val I)
      ((Xk R (hRsT R hR)).val I) (f sb - (Xgb R (hRsT R hR)).val I)) - (A R hR p).Hf I
      ((A R hR p).Y I)‖ ≤ baseErr κ (Fintype.card (Xi R (hRsT R hR)).Λ) (Fintype.card
      (Xk R (hRsT R hR)).Λ) (max H (Real.exp ((↑C₁ : ℝ) * ((1 : ℝ) + Bp + Real.log H) ^
      C₁))) Bp ε K₀ (Fintype.card (Xi R (hRsT R hR)).Λ * Fintype.card (Xk R (hRsT R
      hR)).Λ * ⌊max H (Real.exp ((↑C₁ : ℝ) * ((1 : ℝ) + Bp + Real.log H) ^ C₁))⌋₊ + Ma)
      (Fintype.card (Xi R (hRsT R hR)).Λ * Fintype.card (Xk R (hRsT R hR)).Λ * ⌊max H
      (Real.exp ((↑C₁ : ℝ) * ((1 : ℝ) + Bp + Real.log H) ^ C₁))⌋₊ + Mb)
      (fitOpponentConst (M la)) (fitOpponentConst (M lb)) * dyadicGridLength G (A R hR
      p).R.1 ∧ (∀ I ∈ (A R hR p).cells, ∀ (s s' : Fin (4 : ℕ)), s ≠ s' → PairSmall
      (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1) (w I) s s' ((A R hR p).Y I s)
      ((A R hR p).Y I s') (η₀ + ((2 : ℝ) + (2 : ℝ) * ((1 : ℝ) + (↑(Fintype.card (Xi R
      (hRsT R hR)).Λ) : ℝ) + (↑(Fintype.card (Xk R (hRsT R hR)).Λ) : ℝ) +
      (↑(Fintype.card (Xga R (hRsT R hR)).Λ) : ℝ) + (↑(Fintype.card (Xgb R (hRsT R
      hR)).Λ) : ℝ))) * (Real.exp (-(↑ka : ℝ)) + Real.exp (-(↑kb : ℝ))) + ((1 : ℝ) +
      ((↑(Fintype.card (Xi R (hRsT R hR)).Λ * Fintype.card (Xk R (hRsT R hR)).Λ * ⌊max H
      (Real.exp ((↑C₁ : ℝ) * ((1 : ℝ) + Bp + Real.log H) ^ C₁))⌋₊ + Ma) : ℝ) * √((2 : ℝ)
      ^ K₀ / ε) + (1 : ℝ))) * Real.exp (-(↑kb : ℝ)))) ∧ (∀ I ∈ (A R hR p).cells, ∀ (l :
      Fin (4 : ℕ)), (eLpNorm ((A R hR p).Y I l) (2 : ℝ≥0∞) ((A R hR p).μ I)).toReal ≤ (2
      : ℝ)) ∧ (∀ (l : Fin (4 : ℕ)), ∑ I ∈ (A R hR p).cells, dyadicGridLength G I.1 *
      (eLpNorm ((A R hR p).U l I) (2 : ℝ≥0∞) ((A R hR p).μ I)).toReal ^ (2 : ℕ) ≤ (↑K₀ :
      ℝ) ^ (2 : ℕ) * dyadicGridLength G (A R hR p).R.1) ∧ ∑ I ∈ (A R hR p).cells,
      dyadicGridLength G I.1 * ‖(A R hR p).Hf I ((A R hR p).z (3 : Fin (4 : ℕ)) I)‖ ≤ η₀
      * ((↑K₀ : ℝ) ^ (2 : ℕ) * dyadicGridLength G (A R hR p).R.1) ∧ (A R hR
      p).HasColumnRep (1 : ℝ) ∧ (A R hR p).SubRootProps η₀ ((↑K₀ : ℝ) ^ (2 : ℕ))),
  let ιt : Type :=
    Σ R : Rs, (P R.1 R.2)
  let A' : ιt → ActiveSetup κ (max (max c₁ (max c₂ cp)) c₂a) :=
    fun x => A x.1.1 x.1.2 x.2
  ∀ (_ : ∀ (R : ℤ × ℤ) (hR : R ∈ Rs) (p : ↥(P R hR)), ∀ I ∈ (A R hR p).cells, I ∈
      dyadicFiniteTree G J N ∧ I.1 + (↑K₀ : ℤ) ≤ J.1 + (↑N : ℤ) ∧ Rf I = R ∧ kernelHull
      G J N w I)
    (_ : ∀ (R : ℤ × ℤ) (hRT : R ∈ dyadicFiniteTree G J N), Fintype.card (Xi R hRT).Λ ≤ (2 :
      ℕ) * Mt ∧ Fintype.card (Xk R hRT).Λ ≤ (2 : ℕ) * Mt ∧ Fintype.card (Xga R hRT).Λ ≤
      Mt ∧ Fintype.card (Xgb R hRT).Λ ≤ Mt ∧ Fintype.card (Xi R hRT).Λ * Fintype.card
      (Xk R hRT).Λ * ⌊D⌋₊ + Ma ≤ Wa ∧ Fintype.card (Xi R hRT).Λ * Fintype.card (Xk R
      hRT).Λ * ⌊D⌋₊ + Mb ≤ Wb)
    (_ : ∑ x : ιt, dyadicGridLength G (A' x).R.1 ≤ (64 / 3 : ℝ) * dyadicGridLength G J.1),
  let d₀ : ℤ :=
    J.1 + (↑N : ℤ) + (1 : ℤ) - (↑K₀ : ℤ)
  let Bot : Finset (ℤ × ℤ) :=
    {I ∈ dyadicFiniteTree G J N | ¬I.1 + (↑K₀ : ℤ) ≤ J.1 + (↑N : ℤ) ∧ kernelHull G J N w
      I}
  ∀ (_ : Bot = {I ∈ dyadicFiniteTree G J N | ¬I.1 + (↑K₀ : ℤ) ≤ J.1 + (↑N : ℤ) ∧ kernelHull G
      J N w I}),
  let anc : ℤ × ℤ → ℤ × ℤ :=
    fun I => if h : d₀ ≤ I.1 then (d₀, Classical.choose (dyadicGridCell_ancestor G h
      I.2)) else I
  let Rb : ℤ × ℤ → ℤ × ℤ :=
    fun (I : ℤ × ℤ) => if d₀ ≤ (Rf I).1 then Rf I else anc I
  let Bs : Finset (ℤ × ℤ) :=
    Finset.image Rb Bot
  ∀ (hQ : ∀ R' ∈ Bs, Rf R' ∈ dyadicFiniteTree G J N)
    (_ : ∀ (R' : ℤ × ℤ) (hR' : R' ∈ Bs), ∀ I ∈ {I ∈ Bot | Rb I = R'}, slots4 sa i k (f sa -
      ((Xga (Rf R') (hQ R' hR')).reroot (hQ R' hR')).val I) (((Xi (Rf R') (hQ R'
      hR')).reroot (hQ R' hR')).val I) (((Xk (Rf R') (hQ R' hR')).reroot (hQ R'
      hR')).val I) (f sb - ((Xgb (Rf R') (hQ R' hR')).reroot (hQ R' hR')).val I) =
      stagTuple f g u t I)
    (AB : (R' : ℤ × ℤ) → R' ∈ Bs → ActiveSetup κ (max (max c₁ (max c₂ cp)) c₂a))
    (_ : ∀ (R' : ℤ × ℤ) (hR' : R' ∈ Bs), (AB R' hR').G = G ∧ (AB R' hR').R = R' ∧ (AB R'
      hR').cells = {I ∈ Bot | Rb I = R'} ∧ (AB R' hR').w = w ∧ (AB R' hR').a = sa ∧ (AB
      R' hR').b = sb ∧ (AB R' hR').H = max D (max (fitBudget Cqa Ca ka) (fitBudget Cqa
      Ca kb)) ∧ (AB R' hR').Dc = √ε⁻¹ ∧ (AB R' hR').S = (2 : ℝ) ∧ (AB R' hR').η = (4 :
      ℝ) * η₀ ∧ Fintype.card (AB R' hR').L = Fintype.card ((Xi (Rf R') (hQ R'
      hR')).reroot (hQ R' hR')).Λ + Fintype.card ((Xk (Rf R') (hQ R' hR')).reroot (hQ R'
      hR')).Λ + Fintype.card ((Xga (Rf R') (hQ R' hR')).reroot (hQ R' hR')).Λ +
      Fintype.card ((Xgb (Rf R') (hQ R' hR')).reroot (hQ R' hR')).Λ ∧ (∀ I ∈ {I ∈ Bot |
      Rb I = R'}, (AB R' hR').Y I = slots4 sa i k (f sa - ((Xga (Rf R') (hQ R'
      hR')).reroot (hQ R' hR')).val I) (((Xi (Rf R') (hQ R' hR')).reroot (hQ R'
      hR')).val I) (((Xk (Rf R') (hQ R' hR')).reroot (hQ R' hR')).val I) (f sb - ((Xgb
      (Rf R') (hQ R' hR')).reroot (hQ R' hR')).val I)) ∧ (∀ I ∈ {I ∈ Bot | Rb I = R'}, ∀
      (s s' : Fin (4 : ℕ)), s ≠ s' → PairSmall (dyadicGridLeft G I.1 I.2)
      (dyadicGridLength G I.1) (w I) s s' ((AB R' hR').Y I s) ((AB R' hR').Y I s') η₀) ∧
      (∀ I ∈ {I ∈ Bot | Rb I = R'}, ∀ (l : Fin (4 : ℕ)), (eLpNorm ((AB R' hR').Y I l) (2
      : ℝ≥0∞) ((AB R' hR').μ I)).toReal ≤ (2 : ℝ)) ∧ (∀ (l : Fin (4 : ℕ)), ∑ I ∈ Bot
      with Rb I = R', dyadicGridLength G I.1 * (eLpNorm ((AB R' hR').U l I) (2 : ℝ≥0∞)
      ((AB R' hR').μ I)).toReal ^ (2 : ℕ) ≤ (↑K₀ : ℝ) ^ (2 : ℕ) * dyadicGridLength G
      R'.1) ∧ ∑ I ∈ Bot with Rb I = R', dyadicGridLength G I.1 * ‖(AB R' hR').Hf I ((AB
      R' hR').z (3 : Fin (4 : ℕ)) I)‖ ≤ η₀ * ((↑K₀ : ℝ) ^ (2 : ℕ) * dyadicGridLength G
      R'.1) ∧ (AB R' hR').HasColumnRep (1 : ℝ) ∧ (AB R' hR').SubRootProps η₀ ((↑K₀ : ℝ)
      ^ (2 : ℕ))),
  let ι : Type :=
    ιt ⊕ ↥Bs
  let Atot : ι → ActiveSetup κ (max (max c₁ (max c₂ cp)) c₂a) :=
    Sum.elim A' fun R' => AB R'.1 R'.2
  ∑ I ∈ dyadicFiniteTree G J N, dyadicGridLength G I.1 * ‖localProgressionForm
    (dyadicGridLength G I.1) (w I) (stagTuple f g u t I)‖ ≤ ∑ p : ι, ∑ I ∈ (Atot
    p).cells, dyadicGridLength G I.1 * ‖(Atot p).Hf I ((Atot p).Y I)‖ + E * ((91 / 3 :
    ℝ) * dyadicGridLength G J.1)

open scoped Classical in
private def BaseTupleStage5Statement : Prop :=
  ∀ (κ : LocalKernelClass)
    (c₂ : ℕ)
    (cp : ℕ)
    (Wp : ℝ)
    (_ : ∀ (c : ℕ) (H' : ℝ), cp ≤ c → Wp ≤ H' → ∃ (d : ℕ) (Φ : QuadraticChartData d), (1 : ℕ)
      ≤ d ∧ QuadraticChartComplexity c H' Φ ∧ IsBoundedQuadraticChart Φ)
    (c₁ : ℕ)
    (C₁ : ℕ)
    (c₂a : ℕ)
    (Ca : ℕ)
    (q : ℝ)
    (_ : (2 : ℝ) < q)
    (Cqa : ℝ)
    (G : RealDyadicGrid)
    (J : ℤ × ℤ)
    (N : ℕ)
    (w : ℤ × ℤ → ℝ × ℝ → ℂ)
    (_ : ∀ (I : ℤ × ℤ), IsAdmissibleLocalKernel κ (dyadicGridLeft G I.1 I.2)
      (dyadicGridLength G I.1) (w I))
    (f : Fin (4 : ℕ) → ℝ → ℂ)
    (_ : ∀ (l : Fin (4 : ℕ)), Measurable (f l))
    (_ : ∀ (l : Fin (4 : ℕ)), ∀ I ∈ dyadicFiniteTree G J N, I = J ∨ kernelHull G J N w I →
      eLpNorm (f l) (ENNReal.ofReal q) (normalizedIntervalMeasure (dyadicGridLeft G I.1
      I.2) (dyadicGridLength G I.1)) ≤ (1 : ℝ≥0∞))
    (Bf : ℕ → ℝ)
    (kk : ℕ → ℕ)
    (M : ℕ → ℕ)
    (roots : ℕ → Finset (ℤ × ℤ))
    (seg : ℕ → ℤ × ℤ → ℤ × ℤ)
    (n : ℕ → ℤ × ℤ → ℕ)
    (a : ℕ → ℤ × ℤ → ℕ → ℝ → ℂ)
    (g : ℕ → ℤ × ℤ → ℝ → ℂ)
    (cnt : ℕ → ℤ × ℤ → ℤ × ℤ → ℕ)
    (atm : ℕ → ℤ × ℤ → ℤ × ℤ → ℕ → ℝ → ℂ)
    (_ : ∀ (ℓ : ℕ), IsAdaptiveFit c₂ (Bf ℓ) G J N w (stagPos ℓ) q (f (stagPos ℓ)) (kk ℓ) (M
      ℓ) (roots ℓ) (seg ℓ) (n ℓ) (a ℓ) (g ℓ) ∧ IsAttemptData c₂ (Bf ℓ) G J N (M ℓ)
      (roots ℓ) (seg ℓ) (n ℓ) (a ℓ) (cnt ℓ) (atm ℓ) ∧ IsFitOpponent G J N (f (stagPos
      ℓ)) (roots ℓ) (seg ℓ) (g ℓ) (fitOpponentConst (M ℓ)) (max (2 : ℝ) (↑(M ℓ) : ℝ)) c₂
      (Bf ℓ))
    (u : ℕ)
    (t : ℕ)
    (hut : u < t)
    (Hc : ℝ)
    (Mt : ℕ)
    (_ : ∀ ℓ ≤ t, M ℓ ≤ Mt)
    (η₀ : ℝ)
    (_ : (0 : ℝ) ≤ η₀)
    (_ : ∀ I ∈ dyadicFiniteTree G J N, kernelHull G J N w I → ∀ (s s' : Fin (4 : ℕ)), s ≠ s'
      → PairSmall (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1) (w I) s s'
      (stagTuple f g u t I s) (stagTuple f g u t I s') η₀)
    (_ : ∀ I ∈ dyadicFiniteTree G J N, kernelHull G J N w I → ∀ (l : Fin (4 : ℕ)), eLpNorm
      (stagTuple f g u t I l) (2 : ℝ≥0∞) (normalizedIntervalMeasure (dyadicGridLeft G
      I.1 I.2) (dyadicGridLength G I.1)) ≤ ENNReal.ofReal (2 : ℝ))
    (Bp : ℝ)
    (ε : ℝ)
    (K₀ : ℕ)
    (ka : ℕ)
    (kb : ℕ)
    (Ma : ℕ)
    (Mb : ℕ)
    (_ : (0 : ℝ) < ε)
    (_ : ε ≤ (1 : ℝ)),
  let H : ℝ :=
    max Hc Wp ^ (6 : ℕ)
  let D : ℝ :=
    max H (Real.exp ((↑C₁ : ℝ) * ((1 : ℝ) + Bp + Real.log H) ^ C₁))
  let Wa : ℕ :=
    (2 : ℕ) * Mt * ((2 : ℕ) * Mt) * ⌊D⌋₊ + Ma
  let Wb : ℕ :=
    (2 : ℕ) * Mt * ((2 : ℕ) * Mt) * ⌊D⌋₊ + Mb
  let E : ℝ :=
    baseErr κ ((2 : ℕ) * Mt) ((2 : ℕ) * Mt) D Bp ε K₀ Wa Wb (fitOpponentConst Mt)
      (fitOpponentConst Mt)
  let S₀ : ℝ :=
    (1 : ℝ) + (6 : ℝ) * (↑Mt : ℝ)
  let Sp : ℝ :=
    (↑Wa : ℝ) * √((2 : ℝ) ^ K₀ / ε) + (1 : ℝ)
  let i : Fin (4 : ℕ) :=
    stagPos u
  let k : Fin (4 : ℕ) :=
    stagPos t
  ∀ (_ : i ≠ k)
    (sa : Fin (4 : ℕ))
    (sb : Fin (4 : ℕ))
    (_ : sa ≠ sb)
    (_ : sa ≠ i)
    (_ : sa ≠ k)
    (_ : sb ≠ i)
    (_ : sb ≠ k),
  let la : ℕ :=
    StaggerCell.lastLevel sa t
  ∀ (hla2 : la < t),
  let lb : ℕ :=
    StaggerCell.lastLevel sb t
  ∀ (hlb2 : lb < t),
  let Lset : Finset ℕ :=
    {u, u - (4 : ℕ), t, t - (4 : ℕ), la, lb}
  ∀ (hLne : Lset.Nonempty)
    (_ : SegData G J N seg Lset),
  let Rf : ℤ × ℤ → ℤ × ℤ :=
    firstRoot seg Lset hLne
  let Tup : Finset (ℤ × ℤ) :=
    {I ∈ dyadicFiniteTree G J N | I.1 + (↑K₀ : ℤ) ≤ J.1 + (↑N : ℤ) ∧ kernelHull G J N w
      I}
  let Rs : Finset (ℤ × ℤ) :=
    Finset.image Rf Tup
  ∀ (hRtree : ∀ I ∈ dyadicFiniteTree G J N, Rf I ∈ dyadicFiniteTree G J N ∧ dyadicGridCell G I.1
      I.2 ⊆ dyadicGridCell G (Rf I).1 (Rf I).2)
    (hRsT : ∀ R ∈ Rs, R ∈ dyadicFiniteTree G J N)
    (hHl : ∀ ℓ ≤ t, max (Bf ℓ) Wp ^ (6 : ℕ) ≤ H)
    (_ : (1 : ℝ) ≤ H)
    (_ : Wp ≤ H)
    (X : (ℓ : ℕ) → (R : ℤ × ℤ) → R ∈ dyadicFiniteTree G J N → LowList G J N R (max c₂ cp)
      (max (Bf ℓ) Wp ^ (6 : ℕ))),
  let Y : (ℓ : ℕ) → ℓ ≤ t → (R : ℤ × ℤ) → R ∈ dyadicFiniteTree G J N → LowList G J N R (max c₂
      cp) H :=
    fun ℓ hℓ R hR => (X ℓ R hR).mono le_rfl (hHl ℓ hℓ)
  ∀ (hu4 : u - (4 : ℕ) ≤ t)
    (ht4 : t - (4 : ℕ) ≤ t),
  let Xi : (R : ℤ × ℤ) → R ∈ dyadicFiniteTree G J N → LowList G J N R (max c₂ cp) H :=
    fun R hR => if u ≤ 4 then Y u hut.le R hR else (Y u hut.le R hR).sub (Y (u - 4) hu4
      R hR)
  let Xk : (R : ℤ × ℤ) → R ∈ dyadicFiniteTree G J N → LowList G J N R (max c₂ cp) H :=
    fun R hR => if t ≤ 4 then Y t le_rfl R hR else (Y t le_rfl R hR).sub (Y (t - 4) ht4
      R hR)
  let Xga : (R : ℤ × ℤ) → R ∈ dyadicFiniteTree G J N → LowList G J N R (max c₂ cp) H :=
    fun R hR => if 1 ≤ la then Y la hla2.le R hR else LowList.empty
  let Xgb : (R : ℤ × ℤ) → R ∈ dyadicFiniteTree G J N → LowList G J N R (max c₂ cp) H :=
    fun R hR => if 1 ≤ lb then Y lb hlb2.le R hR else LowList.empty
  ∀ (_ : t ∈ Lset)
    (_ : t - (4 : ℕ) ∈ Lset)
    (_ : ∀ (I : ℤ × ℤ) (hI : I ∈ dyadicFiniteTree G J N), kernelHull G J N w I → slots4 sa i
      k (f sa - (Xga (Rf I) (hRtree I hI).left).val I) ((Xi (Rf I) (hRtree I
      hI).left).val I) ((Xk (Rf I) (hRtree I hI).left).val I) (f sb - (Xgb (Rf I)
      (hRtree I hI).left).val I) = stagTuple f g u t I)
    (z : ℕ → (R : ℤ × ℤ) → R ∈ dyadicFiniteTree G J N → ℤ × ℤ → ℝ → ℂ),
  let BdR : (R : ℤ × ℤ) → R ∈ dyadicFiniteTree G J N → ℝ :=
    fun (R : ℤ × ℤ) (hR : R ∈ dyadicFiniteTree G J N) => (2 : ℝ) + (↑(Fintype.card (Xi R
      hR).Λ + Fintype.card (Xk R hR).Λ + Fintype.card (Xga R hR).Λ + Fintype.card (Xgb R
      hR).Λ) : ℝ)
  ∀ (_ : ∀ (R : ℤ × ℤ) (hR : R ∈ dyadicFiniteTree G J N), IsBasicOn G R (dyadicRemainingDepth
      J N R) (1 : ℝ) (BdR R hR) (max c₂ cp) H w (z t R hR))
    (_ : ∀ (R : ℤ × ℤ) (hR : R ∈ dyadicFiniteTree G J N), ¬t ≤ (4 : ℕ) → IsBasicOn G R
      (dyadicRemainingDepth J N R) (1 : ℝ) (BdR R hR) (max c₂ cp) H w (z (t - (4 : ℕ)) R
      hR))
    (z0 : (R : ℤ × ℤ) → R ∈ dyadicFiniteTree G J N → ℤ × ℤ → ℝ → ℂ)
    (_ : ∀ (R : ℤ × ℤ) (hR : R ∈ dyadicFiniteTree G J N) (I : ℤ × ℤ), ∀ᵐ (y : ℝ), z0 R hR I y
      = (0 : ℂ))
    (_ : ∀ (R : ℤ × ℤ) (hR : R ∈ dyadicFiniteTree G J N), IsBasicOn G R (dyadicRemainingDepth
      J N R) (1 : ℝ) (BdR R hR) (max c₂ cp) H w (z0 R hR)),
  let za : (R : ℤ × ℤ) → R ∈ dyadicFiniteTree G J N → ℤ × ℤ → ℝ → ℂ :=
    fun (R : ℤ × ℤ) (hR : R ∈ dyadicFiniteTree G J N) => if (1 : ℕ) ≤ la then z la R hR
      else z0 R hR
  let zb : (R : ℤ × ℤ) → R ∈ dyadicFiniteTree G J N → ℤ × ℤ → ℝ → ℂ :=
    fun (R : ℤ × ℤ) (hR : R ∈ dyadicFiniteTree G J N) => if (1 : ℕ) ≤ lb then z lb R hR
      else z0 R hR
  ∀ (_ : ∀ (R : ℤ × ℤ) (hR : R ∈ dyadicFiniteTree G J N), IsBasicOn G R (dyadicRemainingDepth
      J N R) (1 : ℝ) (BdR R hR) (max c₂ cp) H w (za R hR))
    (_ : ∀ (R : ℤ × ℤ) (hR : R ∈ dyadicFiniteTree G J N), IsBasicOn G R (dyadicRemainingDepth
      J N R) (1 : ℝ) (BdR R hR) (max c₂ cp) H w (zb R hR))
    (P : (R : ℤ × ℤ) → R ∈ Rs → Finset ((ℤ × ℤ) × ℤ × ℤ))
    (A : (R : ℤ × ℤ) → (hR : R ∈ Rs) → ↥(P R hR) → ActiveSetup κ (max (max c₁ (max c₂ cp))
      c₂a))
    (_ : ∀ (R : ℤ × ℤ) (hR : R ∈ Rs), ∑ p : ↥(P R hR), dyadicGridLength G (A R hR p).R.1 ≤ (8
      / 3 : ℝ) * dyadicGridLength G R.1 ∧ (∀ I ∈ {I ∈ Tup | Rf I = R}, ∃ (p : ↥(P R
      hR)), I ∈ (A R hR p).cells) ∧ (∀ (p p' : ↥(P R hR)), ∀ I ∈ (A R hR p).cells, I ∈
      (A R hR p').cells → p = p') ∧ ∀ (p : ↥(P R hR)), (A R hR p).cells ⊆ {I ∈ Tup | Rf
      I = R} ∧ (∀ I ∈ (A R hR p).cells, ∀ J' ∈ {I ∈ Tup | Rf I = R}, dyadicGridCell G
      I.1 I.2 ⊆ dyadicGridCell G J'.1 J'.2 → dyadicGridCell G J'.1 J'.2 ⊆ dyadicGridCell
      G (A R hR p).R.1 (A R hR p).R.2 → J' ∈ (A R hR p).cells) ∧ (A R hR p).G = G ∧ (A R
      hR p).w = w ∧ (A R hR p).a = sa ∧ (A R hR p).b = sb ∧ (A R hR p).R ∈
      dyadicFiniteTree G J N ∧ dyadicGridCell G (A R hR p).R.1 (A R hR p).R.2 ⊆
      dyadicGridCell G R.1 R.2 ∧ (A R hR p).H = max (max H (Real.exp ((↑C₁ : ℝ) * ((1 :
      ℝ) + Bp + Real.log H) ^ C₁))) (max (fitBudget Cqa Ca ka) (fitBudget Cqa Ca kb)) ∧
      (A R hR p).Dc = √ε⁻¹ ∧ (A R hR p).S = (2 : ℝ) ∧ (A R hR p).η = (4 : ℝ) * η₀ ∧
      Fintype.card (A R hR p).L = Fintype.card (Xi R (hRsT R hR)).Λ + Fintype.card (Xk R
      (hRsT R hR)).Λ + (Fintype.card (Xi R (hRsT R hR)).Λ * Fintype.card (Xk R (hRsT R
      hR)).Λ * ⌊max H (Real.exp ((↑C₁ : ℝ) * ((1 : ℝ) + Bp + Real.log H) ^ C₁))⌋₊ + Ma +
      Fintype.card (Xga R (hRsT R hR)).Λ) + (Fintype.card (Xi R (hRsT R hR)).Λ *
      Fintype.card (Xk R (hRsT R hR)).Λ * ⌊max H (Real.exp ((↑C₁ : ℝ) * ((1 : ℝ) + Bp +
      Real.log H) ^ C₁))⌋₊ + Mb + Fintype.card (Xgb R (hRsT R hR)).Λ) ∧ ∑ I ∈ (A R hR
      p).cells, dyadicGridLength G I.1 * ‖localProgressionForm (dyadicGridLength G I.1)
      (w I) (slots4 sa i k (f sa - (Xga R (hRsT R hR)).val I) ((Xi R (hRsT R hR)).val I)
      ((Xk R (hRsT R hR)).val I) (f sb - (Xgb R (hRsT R hR)).val I)) - (A R hR p).Hf I
      ((A R hR p).Y I)‖ ≤ baseErr κ (Fintype.card (Xi R (hRsT R hR)).Λ) (Fintype.card
      (Xk R (hRsT R hR)).Λ) (max H (Real.exp ((↑C₁ : ℝ) * ((1 : ℝ) + Bp + Real.log H) ^
      C₁))) Bp ε K₀ (Fintype.card (Xi R (hRsT R hR)).Λ * Fintype.card (Xk R (hRsT R
      hR)).Λ * ⌊max H (Real.exp ((↑C₁ : ℝ) * ((1 : ℝ) + Bp + Real.log H) ^ C₁))⌋₊ + Ma)
      (Fintype.card (Xi R (hRsT R hR)).Λ * Fintype.card (Xk R (hRsT R hR)).Λ * ⌊max H
      (Real.exp ((↑C₁ : ℝ) * ((1 : ℝ) + Bp + Real.log H) ^ C₁))⌋₊ + Mb)
      (fitOpponentConst (M la)) (fitOpponentConst (M lb)) * dyadicGridLength G (A R hR
      p).R.1 ∧ (∀ I ∈ (A R hR p).cells, ∀ (s s' : Fin (4 : ℕ)), s ≠ s' → PairSmall
      (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1) (w I) s s' ((A R hR p).Y I s)
      ((A R hR p).Y I s') (η₀ + ((2 : ℝ) + (2 : ℝ) * ((1 : ℝ) + (↑(Fintype.card (Xi R
      (hRsT R hR)).Λ) : ℝ) + (↑(Fintype.card (Xk R (hRsT R hR)).Λ) : ℝ) +
      (↑(Fintype.card (Xga R (hRsT R hR)).Λ) : ℝ) + (↑(Fintype.card (Xgb R (hRsT R
      hR)).Λ) : ℝ))) * (Real.exp (-(↑ka : ℝ)) + Real.exp (-(↑kb : ℝ))) + ((1 : ℝ) +
      ((↑(Fintype.card (Xi R (hRsT R hR)).Λ * Fintype.card (Xk R (hRsT R hR)).Λ * ⌊max H
      (Real.exp ((↑C₁ : ℝ) * ((1 : ℝ) + Bp + Real.log H) ^ C₁))⌋₊ + Ma) : ℝ) * √((2 : ℝ)
      ^ K₀ / ε) + (1 : ℝ))) * Real.exp (-(↑kb : ℝ)))) ∧ (∀ I ∈ (A R hR p).cells, ∀ (l :
      Fin (4 : ℕ)), (eLpNorm ((A R hR p).Y I l) (2 : ℝ≥0∞) ((A R hR p).μ I)).toReal ≤ (2
      : ℝ)) ∧ (∀ (l : Fin (4 : ℕ)), ∑ I ∈ (A R hR p).cells, dyadicGridLength G I.1 *
      (eLpNorm ((A R hR p).U l I) (2 : ℝ≥0∞) ((A R hR p).μ I)).toReal ^ (2 : ℕ) ≤ (↑K₀ :
      ℝ) ^ (2 : ℕ) * dyadicGridLength G (A R hR p).R.1) ∧ ∑ I ∈ (A R hR p).cells,
      dyadicGridLength G I.1 * ‖(A R hR p).Hf I ((A R hR p).z (3 : Fin (4 : ℕ)) I)‖ ≤ η₀
      * ((↑K₀ : ℝ) ^ (2 : ℕ) * dyadicGridLength G (A R hR p).R.1) ∧ (A R hR
      p).HasColumnRep (1 : ℝ) ∧ (A R hR p).SubRootProps η₀ ((↑K₀ : ℝ) ^ (2 : ℕ)))
    (_ : ∀ (T : Finset (ℤ × ℤ)), (∀ I ∈ T, I ∈ dyadicFiniteTree G J N) → ∑ R ∈ Finset.image
      Rf T, dyadicGridLength G R.1 ≤ (8 : ℝ) * dyadicGridLength G J.1),
  let ιt : Type :=
    Σ R : Rs, (P R.1 R.2)
  let A' : ιt → ActiveSetup κ (max (max c₁ (max c₂ cp)) c₂a) :=
    fun x => A x.1.1 x.1.2 x.2
  ∀ (_ : ∀ (R : ℤ × ℤ) (hR : R ∈ Rs) (p : ↥(P R hR)), ∀ I ∈ (A R hR p).cells, I ∈
      dyadicFiniteTree G J N ∧ I.1 + (↑K₀ : ℤ) ≤ J.1 + (↑N : ℤ) ∧ Rf I = R ∧ kernelHull
      G J N w I)
    (_ : ∀ (R : ℤ × ℤ) (hRT : R ∈ dyadicFiniteTree G J N), Fintype.card (Xi R hRT).Λ ≤ (2 :
      ℕ) * Mt ∧ Fintype.card (Xk R hRT).Λ ≤ (2 : ℕ) * Mt ∧ Fintype.card (Xga R hRT).Λ ≤
      Mt ∧ Fintype.card (Xgb R hRT).Λ ≤ Mt ∧ Fintype.card (Xi R hRT).Λ * Fintype.card
      (Xk R hRT).Λ * ⌊D⌋₊ + Ma ≤ Wa ∧ Fintype.card (Xi R hRT).Λ * Fintype.card (Xk R
      hRT).Λ * ⌊D⌋₊ + Mb ≤ Wb)
    (_ : ∑ x : ιt, dyadicGridLength G (A' x).R.1 ≤ (64 / 3 : ℝ) * dyadicGridLength G J.1),
  let d₀ : ℤ :=
    J.1 + (↑N : ℤ) + (1 : ℤ) - (↑K₀ : ℤ)
  let Bot : Finset (ℤ × ℤ) :=
    {I ∈ dyadicFiniteTree G J N | ¬I.1 + (↑K₀ : ℤ) ≤ J.1 + (↑N : ℤ) ∧ kernelHull G J N w
      I}
  ∀ (_ : Bot = {I ∈ dyadicFiniteTree G J N | ¬I.1 + (↑K₀ : ℤ) ≤ J.1 + (↑N : ℤ) ∧ kernelHull G
      J N w I})
    (_ : ∀ I ∈ Bot, I ∈ dyadicFiniteTree G J N ∧ d₀ ≤ I.1 ∧ kernelHull G J N w I),
  let anc : ℤ × ℤ → ℤ × ℤ :=
    fun I => if h : d₀ ≤ I.1 then (d₀, Classical.choose (dyadicGridCell_ancestor G h
      I.2)) else I
  ∀ (_ : ∀ (I : ℤ × ℤ), d₀ ≤ I.1 → (anc I).1 = d₀ ∧ dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell
      G (anc I).1 (anc I).2),
  let Rb : ℤ × ℤ → ℤ × ℤ :=
    fun (I : ℤ × ℤ) => if d₀ ≤ (Rf I).1 then Rf I else anc I
  ∀ (_ : ∀ I ∈ dyadicFiniteTree G J N, d₀ ≤ I.1 → Rb I ∈ dyadicFiniteTree G J N ∧ d₀ ≤ (Rb
      I).1 ∧ dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G (Rb I).1 (Rb I).2 ∧
      dyadicGridCell G (Rb I).1 (Rb I).2 ⊆ dyadicGridCell G (Rf I).1 (Rf I).2)
    (_ : ∀ I ∈ dyadicFiniteTree G J N, d₀ ≤ I.1 → ∀ I' ∈ dyadicFiniteTree G J N,
      dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G I'.1 I'.2 → dyadicGridCell G I'.1 I'.2
      ⊆ dyadicGridCell G (Rb I).1 (Rb I).2 → Rb I' = Rb I),
  let Bs : Finset (ℤ × ℤ) :=
    Finset.image Rb Bot
  ∀ (_ : ∀ R' ∈ Bs, R' ∈ dyadicFiniteTree G J N ∧ d₀ ≤ R'.1)
    (hQ : ∀ R' ∈ Bs, Rf R' ∈ dyadicFiniteTree G J N)
    (_ : ∀ R' ∈ Bs, R' ∈ dyadicFiniteTree G (Rf R') (dyadicRemainingDepth J N (Rf R')))
    (_ : ∀ R' ∈ Bs, ∀ I ∈ {I ∈ Bot | Rb I = R'}, I ∈ dyadicFiniteTree G J N ∧ kernelHull G J
      N w I ∧ Rf I = Rf R' ∧ dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G R'.1 R'.2 ∧ I.1
      < R'.1 + (↑K₀ : ℤ))
    (_ : ∀ R' ∈ Bs, ∀ I ∈ {I ∈ Bot | Rb I = R'}, I ∈ dyadicFiniteTree G (Rf R')
      (dyadicRemainingDepth J N (Rf R')) ∧ kernelHull G (Rf R') (dyadicRemainingDepth J
      N (Rf R')) w I ∧ dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G R'.1 R'.2 ∧ I.1 <
      R'.1 + (↑K₀ : ℤ))
    (_ : ∀ (R' : ℤ × ℤ) (hR' : R' ∈ Bs), ∀ I ∈ {I ∈ Bot | Rb I = R'}, slots4 sa i k (f sa -
      ((Xga (Rf R') (hQ R' hR')).reroot (hQ R' hR')).val I) (((Xi (Rf R') (hQ R'
      hR')).reroot (hQ R' hR')).val I) (((Xk (Rf R') (hQ R' hR')).reroot (hQ R'
      hR')).val I) (f sb - ((Xgb (Rf R') (hQ R' hR')).reroot (hQ R' hR')).val I) =
      stagTuple f g u t I)
    (_ : ∀ (ℓ : ℕ) (hℓ : ℓ ≤ t), ℓ ∈ Lset → ∀ (R : ℤ × ℤ) (hR : R ∈ dyadicFiniteTree G J N),
      ∀ I ∈ dyadicFiniteTree G J N, kernelHull G J N w I → Rf I = R → ∀ᵐ (y : ℝ), y ∈
      dyadicGridCell G I.1 I.2 → (Y ℓ hℓ R hR).val I y = z ℓ R hR I y)
    (_ : ∀ (R : ℤ × ℤ) (hR : R ∈ dyadicFiniteTree G J N), ∀ I ∈ dyadicFiniteTree G J N,
      kernelHull G J N w I → Rf I = R → ∀ᵐ (y : ℝ), y ∈ dyadicGridCell G I.1 I.2 → za R
      hR I y = (Xga R hR).val I y)
    (_ : ∀ (R : ℤ × ℤ) (hR : R ∈ dyadicFiniteTree G J N), ∀ I ∈ dyadicFiniteTree G J N,
      kernelHull G J N w I → Rf I = R → ∀ᵐ (y : ℝ), y ∈ dyadicGridCell G I.1 I.2 → zb R
      hR I y = (Xgb R hR).val I y)
    (_ : ∀ (R' : ℤ × ℤ) (hR' : R' ∈ Bs), ∃ (z₁ : ℤ × ℤ → ℝ → ℂ) (z₂ : ℤ × ℤ → ℝ → ℂ),
      IsBasicOn G (Rf R') (dyadicRemainingDepth J N (Rf R')) (1 : ℝ) (BdR (Rf R') (hQ R'
      hR')) (max c₂ cp) H w z₁ ∧ IsBasicOn G (Rf R') (dyadicRemainingDepth J N (Rf R'))
      (1 : ℝ) (BdR (Rf R') (hQ R' hR')) (max c₂ cp) H w z₂ ∧ ∀ I ∈ {I ∈ Bot | Rb I =
      R'}, ∀ᵐ (y : ℝ), y ∈ dyadicGridCell G I.1 I.2 → ((Xi (Rf R') (hQ R' hR')).reroot
      (hQ R' hR')).val I y = z₁ I y - z₂ I y),
  ∃ (ι : Type) (_ : Fintype ι) (A : ι → ActiveSetup κ (max (max c₁ (max c₂ cp)) c₂a)),
    ∑ p : ι, dyadicGridLength G (A p).R.1 ≤ (91 / 3 : ℝ) * dyadicGridLength G J.1 ∧ (∀
    (p p' : ι), ∀ I ∈ (A p).cells, I ∈ (A p').cells → p = p') ∧ (∀ (p : ι), (A
    p).cells ⊆ dyadicFiniteTree G J N ∧ (∀ I ∈ (A p).cells, kernelHull G J N w I) ∧ (∀
    I ∈ (A p).cells, ∀ (J' : ℤ × ℤ), dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G J'.1
    J'.2 → dyadicGridCell G J'.1 J'.2 ⊆ dyadicGridCell G (A p).R.1 (A p).R.2 → J' ∈ (A
    p).cells) ∧ (A p).G = G ∧ (A p).w = w ∧ (A p).R ∈ dyadicFiniteTree G J N ∧ (A p).H
    = max D (max (fitBudget Cqa Ca ka) (fitBudget Cqa Ca kb)) ∧ (A p).Dc = √ε⁻¹ ∧ (A
    p).S = (2 : ℝ) ∧ (A p).η = (4 : ℝ) * η₀ ∧ Fintype.card (A p).L ≤ (6 : ℕ) * Mt + Wa
    + Wb ∧ (∀ I ∈ (A p).cells, ∀ (s s' : Fin (4 : ℕ)), s ≠ s' → PairSmall
    (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1) (w I) s s' ((A p).Y I s) ((A
    p).Y I s') (η₀ + ((2 : ℝ) + (2 : ℝ) * S₀) * (Real.exp (-(↑ka : ℝ)) + Real.exp
    (-(↑kb : ℝ))) + ((1 : ℝ) + Sp) * Real.exp (-(↑kb : ℝ)))) ∧ (∀ I ∈ (A p).cells, ∀
    (l : Fin (4 : ℕ)), (eLpNorm ((A p).Y I l) (2 : ℝ≥0∞) ((A p).μ I)).toReal ≤ (2 :
    ℝ)) ∧ (∀ (l : Fin (4 : ℕ)), ∑ I ∈ (A p).cells, dyadicGridLength G I.1 * (eLpNorm
    ((A p).U l I) (2 : ℝ≥0∞) ((A p).μ I)).toReal ^ (2 : ℕ) ≤ (↑K₀ : ℝ) ^ (2 : ℕ) *
    dyadicGridLength G (A p).R.1) ∧ ∑ I ∈ (A p).cells, dyadicGridLength G I.1 * ‖(A
    p).Hf I ((A p).z (3 : Fin (4 : ℕ)) I)‖ ≤ η₀ * ((↑K₀ : ℝ) ^ (2 : ℕ) *
    dyadicGridLength G (A p).R.1) ∧ (A p).HasColumnRep (1 : ℝ) ∧ (A p).SubRootProps η₀
    ((↑K₀ : ℝ) ^ (2 : ℕ))) ∧ ∑ I ∈ dyadicFiniteTree G J N, dyadicGridLength G I.1 *
    ‖localProgressionForm (dyadicGridLength G I.1) (w I) (stagTuple f g u t I)‖ ≤ ∑ p
    : ι, ∑ I ∈ (A p).cells, dyadicGridLength G I.1 * ‖(A p).Hf I ((A p).Y I)‖ + E *
    ((91 / 3 : ℝ) * dyadicGridLength G J.1)

open scoped Classical in
private def BaseTupleStage4Statement : Prop :=
  ∀ (κ : LocalKernelClass)
    (c₂ : ℕ)
    (cp : ℕ)
    (Wp : ℝ)
    (_ : ∀ (c : ℕ) (H' : ℝ), cp ≤ c → Wp ≤ H' → ∃ (d : ℕ) (Φ : QuadraticChartData d), (1 : ℕ)
      ≤ d ∧ QuadraticChartComplexity c H' Φ ∧ IsBoundedQuadraticChart Φ)
    (c₁ : ℕ)
    (C₁ : ℕ)
    (c₂a : ℕ)
    (Ca : ℕ)
    (q : ℝ)
    (_ : (2 : ℝ) < q)
    (Cqa : ℝ)
    (G : RealDyadicGrid)
    (J : ℤ × ℤ)
    (N : ℕ)
    (w : ℤ × ℤ → ℝ × ℝ → ℂ)
    (_ : ∀ (I : ℤ × ℤ), IsAdmissibleLocalKernel κ (dyadicGridLeft G I.1 I.2)
      (dyadicGridLength G I.1) (w I))
    (f : Fin (4 : ℕ) → ℝ → ℂ)
    (_ : ∀ (l : Fin (4 : ℕ)), Measurable (f l))
    (_ : ∀ (l : Fin (4 : ℕ)), ∀ I ∈ dyadicFiniteTree G J N, I = J ∨ kernelHull G J N w I →
      eLpNorm (f l) (ENNReal.ofReal q) (normalizedIntervalMeasure (dyadicGridLeft G I.1
      I.2) (dyadicGridLength G I.1)) ≤ (1 : ℝ≥0∞))
    (Bf : ℕ → ℝ)
    (kk : ℕ → ℕ)
    (M : ℕ → ℕ)
    (roots : ℕ → Finset (ℤ × ℤ))
    (seg : ℕ → ℤ × ℤ → ℤ × ℤ)
    (n : ℕ → ℤ × ℤ → ℕ)
    (a : ℕ → ℤ × ℤ → ℕ → ℝ → ℂ)
    (g : ℕ → ℤ × ℤ → ℝ → ℂ)
    (cnt : ℕ → ℤ × ℤ → ℤ × ℤ → ℕ)
    (atm : ℕ → ℤ × ℤ → ℤ × ℤ → ℕ → ℝ → ℂ)
    (_ : ∀ (ℓ : ℕ), IsAdaptiveFit c₂ (Bf ℓ) G J N w (stagPos ℓ) q (f (stagPos ℓ)) (kk ℓ) (M
      ℓ) (roots ℓ) (seg ℓ) (n ℓ) (a ℓ) (g ℓ) ∧ IsAttemptData c₂ (Bf ℓ) G J N (M ℓ)
      (roots ℓ) (seg ℓ) (n ℓ) (a ℓ) (cnt ℓ) (atm ℓ) ∧ IsFitOpponent G J N (f (stagPos
      ℓ)) (roots ℓ) (seg ℓ) (g ℓ) (fitOpponentConst (M ℓ)) (max (2 : ℝ) (↑(M ℓ) : ℝ)) c₂
      (Bf ℓ))
    (u : ℕ)
    (t : ℕ)
    (hut : u < t)
    (Hc : ℝ)
    (Mt : ℕ)
    (_ : ∀ ℓ ≤ t, M ℓ ≤ Mt)
    (η₀ : ℝ)
    (_ : (0 : ℝ) ≤ η₀)
    (_ : ∀ I ∈ dyadicFiniteTree G J N, kernelHull G J N w I → ∀ (s s' : Fin (4 : ℕ)), s ≠ s'
      → PairSmall (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1) (w I) s s'
      (stagTuple f g u t I s) (stagTuple f g u t I s') η₀)
    (_ : ∀ I ∈ dyadicFiniteTree G J N, kernelHull G J N w I → ∀ (l : Fin (4 : ℕ)), eLpNorm
      (stagTuple f g u t I l) (2 : ℝ≥0∞) (normalizedIntervalMeasure (dyadicGridLeft G
      I.1 I.2) (dyadicGridLength G I.1)) ≤ ENNReal.ofReal (2 : ℝ))
    (Bp : ℝ)
    (ε : ℝ)
    (K₀ : ℕ)
    (ka : ℕ)
    (kb : ℕ)
    (Ma : ℕ)
    (Mb : ℕ)
    (_ : (0 : ℝ) < ε)
    (_ : ε ≤ (1 : ℝ)),
  let H : ℝ :=
    max Hc Wp ^ (6 : ℕ)
  let D : ℝ :=
    max H (Real.exp ((↑C₁ : ℝ) * ((1 : ℝ) + Bp + Real.log H) ^ C₁))
  let Wa : ℕ :=
    (2 : ℕ) * Mt * ((2 : ℕ) * Mt) * ⌊D⌋₊ + Ma
  let Wb : ℕ :=
    (2 : ℕ) * Mt * ((2 : ℕ) * Mt) * ⌊D⌋₊ + Mb
  let E : ℝ :=
    baseErr κ ((2 : ℕ) * Mt) ((2 : ℕ) * Mt) D Bp ε K₀ Wa Wb (fitOpponentConst Mt)
      (fitOpponentConst Mt)
  let S₀ : ℝ :=
    (1 : ℝ) + (6 : ℝ) * (↑Mt : ℝ)
  let Sp : ℝ :=
    (↑Wa : ℝ) * √((2 : ℝ) ^ K₀ / ε) + (1 : ℝ)
  let i : Fin (4 : ℕ) :=
    stagPos u
  let k : Fin (4 : ℕ) :=
    stagPos t
  ∀ (_ : i ≠ k)
    (sa : Fin (4 : ℕ))
    (sb : Fin (4 : ℕ))
    (_ : sa ≠ sb)
    (_ : sa ≠ i)
    (_ : sa ≠ k)
    (_ : sb ≠ i)
    (_ : sb ≠ k),
  let la : ℕ :=
    StaggerCell.lastLevel sa t
  ∀ (hla2 : la < t),
  let lb : ℕ :=
    StaggerCell.lastLevel sb t
  ∀ (hlb2 : lb < t),
  let Lset : Finset ℕ :=
    {u, u - (4 : ℕ), t, t - (4 : ℕ), la, lb}
  ∀ (hLne : Lset.Nonempty)
    (_ : SegData G J N seg Lset),
  let Rf : ℤ × ℤ → ℤ × ℤ :=
    firstRoot seg Lset hLne
  let Tup : Finset (ℤ × ℤ) :=
    {I ∈ dyadicFiniteTree G J N | I.1 + (↑K₀ : ℤ) ≤ J.1 + (↑N : ℤ) ∧ kernelHull G J N w
      I}
  let Rs : Finset (ℤ × ℤ) :=
    Finset.image Rf Tup
  ∀ (hRtree : ∀ I ∈ dyadicFiniteTree G J N, Rf I ∈ dyadicFiniteTree G J N ∧ dyadicGridCell G I.1
      I.2 ⊆ dyadicGridCell G (Rf I).1 (Rf I).2)
    (hRsT : ∀ R ∈ Rs, R ∈ dyadicFiniteTree G J N)
    (hHl : ∀ ℓ ≤ t, max (Bf ℓ) Wp ^ (6 : ℕ) ≤ H)
    (_ : (1 : ℝ) ≤ H)
    (_ : Wp ≤ H)
    (X : (ℓ : ℕ) → (R : ℤ × ℤ) → R ∈ dyadicFiniteTree G J N → LowList G J N R (max c₂ cp)
      (max (Bf ℓ) Wp ^ (6 : ℕ))),
  let Y : (ℓ : ℕ) → ℓ ≤ t → (R : ℤ × ℤ) → R ∈ dyadicFiniteTree G J N → LowList G J N R (max c₂
      cp) H :=
    fun ℓ hℓ R hR => (X ℓ R hR).mono le_rfl (hHl ℓ hℓ)
  ∀ (_ : ∀ (ℓ : ℕ) (hℓ : ℓ ≤ t) (R : ℤ × ℤ) (hR : R ∈ dyadicFiniteTree G J N), ∀ I ∈
      dyadicFiniteTree G J N, dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G R.1 R.2 → seg
      ℓ I = seg ℓ R → kernelHull G J N w I → ∀ (y : ℝ), (Y ℓ hℓ R hR).val I y = g ℓ I y)
    (hu4 : u - (4 : ℕ) ≤ t)
    (ht4 : t - (4 : ℕ) ≤ t),
  let Xi : (R : ℤ × ℤ) → R ∈ dyadicFiniteTree G J N → LowList G J N R (max c₂ cp) H :=
    fun R hR => if u ≤ 4 then Y u hut.le R hR else (Y u hut.le R hR).sub (Y (u - 4) hu4
      R hR)
  let Xk : (R : ℤ × ℤ) → R ∈ dyadicFiniteTree G J N → LowList G J N R (max c₂ cp) H :=
    fun R hR => if t ≤ 4 then Y t le_rfl R hR else (Y t le_rfl R hR).sub (Y (t - 4) ht4
      R hR)
  let Xga : (R : ℤ × ℤ) → R ∈ dyadicFiniteTree G J N → LowList G J N R (max c₂ cp) H :=
    fun R hR => if 1 ≤ la then Y la hla2.le R hR else LowList.empty
  let Xgb : (R : ℤ × ℤ) → R ∈ dyadicFiniteTree G J N → LowList G J N R (max c₂ cp) H :=
    fun R hR => if 1 ≤ lb then Y lb hlb2.le R hR else LowList.empty
  ∀ (_ : u ∈ Lset)
    (_ : u - (4 : ℕ) ∈ Lset)
    (_ : t ∈ Lset)
    (_ : t - (4 : ℕ) ∈ Lset)
    (_ : la ∈ Lset)
    (_ : lb ∈ Lset)
    (_ : ∀ I ∈ dyadicFiniteTree G J N, ∀ ℓ ∈ Lset, seg ℓ I = seg ℓ (Rf I))
    (_ : ∀ (I : ℤ × ℤ) (hI : I ∈ dyadicFiniteTree G J N), kernelHull G J N w I → slots4 sa i
      k (f sa - (Xga (Rf I) (hRtree I hI).left).val I) ((Xi (Rf I) (hRtree I
      hI).left).val I) ((Xk (Rf I) (hRtree I hI).left).val I) (f sb - (Xgb (Rf I)
      (hRtree I hI).left).val I) = stagTuple f g u t I)
    (_ : ∀ (I : ℤ × ℤ) (hI : I ∈ dyadicFiniteTree G J N), kernelHull G J N w I → (Xga (Rf I)
      (hRtree I hI).left).val I = if (1 : ℕ) ≤ la then g la I else (0 : ℝ → ℂ))
    (_ : ∀ (I : ℤ × ℤ) (hI : I ∈ dyadicFiniteTree G J N), kernelHull G J N w I → (Xgb (Rf I)
      (hRtree I hI).left).val I = if (1 : ℕ) ≤ lb then g lb I else (0 : ℝ → ℂ))
    (z : ℕ → (R : ℤ × ℤ) → R ∈ dyadicFiniteTree G J N → ℤ × ℤ → ℝ → ℂ)
    (_ : ∀ (ℓ : ℕ) (R : ℤ × ℤ) (hR : R ∈ dyadicFiniteTree G J N), ∀ I ∈ dyadicFiniteTree G J
      N, seg ℓ I = seg ℓ R → ∀ᵐ (y : ℝ), y ∈ dyadicGridCell G I.1 I.2 → z ℓ R hR I y = g
      ℓ I y),
  let BdR : (R : ℤ × ℤ) → R ∈ dyadicFiniteTree G J N → ℝ :=
    fun (R : ℤ × ℤ) (hR : R ∈ dyadicFiniteTree G J N) => (2 : ℝ) + (↑(Fintype.card (Xi R
      hR).Λ + Fintype.card (Xk R hR).Λ + Fintype.card (Xga R hR).Λ + Fintype.card (Xgb R
      hR).Λ) : ℝ)
  ∀ (_ : ∀ (R : ℤ × ℤ) (hR : R ∈ dyadicFiniteTree G J N), IsBasicOn G R (dyadicRemainingDepth
      J N R) (1 : ℝ) (BdR R hR) (max c₂ cp) H w (z u R hR))
    (_ : ∀ (R : ℤ × ℤ) (hR : R ∈ dyadicFiniteTree G J N), ¬u ≤ (4 : ℕ) → IsBasicOn G R
      (dyadicRemainingDepth J N R) (1 : ℝ) (BdR R hR) (max c₂ cp) H w (z (u - (4 : ℕ)) R
      hR))
    (_ : ∀ (R : ℤ × ℤ) (hR : R ∈ dyadicFiniteTree G J N), IsBasicOn G R (dyadicRemainingDepth
      J N R) (1 : ℝ) (BdR R hR) (max c₂ cp) H w (z t R hR))
    (_ : ∀ (R : ℤ × ℤ) (hR : R ∈ dyadicFiniteTree G J N), ¬t ≤ (4 : ℕ) → IsBasicOn G R
      (dyadicRemainingDepth J N R) (1 : ℝ) (BdR R hR) (max c₂ cp) H w (z (t - (4 : ℕ)) R
      hR))
    (z0 : (R : ℤ × ℤ) → R ∈ dyadicFiniteTree G J N → ℤ × ℤ → ℝ → ℂ)
    (_ : ∀ (R : ℤ × ℤ) (hR : R ∈ dyadicFiniteTree G J N) (I : ℤ × ℤ), ∀ᵐ (y : ℝ), z0 R hR I y
      = (0 : ℂ))
    (_ : ∀ (R : ℤ × ℤ) (hR : R ∈ dyadicFiniteTree G J N), IsBasicOn G R (dyadicRemainingDepth
      J N R) (1 : ℝ) (BdR R hR) (max c₂ cp) H w (z0 R hR)),
  let za : (R : ℤ × ℤ) → R ∈ dyadicFiniteTree G J N → ℤ × ℤ → ℝ → ℂ :=
    fun (R : ℤ × ℤ) (hR : R ∈ dyadicFiniteTree G J N) => if (1 : ℕ) ≤ la then z la R hR
      else z0 R hR
  let zb : (R : ℤ × ℤ) → R ∈ dyadicFiniteTree G J N → ℤ × ℤ → ℝ → ℂ :=
    fun (R : ℤ × ℤ) (hR : R ∈ dyadicFiniteTree G J N) => if (1 : ℕ) ≤ lb then z lb R hR
      else z0 R hR
  ∀ (_ : ∀ (R : ℤ × ℤ) (hR : R ∈ dyadicFiniteTree G J N), IsBasicOn G R (dyadicRemainingDepth
      J N R) (1 : ℝ) (BdR R hR) (max c₂ cp) H w (za R hR))
    (_ : ∀ (R : ℤ × ℤ) (hR : R ∈ dyadicFiniteTree G J N), IsBasicOn G R (dyadicRemainingDepth
      J N R) (1 : ℝ) (BdR R hR) (max c₂ cp) H w (zb R hR))
    (P : (R : ℤ × ℤ) → R ∈ Rs → Finset ((ℤ × ℤ) × ℤ × ℤ))
    (A : (R : ℤ × ℤ) → (hR : R ∈ Rs) → ↥(P R hR) → ActiveSetup κ (max (max c₁ (max c₂ cp))
      c₂a))
    (_ : ∀ (R : ℤ × ℤ) (hR : R ∈ Rs), ∑ p : ↥(P R hR), dyadicGridLength G (A R hR p).R.1 ≤ (8
      / 3 : ℝ) * dyadicGridLength G R.1 ∧ (∀ I ∈ {I ∈ Tup | Rf I = R}, ∃ (p : ↥(P R
      hR)), I ∈ (A R hR p).cells) ∧ (∀ (p p' : ↥(P R hR)), ∀ I ∈ (A R hR p).cells, I ∈
      (A R hR p').cells → p = p') ∧ ∀ (p : ↥(P R hR)), (A R hR p).cells ⊆ {I ∈ Tup | Rf
      I = R} ∧ (∀ I ∈ (A R hR p).cells, ∀ J' ∈ {I ∈ Tup | Rf I = R}, dyadicGridCell G
      I.1 I.2 ⊆ dyadicGridCell G J'.1 J'.2 → dyadicGridCell G J'.1 J'.2 ⊆ dyadicGridCell
      G (A R hR p).R.1 (A R hR p).R.2 → J' ∈ (A R hR p).cells) ∧ (A R hR p).G = G ∧ (A R
      hR p).w = w ∧ (A R hR p).a = sa ∧ (A R hR p).b = sb ∧ (A R hR p).R ∈
      dyadicFiniteTree G J N ∧ dyadicGridCell G (A R hR p).R.1 (A R hR p).R.2 ⊆
      dyadicGridCell G R.1 R.2 ∧ (A R hR p).H = max (max H (Real.exp ((↑C₁ : ℝ) * ((1 :
      ℝ) + Bp + Real.log H) ^ C₁))) (max (fitBudget Cqa Ca ka) (fitBudget Cqa Ca kb)) ∧
      (A R hR p).Dc = √ε⁻¹ ∧ (A R hR p).S = (2 : ℝ) ∧ (A R hR p).η = (4 : ℝ) * η₀ ∧
      Fintype.card (A R hR p).L = Fintype.card (Xi R (hRsT R hR)).Λ + Fintype.card (Xk R
      (hRsT R hR)).Λ + (Fintype.card (Xi R (hRsT R hR)).Λ * Fintype.card (Xk R (hRsT R
      hR)).Λ * ⌊max H (Real.exp ((↑C₁ : ℝ) * ((1 : ℝ) + Bp + Real.log H) ^ C₁))⌋₊ + Ma +
      Fintype.card (Xga R (hRsT R hR)).Λ) + (Fintype.card (Xi R (hRsT R hR)).Λ *
      Fintype.card (Xk R (hRsT R hR)).Λ * ⌊max H (Real.exp ((↑C₁ : ℝ) * ((1 : ℝ) + Bp +
      Real.log H) ^ C₁))⌋₊ + Mb + Fintype.card (Xgb R (hRsT R hR)).Λ) ∧ ∑ I ∈ (A R hR
      p).cells, dyadicGridLength G I.1 * ‖localProgressionForm (dyadicGridLength G I.1)
      (w I) (slots4 sa i k (f sa - (Xga R (hRsT R hR)).val I) ((Xi R (hRsT R hR)).val I)
      ((Xk R (hRsT R hR)).val I) (f sb - (Xgb R (hRsT R hR)).val I)) - (A R hR p).Hf I
      ((A R hR p).Y I)‖ ≤ baseErr κ (Fintype.card (Xi R (hRsT R hR)).Λ) (Fintype.card
      (Xk R (hRsT R hR)).Λ) (max H (Real.exp ((↑C₁ : ℝ) * ((1 : ℝ) + Bp + Real.log H) ^
      C₁))) Bp ε K₀ (Fintype.card (Xi R (hRsT R hR)).Λ * Fintype.card (Xk R (hRsT R
      hR)).Λ * ⌊max H (Real.exp ((↑C₁ : ℝ) * ((1 : ℝ) + Bp + Real.log H) ^ C₁))⌋₊ + Ma)
      (Fintype.card (Xi R (hRsT R hR)).Λ * Fintype.card (Xk R (hRsT R hR)).Λ * ⌊max H
      (Real.exp ((↑C₁ : ℝ) * ((1 : ℝ) + Bp + Real.log H) ^ C₁))⌋₊ + Mb)
      (fitOpponentConst (M la)) (fitOpponentConst (M lb)) * dyadicGridLength G (A R hR
      p).R.1 ∧ (∀ I ∈ (A R hR p).cells, ∀ (s s' : Fin (4 : ℕ)), s ≠ s' → PairSmall
      (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1) (w I) s s' ((A R hR p).Y I s)
      ((A R hR p).Y I s') (η₀ + ((2 : ℝ) + (2 : ℝ) * ((1 : ℝ) + (↑(Fintype.card (Xi R
      (hRsT R hR)).Λ) : ℝ) + (↑(Fintype.card (Xk R (hRsT R hR)).Λ) : ℝ) +
      (↑(Fintype.card (Xga R (hRsT R hR)).Λ) : ℝ) + (↑(Fintype.card (Xgb R (hRsT R
      hR)).Λ) : ℝ))) * (Real.exp (-(↑ka : ℝ)) + Real.exp (-(↑kb : ℝ))) + ((1 : ℝ) +
      ((↑(Fintype.card (Xi R (hRsT R hR)).Λ * Fintype.card (Xk R (hRsT R hR)).Λ * ⌊max H
      (Real.exp ((↑C₁ : ℝ) * ((1 : ℝ) + Bp + Real.log H) ^ C₁))⌋₊ + Ma) : ℝ) * √((2 : ℝ)
      ^ K₀ / ε) + (1 : ℝ))) * Real.exp (-(↑kb : ℝ)))) ∧ (∀ I ∈ (A R hR p).cells, ∀ (l :
      Fin (4 : ℕ)), (eLpNorm ((A R hR p).Y I l) (2 : ℝ≥0∞) ((A R hR p).μ I)).toReal ≤ (2
      : ℝ)) ∧ (∀ (l : Fin (4 : ℕ)), ∑ I ∈ (A R hR p).cells, dyadicGridLength G I.1 *
      (eLpNorm ((A R hR p).U l I) (2 : ℝ≥0∞) ((A R hR p).μ I)).toReal ^ (2 : ℕ) ≤ (↑K₀ :
      ℝ) ^ (2 : ℕ) * dyadicGridLength G (A R hR p).R.1) ∧ ∑ I ∈ (A R hR p).cells,
      dyadicGridLength G I.1 * ‖(A R hR p).Hf I ((A R hR p).z (3 : Fin (4 : ℕ)) I)‖ ≤ η₀
      * ((↑K₀ : ℝ) ^ (2 : ℕ) * dyadicGridLength G (A R hR p).R.1) ∧ (A R hR
      p).HasColumnRep (1 : ℝ) ∧ (A R hR p).SubRootProps η₀ ((↑K₀ : ℝ) ^ (2 : ℕ)))
    (_ : ∀ (T : Finset (ℤ × ℤ)), (∀ I ∈ T, I ∈ dyadicFiniteTree G J N) → ∑ R ∈ Finset.image
      Rf T, dyadicGridLength G R.1 ≤ (8 : ℝ) * dyadicGridLength G J.1),
  let ιt : Type :=
    Σ R : Rs, (P R.1 R.2)
  let A' : ιt → ActiveSetup κ (max (max c₁ (max c₂ cp)) c₂a) :=
    fun x => A x.1.1 x.1.2 x.2
  ∀ (_ : ∀ (R : ℤ × ℤ) (hR : R ∈ Rs) (p : ↥(P R hR)), ∀ I ∈ (A R hR p).cells, I ∈
      dyadicFiniteTree G J N ∧ I.1 + (↑K₀ : ℤ) ≤ J.1 + (↑N : ℤ) ∧ Rf I = R ∧ kernelHull
      G J N w I)
    (_ : ∀ (R : ℤ × ℤ) (hRT : R ∈ dyadicFiniteTree G J N), Fintype.card (Xi R hRT).Λ ≤ (2 :
      ℕ) * Mt ∧ Fintype.card (Xk R hRT).Λ ≤ (2 : ℕ) * Mt ∧ Fintype.card (Xga R hRT).Λ ≤
      Mt ∧ Fintype.card (Xgb R hRT).Λ ≤ Mt ∧ Fintype.card (Xi R hRT).Λ * Fintype.card
      (Xk R hRT).Λ * ⌊D⌋₊ + Ma ≤ Wa ∧ Fintype.card (Xi R hRT).Λ * Fintype.card (Xk R
      hRT).Λ * ⌊D⌋₊ + Mb ≤ Wb)
    (_ : ∑ x : ιt, dyadicGridLength G (A' x).R.1 ≤ (64 / 3 : ℝ) * dyadicGridLength G J.1),
  let d₀ : ℤ :=
    J.1 + (↑N : ℤ) + (1 : ℤ) - (↑K₀ : ℤ)
  let Bot : Finset (ℤ × ℤ) :=
    {I ∈ dyadicFiniteTree G J N | ¬I.1 + (↑K₀ : ℤ) ≤ J.1 + (↑N : ℤ) ∧ kernelHull G J N w
      I}
  ∀ (_ : Bot = {I ∈ dyadicFiniteTree G J N | ¬I.1 + (↑K₀ : ℤ) ≤ J.1 + (↑N : ℤ) ∧ kernelHull G
      J N w I})
    (_ : ∀ I ∈ Bot, I ∈ dyadicFiniteTree G J N ∧ d₀ ≤ I.1 ∧ kernelHull G J N w I),
  let anc : ℤ × ℤ → ℤ × ℤ :=
    fun I => if h : d₀ ≤ I.1 then (d₀, Classical.choose (dyadicGridCell_ancestor G h
      I.2)) else I
  ∀ (_ : ∀ (I : ℤ × ℤ), d₀ ≤ I.1 → (anc I).1 = d₀ ∧ dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell
      G (anc I).1 (anc I).2),
  let Rb : ℤ × ℤ → ℤ × ℤ :=
    fun (I : ℤ × ℤ) => if d₀ ≤ (Rf I).1 then Rf I else anc I
  ∀ (_ : ∀ I ∈ dyadicFiniteTree G J N, d₀ ≤ I.1 → Rb I ∈ dyadicFiniteTree G J N ∧ d₀ ≤ (Rb
      I).1 ∧ dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G (Rb I).1 (Rb I).2 ∧
      dyadicGridCell G (Rb I).1 (Rb I).2 ⊆ dyadicGridCell G (Rf I).1 (Rf I).2),
  ∃ (ι : Type) (_ : Fintype ι) (A : ι → ActiveSetup κ (max (max c₁ (max c₂ cp)) c₂a)),
    ∑ p : ι, dyadicGridLength G (A p).R.1 ≤ (91 / 3 : ℝ) * dyadicGridLength G J.1 ∧ (∀
    (p p' : ι), ∀ I ∈ (A p).cells, I ∈ (A p').cells → p = p') ∧ (∀ (p : ι), (A
    p).cells ⊆ dyadicFiniteTree G J N ∧ (∀ I ∈ (A p).cells, kernelHull G J N w I) ∧ (∀
    I ∈ (A p).cells, ∀ (J' : ℤ × ℤ), dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G J'.1
    J'.2 → dyadicGridCell G J'.1 J'.2 ⊆ dyadicGridCell G (A p).R.1 (A p).R.2 → J' ∈ (A
    p).cells) ∧ (A p).G = G ∧ (A p).w = w ∧ (A p).R ∈ dyadicFiniteTree G J N ∧ (A p).H
    = max D (max (fitBudget Cqa Ca ka) (fitBudget Cqa Ca kb)) ∧ (A p).Dc = √ε⁻¹ ∧ (A
    p).S = (2 : ℝ) ∧ (A p).η = (4 : ℝ) * η₀ ∧ Fintype.card (A p).L ≤ (6 : ℕ) * Mt + Wa
    + Wb ∧ (∀ I ∈ (A p).cells, ∀ (s s' : Fin (4 : ℕ)), s ≠ s' → PairSmall
    (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1) (w I) s s' ((A p).Y I s) ((A
    p).Y I s') (η₀ + ((2 : ℝ) + (2 : ℝ) * S₀) * (Real.exp (-(↑ka : ℝ)) + Real.exp
    (-(↑kb : ℝ))) + ((1 : ℝ) + Sp) * Real.exp (-(↑kb : ℝ)))) ∧ (∀ I ∈ (A p).cells, ∀
    (l : Fin (4 : ℕ)), (eLpNorm ((A p).Y I l) (2 : ℝ≥0∞) ((A p).μ I)).toReal ≤ (2 :
    ℝ)) ∧ (∀ (l : Fin (4 : ℕ)), ∑ I ∈ (A p).cells, dyadicGridLength G I.1 * (eLpNorm
    ((A p).U l I) (2 : ℝ≥0∞) ((A p).μ I)).toReal ^ (2 : ℕ) ≤ (↑K₀ : ℝ) ^ (2 : ℕ) *
    dyadicGridLength G (A p).R.1) ∧ ∑ I ∈ (A p).cells, dyadicGridLength G I.1 * ‖(A
    p).Hf I ((A p).z (3 : Fin (4 : ℕ)) I)‖ ≤ η₀ * ((↑K₀ : ℝ) ^ (2 : ℕ) *
    dyadicGridLength G (A p).R.1) ∧ (A p).HasColumnRep (1 : ℝ) ∧ (A p).SubRootProps η₀
    ((↑K₀ : ℝ) ^ (2 : ℕ))) ∧ ∑ I ∈ dyadicFiniteTree G J N, dyadicGridLength G I.1 *
    ‖localProgressionForm (dyadicGridLength G I.1) (w I) (stagTuple f g u t I)‖ ≤ ∑ p
    : ι, ∑ I ∈ (A p).cells, dyadicGridLength G I.1 * ‖(A p).Hf I ((A p).Y I)‖ + E *
    ((91 / 3 : ℝ) * dyadicGridLength G J.1)

open scoped Classical in
private def BaseTupleStage3Statement : Prop :=
  ∀ (κ : LocalKernelClass)
    (c₂ : ℕ)
    (cp : ℕ)
    (Wp : ℝ)
    (_ : ∀ (c : ℕ) (H' : ℝ), cp ≤ c → Wp ≤ H' → ∃ (d : ℕ) (Φ : QuadraticChartData d), (1 : ℕ)
      ≤ d ∧ QuadraticChartComplexity c H' Φ ∧ IsBoundedQuadraticChart Φ)
    (c₁ : ℕ)
    (C₁ : ℕ)
    (c₂a : ℕ)
    (Ca : ℕ)
    (q : ℝ)
    (_ : (2 : ℝ) < q)
    (Cqa : ℝ)
    (G : RealDyadicGrid)
    (J : ℤ × ℤ)
    (N : ℕ)
    (w : ℤ × ℤ → ℝ × ℝ → ℂ)
    (_ : ∀ (I : ℤ × ℤ), IsAdmissibleLocalKernel κ (dyadicGridLeft G I.1 I.2)
      (dyadicGridLength G I.1) (w I))
    (f : Fin (4 : ℕ) → ℝ → ℂ)
    (_ : ∀ (l : Fin (4 : ℕ)), Measurable (f l))
    (_ : ∀ (l : Fin (4 : ℕ)), ∀ I ∈ dyadicFiniteTree G J N, I = J ∨ kernelHull G J N w I →
      eLpNorm (f l) (ENNReal.ofReal q) (normalizedIntervalMeasure (dyadicGridLeft G I.1
      I.2) (dyadicGridLength G I.1)) ≤ (1 : ℝ≥0∞))
    (Bf : ℕ → ℝ)
    (kk : ℕ → ℕ)
    (M : ℕ → ℕ)
    (roots : ℕ → Finset (ℤ × ℤ))
    (seg : ℕ → ℤ × ℤ → ℤ × ℤ)
    (n : ℕ → ℤ × ℤ → ℕ)
    (a : ℕ → ℤ × ℤ → ℕ → ℝ → ℂ)
    (g : ℕ → ℤ × ℤ → ℝ → ℂ)
    (cnt : ℕ → ℤ × ℤ → ℤ × ℤ → ℕ)
    (atm : ℕ → ℤ × ℤ → ℤ × ℤ → ℕ → ℝ → ℂ)
    (_ : ∀ (ℓ : ℕ), IsAdaptiveFit c₂ (Bf ℓ) G J N w (stagPos ℓ) q (f (stagPos ℓ)) (kk ℓ) (M
      ℓ) (roots ℓ) (seg ℓ) (n ℓ) (a ℓ) (g ℓ) ∧ IsAttemptData c₂ (Bf ℓ) G J N (M ℓ)
      (roots ℓ) (seg ℓ) (n ℓ) (a ℓ) (cnt ℓ) (atm ℓ) ∧ IsFitOpponent G J N (f (stagPos
      ℓ)) (roots ℓ) (seg ℓ) (g ℓ) (fitOpponentConst (M ℓ)) (max (2 : ℝ) (↑(M ℓ) : ℝ)) c₂
      (Bf ℓ))
    (u : ℕ)
    (t : ℕ)
    (hut : u < t)
    (Hc : ℝ)
    (Mt : ℕ)
    (_ : ∀ ℓ ≤ t, M ℓ ≤ Mt)
    (η₀ : ℝ)
    (_ : (0 : ℝ) ≤ η₀)
    (_ : ∀ I ∈ dyadicFiniteTree G J N, kernelHull G J N w I → ∀ (s s' : Fin (4 : ℕ)), s ≠ s'
      → PairSmall (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1) (w I) s s'
      (stagTuple f g u t I s) (stagTuple f g u t I s') η₀)
    (_ : ∀ I ∈ dyadicFiniteTree G J N, kernelHull G J N w I → ∀ (l : Fin (4 : ℕ)), eLpNorm
      (stagTuple f g u t I l) (2 : ℝ≥0∞) (normalizedIntervalMeasure (dyadicGridLeft G
      I.1 I.2) (dyadicGridLength G I.1)) ≤ ENNReal.ofReal (2 : ℝ))
    (Bp : ℝ)
    (ε : ℝ)
    (K₀ : ℕ)
    (ka : ℕ)
    (kb : ℕ)
    (Ma : ℕ)
    (Mb : ℕ)
    (_ : (0 : ℝ) < ε)
    (_ : ε ≤ (1 : ℝ)),
  let H : ℝ :=
    max Hc Wp ^ (6 : ℕ)
  let D : ℝ :=
    max H (Real.exp ((↑C₁ : ℝ) * ((1 : ℝ) + Bp + Real.log H) ^ C₁))
  let Wa : ℕ :=
    (2 : ℕ) * Mt * ((2 : ℕ) * Mt) * ⌊D⌋₊ + Ma
  let Wb : ℕ :=
    (2 : ℕ) * Mt * ((2 : ℕ) * Mt) * ⌊D⌋₊ + Mb
  let E : ℝ :=
    baseErr κ ((2 : ℕ) * Mt) ((2 : ℕ) * Mt) D Bp ε K₀ Wa Wb (fitOpponentConst Mt)
      (fitOpponentConst Mt)
  let S₀ : ℝ :=
    (1 : ℝ) + (6 : ℝ) * (↑Mt : ℝ)
  let Sp : ℝ :=
    (↑Wa : ℝ) * √((2 : ℝ) ^ K₀ / ε) + (1 : ℝ)
  let i : Fin (4 : ℕ) :=
    stagPos u
  let k : Fin (4 : ℕ) :=
    stagPos t
  ∀ (_ : i ≠ k)
    (sa : Fin (4 : ℕ))
    (sb : Fin (4 : ℕ))
    (_ : sa ≠ sb)
    (_ : sa ≠ i)
    (_ : sa ≠ k)
    (_ : sb ≠ i)
    (_ : sb ≠ k),
  let la : ℕ :=
    StaggerCell.lastLevel sa t
  ∀ (hla2 : la < t),
  let lb : ℕ :=
    StaggerCell.lastLevel sb t
  ∀ (hlb2 : lb < t),
  let Lset : Finset ℕ :=
    {u, u - (4 : ℕ), t, t - (4 : ℕ), la, lb}
  ∀ (_ : Lset = {u, u - (4 : ℕ), t, t - (4 : ℕ), la, lb})
    (hLne : Lset.Nonempty)
    (_ : SegData G J N seg Lset),
  let Rf : ℤ × ℤ → ℤ × ℤ :=
    firstRoot seg Lset hLne
  let Tup : Finset (ℤ × ℤ) :=
    {I ∈ dyadicFiniteTree G J N | I.1 + (↑K₀ : ℤ) ≤ J.1 + (↑N : ℤ) ∧ kernelHull G J N w
      I}
  let Rs : Finset (ℤ × ℤ) :=
    Finset.image Rf Tup
  ∀ (hRtree : ∀ I ∈ dyadicFiniteTree G J N, Rf I ∈ dyadicFiniteTree G J N ∧ dyadicGridCell G I.1
      I.2 ⊆ dyadicGridCell G (Rf I).1 (Rf I).2)
    (hRsT : ∀ R ∈ Rs, R ∈ dyadicFiniteTree G J N)
    (hHl : ∀ ℓ ≤ t, max (Bf ℓ) Wp ^ (6 : ℕ) ≤ H)
    (_ : (1 : ℝ) ≤ H)
    (_ : Wp ≤ H)
    (X : (ℓ : ℕ) → (R : ℤ × ℤ) → R ∈ dyadicFiniteTree G J N → LowList G J N R (max c₂ cp)
      (max (Bf ℓ) Wp ^ (6 : ℕ))),
  let Y : (ℓ : ℕ) → ℓ ≤ t → (R : ℤ × ℤ) → R ∈ dyadicFiniteTree G J N → LowList G J N R (max c₂
      cp) H :=
    fun ℓ hℓ R hR => (X ℓ R hR).mono le_rfl (hHl ℓ hℓ)
  ∀ (_ : ∀ (ℓ : ℕ) (hℓ : ℓ ≤ t) (R : ℤ × ℤ) (hR : R ∈ dyadicFiniteTree G J N), ∀ I ∈
      dyadicFiniteTree G J N, dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G R.1 R.2 → seg
      ℓ I = seg ℓ R → kernelHull G J N w I → ∀ (y : ℝ), (Y ℓ hℓ R hR).val I y = g ℓ I y)
    (_ : ∀ (ℓ : ℕ) (hℓ : ℓ ≤ t) (R : ℤ × ℤ) (hR : R ∈ dyadicFiniteTree G J N), Fintype.card
      (Y ℓ hℓ R hR).Λ = M ℓ)
    (hu4 : u - (4 : ℕ) ≤ t)
    (ht4 : t - (4 : ℕ) ≤ t),
  let Xi : (R : ℤ × ℤ) → R ∈ dyadicFiniteTree G J N → LowList G J N R (max c₂ cp) H :=
    fun R hR => if u ≤ 4 then Y u hut.le R hR else (Y u hut.le R hR).sub (Y (u - 4) hu4
      R hR)
  let Xk : (R : ℤ × ℤ) → R ∈ dyadicFiniteTree G J N → LowList G J N R (max c₂ cp) H :=
    fun R hR => if t ≤ 4 then Y t le_rfl R hR else (Y t le_rfl R hR).sub (Y (t - 4) ht4
      R hR)
  let Xga : (R : ℤ × ℤ) → R ∈ dyadicFiniteTree G J N → LowList G J N R (max c₂ cp) H :=
    fun R hR => if 1 ≤ la then Y la hla2.le R hR else LowList.empty
  let Xgb : (R : ℤ × ℤ) → R ∈ dyadicFiniteTree G J N → LowList G J N R (max c₂ cp) H :=
    fun R hR => if 1 ≤ lb then Y lb hlb2.le R hR else LowList.empty
  ∀ (_ : u ∈ Lset)
    (_ : u - (4 : ℕ) ∈ Lset)
    (_ : t ∈ Lset)
    (_ : t - (4 : ℕ) ∈ Lset)
    (_ : la ∈ Lset)
    (_ : lb ∈ Lset)
    (_ : ∀ I ∈ dyadicFiniteTree G J N, ∀ ℓ ∈ Lset, seg ℓ I = seg ℓ (Rf I))
    (_ : ∀ (I : ℤ × ℤ) (hI : I ∈ dyadicFiniteTree G J N), kernelHull G J N w I → slots4 sa i
      k (f sa - (Xga (Rf I) (hRtree I hI).left).val I) ((Xi (Rf I) (hRtree I
      hI).left).val I) ((Xk (Rf I) (hRtree I hI).left).val I) (f sb - (Xgb (Rf I)
      (hRtree I hI).left).val I) = stagTuple f g u t I)
    (_ : ∀ (I : ℤ × ℤ) (hI : I ∈ dyadicFiniteTree G J N), kernelHull G J N w I → (Xga (Rf I)
      (hRtree I hI).left).val I = if (1 : ℕ) ≤ la then g la I else (0 : ℝ → ℂ))
    (_ : ∀ (I : ℤ × ℤ) (hI : I ∈ dyadicFiniteTree G J N), kernelHull G J N w I → (Xgb (Rf I)
      (hRtree I hI).left).val I = if (1 : ℕ) ≤ lb then g lb I else (0 : ℝ → ℂ))
    (z : ℕ → (R : ℤ × ℤ) → R ∈ dyadicFiniteTree G J N → ℤ × ℤ → ℝ → ℂ)
    (_ : ∀ (ℓ : ℕ) (R : ℤ × ℤ) (hR : R ∈ dyadicFiniteTree G J N), ∀ I ∈ dyadicFiniteTree G J
      N, seg ℓ I = seg ℓ R → ∀ᵐ (y : ℝ), y ∈ dyadicGridCell G I.1 I.2 → z ℓ R hR I y = g
      ℓ I y),
  let BdR : (R : ℤ × ℤ) → R ∈ dyadicFiniteTree G J N → ℝ :=
    fun (R : ℤ × ℤ) (hR : R ∈ dyadicFiniteTree G J N) => (2 : ℝ) + (↑(Fintype.card (Xi R
      hR).Λ + Fintype.card (Xk R hR).Λ + Fintype.card (Xga R hR).Λ + Fintype.card (Xgb R
      hR).Λ) : ℝ)
  ∀ (_ : ∀ (R : ℤ × ℤ) (hR : R ∈ dyadicFiniteTree G J N), IsBasicOn G R (dyadicRemainingDepth
      J N R) (1 : ℝ) (BdR R hR) (max c₂ cp) H w (z u R hR))
    (_ : ∀ (R : ℤ × ℤ) (hR : R ∈ dyadicFiniteTree G J N), ¬u ≤ (4 : ℕ) → IsBasicOn G R
      (dyadicRemainingDepth J N R) (1 : ℝ) (BdR R hR) (max c₂ cp) H w (z (u - (4 : ℕ)) R
      hR))
    (_ : ∀ (R : ℤ × ℤ) (hR : R ∈ dyadicFiniteTree G J N), IsBasicOn G R (dyadicRemainingDepth
      J N R) (1 : ℝ) (BdR R hR) (max c₂ cp) H w (z t R hR))
    (_ : ∀ (R : ℤ × ℤ) (hR : R ∈ dyadicFiniteTree G J N), ¬t ≤ (4 : ℕ) → IsBasicOn G R
      (dyadicRemainingDepth J N R) (1 : ℝ) (BdR R hR) (max c₂ cp) H w (z (t - (4 : ℕ)) R
      hR))
    (z0 : (R : ℤ × ℤ) → R ∈ dyadicFiniteTree G J N → ℤ × ℤ → ℝ → ℂ)
    (_ : ∀ (R : ℤ × ℤ) (hR : R ∈ dyadicFiniteTree G J N) (I : ℤ × ℤ), ∀ᵐ (y : ℝ), z0 R hR I y
      = (0 : ℂ))
    (_ : ∀ (R : ℤ × ℤ) (hR : R ∈ dyadicFiniteTree G J N), IsBasicOn G R (dyadicRemainingDepth
      J N R) (1 : ℝ) (BdR R hR) (max c₂ cp) H w (z0 R hR)),
  let za : (R : ℤ × ℤ) → R ∈ dyadicFiniteTree G J N → ℤ × ℤ → ℝ → ℂ :=
    fun (R : ℤ × ℤ) (hR : R ∈ dyadicFiniteTree G J N) => if (1 : ℕ) ≤ la then z la R hR
      else z0 R hR
  let zb : (R : ℤ × ℤ) → R ∈ dyadicFiniteTree G J N → ℤ × ℤ → ℝ → ℂ :=
    fun (R : ℤ × ℤ) (hR : R ∈ dyadicFiniteTree G J N) => if (1 : ℕ) ≤ lb then z lb R hR
      else z0 R hR
  ∀ (_ : ∀ (R : ℤ × ℤ) (hR : R ∈ dyadicFiniteTree G J N), IsBasicOn G R (dyadicRemainingDepth
      J N R) (1 : ℝ) (BdR R hR) (max c₂ cp) H w (za R hR))
    (_ : ∀ (R : ℤ × ℤ) (hR : R ∈ dyadicFiniteTree G J N), IsBasicOn G R (dyadicRemainingDepth
      J N R) (1 : ℝ) (BdR R hR) (max c₂ cp) H w (zb R hR))
    (_ : ∀ (R : ℤ × ℤ) (hR : R ∈ Rs),
    have D := max H (Real.exp ((↑C₁ : ℝ) * ((1 : ℝ) + Bp + Real.log H) ^ C₁));
    have Wa := Fintype.card (Xi R (hRsT R hR)).Λ * Fintype.card (Xk R (hRsT R hR)).Λ *
      ⌊D⌋₊ + Ma;
    have Wb := Fintype.card (Xi R (hRsT R hR)).Λ * Fintype.card (Xk R (hRsT R hR)).Λ *
      ⌊D⌋₊ + Mb;
    have S₀ := (1 : ℝ) + (↑(Fintype.card (Xi R (hRsT R hR)).Λ) : ℝ) + (↑(Fintype.card
      (Xk R (hRsT R hR)).Λ) : ℝ) + (↑(Fintype.card (Xga R (hRsT R hR)).Λ) : ℝ) +
      (↑(Fintype.card (Xgb R (hRsT R hR)).Λ) : ℝ);
    have Sp := (↑Wa : ℝ) * √((2 : ℝ) ^ K₀ / ε) + (1 : ℝ);
    ∃ (P : Finset ((ℤ × ℤ) × ℤ × ℤ)) (A : ↥P → ActiveSetup κ (max (max c₁ (max c₂ cp))
      c₂a)), ∑ p : ↥P, dyadicGridLength G (A p).R.1 ≤ (8 / 3 : ℝ) * dyadicGridLength G
      R.1 ∧ (∀ I ∈ {I ∈ Tup | Rf I = R}, ∃ (p : ↥P), I ∈ (A p).cells) ∧ (∀ (p p' : ↥P),
      ∀ I ∈ (A p).cells, I ∈ (A p').cells → p = p') ∧ ∀ (p : ↥P), (A p).cells ⊆ {I ∈ Tup
      | Rf I = R} ∧ (∀ I ∈ (A p).cells, ∀ J' ∈ {I ∈ Tup | Rf I = R}, dyadicGridCell G
      I.1 I.2 ⊆ dyadicGridCell G J'.1 J'.2 → dyadicGridCell G J'.1 J'.2 ⊆ dyadicGridCell
      G (A p).R.1 (A p).R.2 → J' ∈ (A p).cells) ∧ (A p).G = G ∧ (A p).w = w ∧ (A p).a =
      sa ∧ (A p).b = sb ∧ (A p).R ∈ dyadicFiniteTree G J N ∧ dyadicGridCell G (A p).R.1
      (A p).R.2 ⊆ dyadicGridCell G R.1 R.2 ∧ (A p).H = max D (max (fitBudget Cqa Ca ka)
      (fitBudget Cqa Ca kb)) ∧ (A p).Dc = √ε⁻¹ ∧ (A p).S = (2 : ℝ) ∧ (A p).η = (4 : ℝ) *
      η₀ ∧ Fintype.card (A p).L = Fintype.card (Xi R (hRsT R hR)).Λ + Fintype.card (Xk R
      (hRsT R hR)).Λ + (Wa + Fintype.card (Xga R (hRsT R hR)).Λ) + (Wb + Fintype.card
      (Xgb R (hRsT R hR)).Λ) ∧ ∑ I ∈ (A p).cells, dyadicGridLength G I.1 *
      ‖localProgressionForm (dyadicGridLength G I.1) (w I) (slots4 sa i k (f sa - (Xga R
      (hRsT R hR)).val I) ((Xi R (hRsT R hR)).val I) ((Xk R (hRsT R hR)).val I) (f sb -
      (Xgb R (hRsT R hR)).val I)) - (A p).Hf I ((A p).Y I)‖ ≤ baseErr κ (Fintype.card
      (Xi R (hRsT R hR)).Λ) (Fintype.card (Xk R (hRsT R hR)).Λ) D Bp ε K₀ Wa Wb
      (fitOpponentConst (M la)) (fitOpponentConst (M lb)) * dyadicGridLength G (A p).R.1
      ∧ (∀ I ∈ (A p).cells, ∀ (s s' : Fin (4 : ℕ)), s ≠ s' → PairSmall (dyadicGridLeft G
      I.1 I.2) (dyadicGridLength G I.1) (w I) s s' ((A p).Y I s) ((A p).Y I s') (η₀ +
      ((2 : ℝ) + (2 : ℝ) * S₀) * (Real.exp (-(↑ka : ℝ)) + Real.exp (-(↑kb : ℝ))) + ((1 :
      ℝ) + Sp) * Real.exp (-(↑kb : ℝ)))) ∧ (∀ I ∈ (A p).cells, ∀ (l : Fin (4 : ℕ)),
      (eLpNorm ((A p).Y I l) (2 : ℝ≥0∞) ((A p).μ I)).toReal ≤ (2 : ℝ)) ∧ (∀ (l : Fin (4
      : ℕ)), ∑ I ∈ (A p).cells, dyadicGridLength G I.1 * (eLpNorm ((A p).U l I) (2 :
      ℝ≥0∞) ((A p).μ I)).toReal ^ (2 : ℕ) ≤ (↑K₀ : ℝ) ^ (2 : ℕ) * dyadicGridLength G (A
      p).R.1) ∧ ∑ I ∈ (A p).cells, dyadicGridLength G I.1 * ‖(A p).Hf I ((A p).z (3 :
      Fin (4 : ℕ)) I)‖ ≤ η₀ * ((↑K₀ : ℝ) ^ (2 : ℕ) * dyadicGridLength G (A p).R.1) ∧ (A
      p).HasColumnRep (1 : ℝ) ∧ (A p).SubRootProps η₀ ((↑K₀ : ℝ) ^ (2 : ℕ))),
  ∃ (ι : Type) (_ : Fintype ι) (A : ι → ActiveSetup κ (max (max c₁ (max c₂ cp)) c₂a)),
    ∑ p : ι, dyadicGridLength G (A p).R.1 ≤ (91 / 3 : ℝ) * dyadicGridLength G J.1 ∧ (∀
    (p p' : ι), ∀ I ∈ (A p).cells, I ∈ (A p').cells → p = p') ∧ (∀ (p : ι), (A
    p).cells ⊆ dyadicFiniteTree G J N ∧ (∀ I ∈ (A p).cells, kernelHull G J N w I) ∧ (∀
    I ∈ (A p).cells, ∀ (J' : ℤ × ℤ), dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G J'.1
    J'.2 → dyadicGridCell G J'.1 J'.2 ⊆ dyadicGridCell G (A p).R.1 (A p).R.2 → J' ∈ (A
    p).cells) ∧ (A p).G = G ∧ (A p).w = w ∧ (A p).R ∈ dyadicFiniteTree G J N ∧ (A p).H
    = max D (max (fitBudget Cqa Ca ka) (fitBudget Cqa Ca kb)) ∧ (A p).Dc = √ε⁻¹ ∧ (A
    p).S = (2 : ℝ) ∧ (A p).η = (4 : ℝ) * η₀ ∧ Fintype.card (A p).L ≤ (6 : ℕ) * Mt + Wa
    + Wb ∧ (∀ I ∈ (A p).cells, ∀ (s s' : Fin (4 : ℕ)), s ≠ s' → PairSmall
    (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1) (w I) s s' ((A p).Y I s) ((A
    p).Y I s') (η₀ + ((2 : ℝ) + (2 : ℝ) * S₀) * (Real.exp (-(↑ka : ℝ)) + Real.exp
    (-(↑kb : ℝ))) + ((1 : ℝ) + Sp) * Real.exp (-(↑kb : ℝ)))) ∧ (∀ I ∈ (A p).cells, ∀
    (l : Fin (4 : ℕ)), (eLpNorm ((A p).Y I l) (2 : ℝ≥0∞) ((A p).μ I)).toReal ≤ (2 :
    ℝ)) ∧ (∀ (l : Fin (4 : ℕ)), ∑ I ∈ (A p).cells, dyadicGridLength G I.1 * (eLpNorm
    ((A p).U l I) (2 : ℝ≥0∞) ((A p).μ I)).toReal ^ (2 : ℕ) ≤ (↑K₀ : ℝ) ^ (2 : ℕ) *
    dyadicGridLength G (A p).R.1) ∧ ∑ I ∈ (A p).cells, dyadicGridLength G I.1 * ‖(A
    p).Hf I ((A p).z (3 : Fin (4 : ℕ)) I)‖ ≤ η₀ * ((↑K₀ : ℝ) ^ (2 : ℕ) *
    dyadicGridLength G (A p).R.1) ∧ (A p).HasColumnRep (1 : ℝ) ∧ (A p).SubRootProps η₀
    ((↑K₀ : ℝ) ^ (2 : ℕ))) ∧ ∑ I ∈ dyadicFiniteTree G J N, dyadicGridLength G I.1 *
    ‖localProgressionForm (dyadicGridLength G I.1) (w I) (stagTuple f g u t I)‖ ≤ ∑ p
    : ι, ∑ I ∈ (A p).cells, dyadicGridLength G I.1 * ‖(A p).Hf I ((A p).Y I)‖ + E *
    ((91 / 3 : ℝ) * dyadicGridLength G J.1)

open scoped Classical in
private def BaseTupleStage2Statement : Prop :=
  ∀ (κ : LocalKernelClass)
    (c₂ : ℕ)
    (cp : ℕ)
    (Wp : ℝ)
    (_ : ∀ (c : ℕ) (H' : ℝ), cp ≤ c → Wp ≤ H' → ∃ (d : ℕ) (Φ : QuadraticChartData d), (1 : ℕ)
      ≤ d ∧ QuadraticChartComplexity c H' Φ ∧ IsBoundedQuadraticChart Φ)
    (c₁ : ℕ)
    (C₁ : ℕ)
    (c₂a : ℕ)
    (Ca : ℕ)
    (q : ℝ)
    (_ : (2 : ℝ) < q)
    (Cqa : ℝ)
    (_ : ∀ {G : RealDyadicGrid} {J : ℤ × ℤ} {N : ℕ} {H : ℝ} {R : ℤ × ℤ}, R ∈ dyadicFiniteTree
      G J N → (1 : ℝ) ≤ H → ∀ {a i k b : Fin (4 : ℕ)}, a ≠ i → a ≠ k → a ≠ b → i ≠ k → i
      ≠ b → k ≠ b → ∀ (w : ℤ × ℤ → ℝ × ℝ → ℂ), (∀ (I : ℤ × ℤ), IsAdmissibleLocalKernel κ
      (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1) (w I)) → ∀ (f : Fin (4 : ℕ) →
      ℝ → ℂ), (∀ (l : Fin (4 : ℕ)), Measurable (f l)) → (∀ (l : Fin (4 : ℕ)), ∀ I ∈
      dyadicFiniteTree G J N, kernelHull G J N w I → eLpNorm (f l) (ENNReal.ofReal q)
      (normalizedIntervalMeasure (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1)) ≤
      (1 : ℝ≥0∞)) → ∀ (Xi Xk Xga Xgb : LowList G J N R (max c₂ cp) H), (∃ (d : ℕ) (Φ :
      QuadraticChartData d), (1 : ℕ) ≤ d ∧ QuadraticChartComplexity (max c₂ cp) H Φ ∧
      IsBoundedQuadraticChart Φ) → ∀ (zga zgb : ℤ × ℤ → ℝ → ℂ) {Cga Cgb : ℝ}, (0 : ℝ) ≤
      Cga → (0 : ℝ) ≤ Cgb → ((∀ (I : ℤ × ℤ), Measurable (zga I) ∧ MemLp (zga I) (2 :
      ℝ≥0∞) (volume.restrict (dyadicGridCell G I.1 I.2))) ∧ ∀ J' ∈ dyadicFiniteTree G J
      N, dyadicGridCell G J'.1 J'.2 ⊆ dyadicGridCell G R.1 R.2 → IsAdmissibleOpponent G
      J' (f a) zga Cga ∧ HasDepthEnergy G J' (f a) zga (1 : ℝ)) → ((∀ (I : ℤ × ℤ),
      Measurable (zgb I) ∧ MemLp (zgb I) (2 : ℝ≥0∞) (volume.restrict (dyadicGridCell G
      I.1 I.2))) ∧ ∀ J' ∈ dyadicFiniteTree G J N, dyadicGridCell G J'.1 J'.2 ⊆
      dyadicGridCell G R.1 R.2 → IsAdmissibleOpponent G J' (f b) zgb Cgb ∧
      HasDepthEnergy G J' (f b) zgb (1 : ℝ)) → ∀ (K₀ : ℕ) (Tc : Finset (ℤ × ℤ)), (∀ I ∈
      Tc, I ∈ dyadicFiniteTree G J N ∧ dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G R.1
      R.2 ∧ I.1 + (↑K₀ : ℤ) ≤ J.1 + (↑N : ℤ) ∧ (∀ᵐ (y : ℝ), y ∈ dyadicGridCell G I.1 I.2
      → zga I y = Xga.val I y) ∧ ∀ᵐ (y : ℝ), y ∈ dyadicGridCell G I.1 I.2 → zgb I y =
      Xgb.val I y) → (∀ I ∈ Tc, kernelHull G J N w I) → ∀ {Bd : ℝ}, (∃ (z₁ : ℤ × ℤ → ℝ →
      ℂ) (z₂ : ℤ × ℤ → ℝ → ℂ), IsBasicOn G R (dyadicRemainingDepth J N R) (1 : ℝ) Bd
      (max c₂ cp) H w z₁ ∧ IsBasicOn G R (dyadicRemainingDepth J N R) (1 : ℝ) Bd (max c₂
      cp) H w z₂ ∧ ∀ I ∈ Tc, ∀ᵐ (y : ℝ), y ∈ dyadicGridCell G I.1 I.2 → Xi.val I y = z₁
      I y - z₂ I y) → (∃ (z₁ : ℤ × ℤ → ℝ → ℂ) (z₂ : ℤ × ℤ → ℝ → ℂ), IsBasicOn G R
      (dyadicRemainingDepth J N R) (1 : ℝ) Bd (max c₂ cp) H w z₁ ∧ IsBasicOn G R
      (dyadicRemainingDepth J N R) (1 : ℝ) Bd (max c₂ cp) H w z₂ ∧ ∀ I ∈ Tc, ∀ᵐ (y : ℝ),
      y ∈ dyadicGridCell G I.1 I.2 → Xk.val I y = z₁ I y - z₂ I y) → IsBasicOn G R
      (dyadicRemainingDepth J N R) (1 : ℝ) Bd (max c₂ cp) H w zga → IsBasicOn G R
      (dyadicRemainingDepth J N R) (1 : ℝ) Bd (max c₂ cp) H w zgb → Bd ≤ (2 : ℝ) +
      (↑(Fintype.card Xi.Λ + Fintype.card Xk.Λ + Fintype.card Xga.Λ + Fintype.card
      Xgb.Λ) : ℝ) → (∀ I ∈ Tc, eLpNorm (Xi.val I) (2 : ℝ≥0∞) (normalizedIntervalMeasure
      (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1)) ≤ ENNReal.ofReal (2 : ℝ)) →
      (∀ I ∈ Tc, eLpNorm (Xk.val I) (2 : ℝ≥0∞) (normalizedIntervalMeasure
      (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1)) ≤ ENNReal.ofReal (2 : ℝ)) →
      (∀ I ∈ Tc, eLpNorm (Xga.val I) (2 : ℝ≥0∞) (normalizedIntervalMeasure
      (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1)) ≤ ENNReal.ofReal (1 : ℝ)) →
      (∀ I ∈ Tc, eLpNorm (Xgb.val I) (2 : ℝ≥0∞) (normalizedIntervalMeasure
      (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1)) ≤ ENNReal.ofReal (1 : ℝ)) → ∀
      {η₀ : ℝ}, (0 : ℝ) ≤ η₀ → (∀ I ∈ Tc, ∀ (s s' : Fin (4 : ℕ)), s ≠ s' → PairSmall
      (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1) (w I) s s' (slots4 a i k (f a
      - Xga.val I) (Xi.val I) (Xk.val I) (f b - Xgb.val I) s) (slots4 a i k (f a -
      Xga.val I) (Xi.val I) (Xk.val I) (f b - Xgb.val I) s') η₀) → ∀ (Bp ε : ℝ) (ka kb
      Ma Mb : ℕ), (1 : ℝ) ≤ Bp → (0 : ℝ) < ε → ε ≤ (1 : ℝ) → (1 : ℕ) ≤ ka → (1 : ℕ) ≤ kb
      → (16 : ℝ) * fitBudget Cqa Ca ka ^ (2 : ℕ) < (↑Ma : ℝ) → (16 : ℝ) * fitBudget Cqa
      Ca kb ^ (2 : ℕ) < (↑Mb : ℝ) →
    have D := max H (Real.exp ((↑C₁ : ℝ) * ((1 : ℝ) + Bp + Real.log H) ^ C₁));
    have Wa := Fintype.card Xi.Λ * Fintype.card Xk.Λ * ⌊D⌋₊ + Ma;
    have Wb := Fintype.card Xi.Λ * Fintype.card Xk.Λ * ⌊D⌋₊ + Mb;
    have S₀ := (1 : ℝ) + (↑(Fintype.card Xi.Λ) : ℝ) + (↑(Fintype.card Xk.Λ) : ℝ) +
      (↑(Fintype.card Xga.Λ) : ℝ) + (↑(Fintype.card Xgb.Λ) : ℝ);
    have Sp := (↑Wa : ℝ) * √((2 : ℝ) ^ K₀ / ε) + (1 : ℝ);
    ∃ (P : Finset ((ℤ × ℤ) × ℤ × ℤ)) (A : ↥P → ActiveSetup κ (max (max c₁ (max c₂ cp))
      c₂a)), ∑ p : ↥P, dyadicGridLength G (A p).R.1 ≤ (8 / 3 : ℝ) * dyadicGridLength G
      R.1 ∧ (∀ I ∈ Tc, ∃ (p : ↥P), I ∈ (A p).cells) ∧ (∀ (p p' : ↥P), ∀ I ∈ (A p).cells,
      I ∈ (A p').cells → p = p') ∧ ∀ (p : ↥P), (A p).cells ⊆ Tc ∧ (∀ I ∈ (A p).cells, ∀
      J' ∈ Tc, dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G J'.1 J'.2 → dyadicGridCell G
      J'.1 J'.2 ⊆ dyadicGridCell G (A p).R.1 (A p).R.2 → J' ∈ (A p).cells) ∧ (A p).G = G
      ∧ (A p).w = w ∧ (A p).a = a ∧ (A p).b = b ∧ (A p).R ∈ dyadicFiniteTree G J N ∧
      dyadicGridCell G (A p).R.1 (A p).R.2 ⊆ dyadicGridCell G R.1 R.2 ∧ (A p).H = max D
      (max (fitBudget Cqa Ca ka) (fitBudget Cqa Ca kb)) ∧ (A p).Dc = √ε⁻¹ ∧ (A p).S = (2
      : ℝ) ∧ (A p).η = (4 : ℝ) * η₀ ∧ Fintype.card (A p).L = Fintype.card Xi.Λ +
      Fintype.card Xk.Λ + (Wa + Fintype.card Xga.Λ) + (Wb + Fintype.card Xgb.Λ) ∧ ∑ I ∈
      (A p).cells, dyadicGridLength G I.1 * ‖localProgressionForm (dyadicGridLength G
      I.1) (w I) (slots4 a i k (f a - Xga.val I) (Xi.val I) (Xk.val I) (f b - Xgb.val
      I)) - (A p).Hf I ((A p).Y I)‖ ≤ baseErr κ (Fintype.card Xi.Λ) (Fintype.card Xk.Λ)
      D Bp ε K₀ Wa Wb Cga Cgb * dyadicGridLength G (A p).R.1 ∧ (∀ I ∈ (A p).cells, ∀ (s
      s' : Fin (4 : ℕ)), s ≠ s' → PairSmall (dyadicGridLeft G I.1 I.2) (dyadicGridLength
      G I.1) (w I) s s' ((A p).Y I s) ((A p).Y I s') (η₀ + ((2 : ℝ) + (2 : ℝ) * S₀) *
      (Real.exp (-(↑ka : ℝ)) + Real.exp (-(↑kb : ℝ))) + ((1 : ℝ) + Sp) * Real.exp (-(↑kb
      : ℝ)))) ∧ (∀ I ∈ (A p).cells, ∀ (l : Fin (4 : ℕ)), (eLpNorm ((A p).Y I l) (2 :
      ℝ≥0∞) ((A p).μ I)).toReal ≤ (2 : ℝ)) ∧ (∀ (l : Fin (4 : ℕ)), ∑ I ∈ (A p).cells,
      dyadicGridLength G I.1 * (eLpNorm ((A p).U l I) (2 : ℝ≥0∞) ((A p).μ I)).toReal ^
      (2 : ℕ) ≤ (↑K₀ : ℝ) ^ (2 : ℕ) * dyadicGridLength G (A p).R.1) ∧ ∑ I ∈ (A p).cells,
      dyadicGridLength G I.1 * ‖(A p).Hf I ((A p).z (3 : Fin (4 : ℕ)) I)‖ ≤ η₀ * ((↑K₀ :
      ℝ) ^ (2 : ℕ) * dyadicGridLength G (A p).R.1) ∧ (A p).HasColumnRep (1 : ℝ) ∧ (A
      p).SubRootProps η₀ ((↑K₀ : ℝ) ^ (2 : ℕ)))
    (G : RealDyadicGrid)
    (J : ℤ × ℤ)
    (N : ℕ)
    (w : ℤ × ℤ → ℝ × ℝ → ℂ)
    (_ : ∀ (I : ℤ × ℤ), IsAdmissibleLocalKernel κ (dyadicGridLeft G I.1 I.2)
      (dyadicGridLength G I.1) (w I))
    (f : Fin (4 : ℕ) → ℝ → ℂ)
    (_ : ∀ (l : Fin (4 : ℕ)), Measurable (f l))
    (_ : ∀ (l : Fin (4 : ℕ)), ∀ I ∈ dyadicFiniteTree G J N, I = J ∨ kernelHull G J N w I →
      eLpNorm (f l) (ENNReal.ofReal q) (normalizedIntervalMeasure (dyadicGridLeft G I.1
      I.2) (dyadicGridLength G I.1)) ≤ (1 : ℝ≥0∞))
    (Bf : ℕ → ℝ)
    (kk : ℕ → ℕ)
    (M : ℕ → ℕ)
    (roots : ℕ → Finset (ℤ × ℤ))
    (seg : ℕ → ℤ × ℤ → ℤ × ℤ)
    (n : ℕ → ℤ × ℤ → ℕ)
    (a : ℕ → ℤ × ℤ → ℕ → ℝ → ℂ)
    (g : ℕ → ℤ × ℤ → ℝ → ℂ)
    (cnt : ℕ → ℤ × ℤ → ℤ × ℤ → ℕ)
    (atm : ℕ → ℤ × ℤ → ℤ × ℤ → ℕ → ℝ → ℂ)
    (_ : ∀ (ℓ : ℕ), IsAdaptiveFit c₂ (Bf ℓ) G J N w (stagPos ℓ) q (f (stagPos ℓ)) (kk ℓ) (M
      ℓ) (roots ℓ) (seg ℓ) (n ℓ) (a ℓ) (g ℓ) ∧ IsAttemptData c₂ (Bf ℓ) G J N (M ℓ)
      (roots ℓ) (seg ℓ) (n ℓ) (a ℓ) (cnt ℓ) (atm ℓ) ∧ IsFitOpponent G J N (f (stagPos
      ℓ)) (roots ℓ) (seg ℓ) (g ℓ) (fitOpponentConst (M ℓ)) (max (2 : ℝ) (↑(M ℓ) : ℝ)) c₂
      (Bf ℓ))
    (u : ℕ)
    (t : ℕ)
    (hut : u < t)
    (Hc : ℝ)
    (Mt : ℕ)
    (_ : ∀ ℓ ≤ t, M ℓ ≤ Mt)
    (η₀ : ℝ)
    (_ : (0 : ℝ) ≤ η₀)
    (_ : ∀ I ∈ dyadicFiniteTree G J N, kernelHull G J N w I → ∀ (s s' : Fin (4 : ℕ)), s ≠ s'
      → PairSmall (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1) (w I) s s'
      (stagTuple f g u t I s) (stagTuple f g u t I s') η₀)
    (_ : ∀ I ∈ dyadicFiniteTree G J N, kernelHull G J N w I → ∀ (l : Fin (4 : ℕ)), eLpNorm
      (stagTuple f g u t I l) (2 : ℝ≥0∞) (normalizedIntervalMeasure (dyadicGridLeft G
      I.1 I.2) (dyadicGridLength G I.1)) ≤ ENNReal.ofReal (2 : ℝ))
    (Bp : ℝ)
    (ε : ℝ)
    (K₀ : ℕ)
    (ka : ℕ)
    (kb : ℕ)
    (Ma : ℕ)
    (Mb : ℕ)
    (_ : (1 : ℝ) ≤ Bp)
    (_ : (0 : ℝ) < ε)
    (_ : ε ≤ (1 : ℝ))
    (_ : (1 : ℕ) ≤ ka)
    (_ : (1 : ℕ) ≤ kb)
    (_ : (16 : ℝ) * fitBudget Cqa Ca ka ^ (2 : ℕ) < (↑Ma : ℝ))
    (_ : (16 : ℝ) * fitBudget Cqa Ca kb ^ (2 : ℕ) < (↑Mb : ℝ)),
  let H : ℝ :=
    max Hc Wp ^ (6 : ℕ)
  let D : ℝ :=
    max H (Real.exp ((↑C₁ : ℝ) * ((1 : ℝ) + Bp + Real.log H) ^ C₁))
  let Wa : ℕ :=
    (2 : ℕ) * Mt * ((2 : ℕ) * Mt) * ⌊D⌋₊ + Ma
  let Wb : ℕ :=
    (2 : ℕ) * Mt * ((2 : ℕ) * Mt) * ⌊D⌋₊ + Mb
  let E : ℝ :=
    baseErr κ ((2 : ℕ) * Mt) ((2 : ℕ) * Mt) D Bp ε K₀ Wa Wb (fitOpponentConst Mt)
      (fitOpponentConst Mt)
  let S₀ : ℝ :=
    (1 : ℝ) + (6 : ℝ) * (↑Mt : ℝ)
  let Sp : ℝ :=
    (↑Wa : ℝ) * √((2 : ℝ) ^ K₀ / ε) + (1 : ℝ)
  let i : Fin (4 : ℕ) :=
    stagPos u
  let k : Fin (4 : ℕ) :=
    stagPos t
  ∀ (_ : i ≠ k)
    (sa : Fin (4 : ℕ))
    (sb : Fin (4 : ℕ))
    (_ : sa ≠ sb)
    (_ : sa ≠ i)
    (_ : sa ≠ k)
    (_ : sb ≠ i)
    (_ : sb ≠ k),
  let la : ℕ :=
    StaggerCell.lastLevel sa t
  ∀ (hla2 : la < t)
    (_ : (1 : ℕ) ≤ la → stagPos la = sa),
  let lb : ℕ :=
    StaggerCell.lastLevel sb t
  ∀ (hlb2 : lb < t)
    (_ : (1 : ℕ) ≤ lb → stagPos lb = sb),
  let Lset : Finset ℕ :=
    {u, u - (4 : ℕ), t, t - (4 : ℕ), la, lb}
  ∀ (_ : Lset = {u, u - (4 : ℕ), t, t - (4 : ℕ), la, lb})
    (hLne : Lset.Nonempty)
    (_ : SegData G J N seg Lset),
  let Rf : ℤ × ℤ → ℤ × ℤ :=
    firstRoot seg Lset hLne
  let Tup : Finset (ℤ × ℤ) :=
    {I ∈ dyadicFiniteTree G J N | I.1 + (↑K₀ : ℤ) ≤ J.1 + (↑N : ℤ) ∧ kernelHull G J N w
      I}
  let Rs : Finset (ℤ × ℤ) :=
    Finset.image Rf Tup
  ∀ (hRtree : ∀ I ∈ dyadicFiniteTree G J N, Rf I ∈ dyadicFiniteTree G J N ∧ dyadicGridCell G I.1
      I.2 ⊆ dyadicGridCell G (Rf I).1 (Rf I).2)
    (_ : ∀ R ∈ Rs, R ∈ dyadicFiniteTree G J N)
    (hHl : ∀ ℓ ≤ t, max (Bf ℓ) Wp ^ (6 : ℕ) ≤ H)
    (_ : (1 : ℝ) ≤ H)
    (_ : Wp ≤ H)
    (X : (ℓ : ℕ) → (R : ℤ × ℤ) → R ∈ dyadicFiniteTree G J N → LowList G J N R (max c₂ cp)
      (max (Bf ℓ) Wp ^ (6 : ℕ))),
  let Y : (ℓ : ℕ) → ℓ ≤ t → (R : ℤ × ℤ) → R ∈ dyadicFiniteTree G J N → LowList G J N R (max c₂
      cp) H :=
    fun ℓ hℓ R hR => (X ℓ R hR).mono le_rfl (hHl ℓ hℓ)
  ∀ (_ : ∀ (ℓ : ℕ) (hℓ : ℓ ≤ t) (R : ℤ × ℤ) (hR : R ∈ dyadicFiniteTree G J N), ∀ I ∈
      dyadicFiniteTree G J N, dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G R.1 R.2 → seg
      ℓ I = seg ℓ R → kernelHull G J N w I → ∀ (y : ℝ), (Y ℓ hℓ R hR).val I y = g ℓ I y)
    (_ : ∀ (ℓ : ℕ) (hℓ : ℓ ≤ t) (R : ℤ × ℤ) (hR : R ∈ dyadicFiniteTree G J N), Fintype.card
      (Y ℓ hℓ R hR).Λ = M ℓ)
    (hu4 : u - (4 : ℕ) ≤ t)
    (ht4 : t - (4 : ℕ) ≤ t),
  let Xi : (R : ℤ × ℤ) → R ∈ dyadicFiniteTree G J N → LowList G J N R (max c₂ cp) H :=
    fun R hR => if u ≤ 4 then Y u hut.le R hR else (Y u hut.le R hR).sub (Y (u - 4) hu4
      R hR)
  let Xk : (R : ℤ × ℤ) → R ∈ dyadicFiniteTree G J N → LowList G J N R (max c₂ cp) H :=
    fun R hR => if t ≤ 4 then Y t le_rfl R hR else (Y t le_rfl R hR).sub (Y (t - 4) ht4
      R hR)
  let Xga : (R : ℤ × ℤ) → R ∈ dyadicFiniteTree G J N → LowList G J N R (max c₂ cp) H :=
    fun R hR => if 1 ≤ la then Y la hla2.le R hR else LowList.empty
  let Xgb : (R : ℤ × ℤ) → R ∈ dyadicFiniteTree G J N → LowList G J N R (max c₂ cp) H :=
    fun R hR => if 1 ≤ lb then Y lb hlb2.le R hR else LowList.empty
  ∀ (_ : u ∈ Lset)
    (_ : u - (4 : ℕ) ∈ Lset)
    (_ : t ∈ Lset)
    (_ : t - (4 : ℕ) ∈ Lset)
    (_ : la ∈ Lset)
    (_ : lb ∈ Lset)
    (_ : ∀ I ∈ dyadicFiniteTree G J N, ∀ ℓ ∈ Lset, seg ℓ I = seg ℓ (Rf I))
    (_ : ∀ (I : ℤ × ℤ) (hI : I ∈ dyadicFiniteTree G J N), kernelHull G J N w I → slots4 sa i
      k (f sa - (Xga (Rf I) (hRtree I hI).left).val I) ((Xi (Rf I) (hRtree I
      hI).left).val I) ((Xk (Rf I) (hRtree I hI).left).val I) (f sb - (Xgb (Rf I)
      (hRtree I hI).left).val I) = stagTuple f g u t I)
    (_ : ∀ (I : ℤ × ℤ) (hI : I ∈ dyadicFiniteTree G J N), kernelHull G J N w I → (Xi (Rf I)
      (hRtree I hI).left).val I = stagTuple f g u t I i)
    (_ : ∀ (I : ℤ × ℤ) (hI : I ∈ dyadicFiniteTree G J N), kernelHull G J N w I → (Xk (Rf I)
      (hRtree I hI).left).val I = stagTuple f g u t I k)
    (_ : ∀ (ℓ : ℕ), ∀ I ∈ dyadicFiniteTree G J N, kernelHull G J N w I → eLpNorm (g ℓ I) (2 :
      ℝ≥0∞) (normalizedIntervalMeasure (dyadicGridLeft G I.1 I.2) (dyadicGridLength G
      I.1)) ≤ ENNReal.ofReal (1 : ℝ))
    (_ : ∀ (I : ℤ × ℤ) (hI : I ∈ dyadicFiniteTree G J N), kernelHull G J N w I → (Xga (Rf I)
      (hRtree I hI).left).val I = if (1 : ℕ) ≤ la then g la I else (0 : ℝ → ℂ))
    (_ : ∀ (I : ℤ × ℤ) (hI : I ∈ dyadicFiniteTree G J N), kernelHull G J N w I → (Xgb (Rf I)
      (hRtree I hI).left).val I = if (1 : ℕ) ≤ lb then g lb I else (0 : ℝ → ℂ))
    (z : ℕ → (R : ℤ × ℤ) → R ∈ dyadicFiniteTree G J N → ℤ × ℤ → ℝ → ℂ)
    (_ : ∀ (ℓ : ℕ) (R : ℤ × ℤ) (hR : R ∈ dyadicFiniteTree G J N) (I : ℤ × ℤ), Measurable (z ℓ
      R hR I) ∧ MemLp (z ℓ R hR I) (2 : ℝ≥0∞) (volume.restrict (dyadicGridCell G I.1
      I.2)))
    (_ : ∀ (ℓ : ℕ) (R : ℤ × ℤ) (hR : R ∈ dyadicFiniteTree G J N), ∀ I ∈ dyadicFiniteTree G J
      N, seg ℓ I = seg ℓ R → ∀ᵐ (y : ℝ), y ∈ dyadicGridCell G I.1 I.2 → z ℓ R hR I y = g
      ℓ I y)
    (_ : ∀ (ℓ : ℕ) (R : ℤ × ℤ) (hR : R ∈ dyadicFiniteTree G J N), ∀ J' ∈ dyadicFiniteTree G J
      N, dyadicGridCell G J'.1 J'.2 ⊆ dyadicGridCell G R.1 R.2 → IsAdmissibleOpponent G
      J' (f (stagPos ℓ)) (z ℓ R hR) (fitOpponentConst (M ℓ)) ∧ HasDepthEnergy G J' (f
      (stagPos ℓ)) (z ℓ R hR) (1 : ℝ))
    (_ : ∀ (ℓ : ℕ) (R : ℤ × ℤ) (hR : R ∈ dyadicFiniteTree G J N), IsBasicOn G R
      (dyadicRemainingDepth J N R) (1 : ℝ) (max (2 : ℝ) (↑(M ℓ) : ℝ)) c₂ (Bf ℓ) w (z ℓ R
      hR))
    (_ : ∀ ℓ ≤ t, Bf ℓ ≤ H),
  let BdR : (R : ℤ × ℤ) → R ∈ dyadicFiniteTree G J N → ℝ :=
    fun (R : ℤ × ℤ) (hR : R ∈ dyadicFiniteTree G J N) => (2 : ℝ) + (↑(Fintype.card (Xi R
      hR).Λ + Fintype.card (Xk R hR).Λ + Fintype.card (Xga R hR).Λ + Fintype.card (Xgb R
      hR).Λ) : ℝ)
  ∀ (_ : ∀ (ℓ : ℕ) (R : ℤ × ℤ) (hR : R ∈ dyadicFiniteTree G J N), M ℓ ≤ Fintype.card (Xi R
      hR).Λ + Fintype.card (Xk R hR).Λ + Fintype.card (Xga R hR).Λ + Fintype.card (Xgb R
      hR).Λ → max (2 : ℝ) (↑(M ℓ) : ℝ) ≤ BdR R hR)
    (_ : ∀ (R : ℤ × ℤ) (hR : R ∈ dyadicFiniteTree G J N), M u ≤ Fintype.card (Xi R hR).Λ ∧
      (¬u ≤ (4 : ℕ) → M (u - (4 : ℕ)) ≤ Fintype.card (Xi R hR).Λ))
    (_ : ∀ (R : ℤ × ℤ) (hR : R ∈ dyadicFiniteTree G J N), M t ≤ Fintype.card (Xk R hR).Λ ∧
      (¬t ≤ (4 : ℕ) → M (t - (4 : ℕ)) ≤ Fintype.card (Xk R hR).Λ))
    (_ : ∀ (R : ℤ × ℤ) (hR : R ∈ dyadicFiniteTree G J N), (1 : ℕ) ≤ la → M la ≤ Fintype.card
      (Xga R hR).Λ)
    (_ : ∀ (R : ℤ × ℤ) (hR : R ∈ dyadicFiniteTree G J N), (1 : ℕ) ≤ lb → M lb ≤ Fintype.card
      (Xgb R hR).Λ)
    (_ : ∀ (R : ℤ × ℤ) (hR : R ∈ dyadicFiniteTree G J N), IsBasicOn G R (dyadicRemainingDepth
      J N R) (1 : ℝ) (BdR R hR) (max c₂ cp) H w (z u R hR))
    (_ : ∀ (R : ℤ × ℤ) (hR : R ∈ dyadicFiniteTree G J N), ¬u ≤ (4 : ℕ) → IsBasicOn G R
      (dyadicRemainingDepth J N R) (1 : ℝ) (BdR R hR) (max c₂ cp) H w (z (u - (4 : ℕ)) R
      hR))
    (_ : ∀ (R : ℤ × ℤ) (hR : R ∈ dyadicFiniteTree G J N), IsBasicOn G R (dyadicRemainingDepth
      J N R) (1 : ℝ) (BdR R hR) (max c₂ cp) H w (z t R hR)),
  ∃ (ι : Type) (_ : Fintype ι) (A : ι → ActiveSetup κ (max (max c₁ (max c₂ cp)) c₂a)),
    ∑ p : ι, dyadicGridLength G (A p).R.1 ≤ (91 / 3 : ℝ) * dyadicGridLength G J.1 ∧ (∀
    (p p' : ι), ∀ I ∈ (A p).cells, I ∈ (A p').cells → p = p') ∧ (∀ (p : ι), (A
    p).cells ⊆ dyadicFiniteTree G J N ∧ (∀ I ∈ (A p).cells, kernelHull G J N w I) ∧ (∀
    I ∈ (A p).cells, ∀ (J' : ℤ × ℤ), dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G J'.1
    J'.2 → dyadicGridCell G J'.1 J'.2 ⊆ dyadicGridCell G (A p).R.1 (A p).R.2 → J' ∈ (A
    p).cells) ∧ (A p).G = G ∧ (A p).w = w ∧ (A p).R ∈ dyadicFiniteTree G J N ∧ (A p).H
    = max D (max (fitBudget Cqa Ca ka) (fitBudget Cqa Ca kb)) ∧ (A p).Dc = √ε⁻¹ ∧ (A
    p).S = (2 : ℝ) ∧ (A p).η = (4 : ℝ) * η₀ ∧ Fintype.card (A p).L ≤ (6 : ℕ) * Mt + Wa
    + Wb ∧ (∀ I ∈ (A p).cells, ∀ (s s' : Fin (4 : ℕ)), s ≠ s' → PairSmall
    (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1) (w I) s s' ((A p).Y I s) ((A
    p).Y I s') (η₀ + ((2 : ℝ) + (2 : ℝ) * S₀) * (Real.exp (-(↑ka : ℝ)) + Real.exp
    (-(↑kb : ℝ))) + ((1 : ℝ) + Sp) * Real.exp (-(↑kb : ℝ)))) ∧ (∀ I ∈ (A p).cells, ∀
    (l : Fin (4 : ℕ)), (eLpNorm ((A p).Y I l) (2 : ℝ≥0∞) ((A p).μ I)).toReal ≤ (2 :
    ℝ)) ∧ (∀ (l : Fin (4 : ℕ)), ∑ I ∈ (A p).cells, dyadicGridLength G I.1 * (eLpNorm
    ((A p).U l I) (2 : ℝ≥0∞) ((A p).μ I)).toReal ^ (2 : ℕ) ≤ (↑K₀ : ℝ) ^ (2 : ℕ) *
    dyadicGridLength G (A p).R.1) ∧ ∑ I ∈ (A p).cells, dyadicGridLength G I.1 * ‖(A
    p).Hf I ((A p).z (3 : Fin (4 : ℕ)) I)‖ ≤ η₀ * ((↑K₀ : ℝ) ^ (2 : ℕ) *
    dyadicGridLength G (A p).R.1) ∧ (A p).HasColumnRep (1 : ℝ) ∧ (A p).SubRootProps η₀
    ((↑K₀ : ℝ) ^ (2 : ℕ))) ∧ ∑ I ∈ dyadicFiniteTree G J N, dyadicGridLength G I.1 *
    ‖localProgressionForm (dyadicGridLength G I.1) (w I) (stagTuple f g u t I)‖ ≤ ∑ p
    : ι, ∑ I ∈ (A p).cells, dyadicGridLength G I.1 * ‖(A p).Hf I ((A p).Y I)‖ + E *
    ((91 / 3 : ℝ) * dyadicGridLength G J.1)

open scoped Classical in
private def BaseTupleStage1Statement : Prop :=
  ∀ (κ : LocalKernelClass)
    (c₂ : ℕ)
    (cp : ℕ)
    (Wp : ℝ)
    (_ : ∀ (c : ℕ) (H' : ℝ), cp ≤ c → Wp ≤ H' → ∃ (d : ℕ) (Φ : QuadraticChartData d), (1 : ℕ)
      ≤ d ∧ QuadraticChartComplexity c H' Φ ∧ IsBoundedQuadraticChart Φ)
    (c₁ : ℕ)
    (C₁ : ℕ)
    (c₂a : ℕ)
    (Ca : ℕ)
    (q : ℝ)
    (_ : (2 : ℝ) < q)
    (Cqa : ℝ)
    (_ : ∀ {G : RealDyadicGrid} {J : ℤ × ℤ} {N : ℕ} {H : ℝ} {R : ℤ × ℤ}, R ∈ dyadicFiniteTree
      G J N → (1 : ℝ) ≤ H → ∀ {a i k b : Fin (4 : ℕ)}, a ≠ i → a ≠ k → a ≠ b → i ≠ k → i
      ≠ b → k ≠ b → ∀ (w : ℤ × ℤ → ℝ × ℝ → ℂ), (∀ (I : ℤ × ℤ), IsAdmissibleLocalKernel κ
      (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1) (w I)) → ∀ (f : Fin (4 : ℕ) →
      ℝ → ℂ), (∀ (l : Fin (4 : ℕ)), Measurable (f l)) → (∀ (l : Fin (4 : ℕ)), ∀ I ∈
      dyadicFiniteTree G J N, kernelHull G J N w I → eLpNorm (f l) (ENNReal.ofReal q)
      (normalizedIntervalMeasure (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1)) ≤
      (1 : ℝ≥0∞)) → ∀ (Xi Xk Xga Xgb : LowList G J N R (max c₂ cp) H), (∃ (d : ℕ) (Φ :
      QuadraticChartData d), (1 : ℕ) ≤ d ∧ QuadraticChartComplexity (max c₂ cp) H Φ ∧
      IsBoundedQuadraticChart Φ) → ∀ (zga zgb : ℤ × ℤ → ℝ → ℂ) {Cga Cgb : ℝ}, (0 : ℝ) ≤
      Cga → (0 : ℝ) ≤ Cgb → ((∀ (I : ℤ × ℤ), Measurable (zga I) ∧ MemLp (zga I) (2 :
      ℝ≥0∞) (volume.restrict (dyadicGridCell G I.1 I.2))) ∧ ∀ J' ∈ dyadicFiniteTree G J
      N, dyadicGridCell G J'.1 J'.2 ⊆ dyadicGridCell G R.1 R.2 → IsAdmissibleOpponent G
      J' (f a) zga Cga ∧ HasDepthEnergy G J' (f a) zga (1 : ℝ)) → ((∀ (I : ℤ × ℤ),
      Measurable (zgb I) ∧ MemLp (zgb I) (2 : ℝ≥0∞) (volume.restrict (dyadicGridCell G
      I.1 I.2))) ∧ ∀ J' ∈ dyadicFiniteTree G J N, dyadicGridCell G J'.1 J'.2 ⊆
      dyadicGridCell G R.1 R.2 → IsAdmissibleOpponent G J' (f b) zgb Cgb ∧
      HasDepthEnergy G J' (f b) zgb (1 : ℝ)) → ∀ (K₀ : ℕ) (Tc : Finset (ℤ × ℤ)), (∀ I ∈
      Tc, I ∈ dyadicFiniteTree G J N ∧ dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G R.1
      R.2 ∧ I.1 + (↑K₀ : ℤ) ≤ J.1 + (↑N : ℤ) ∧ (∀ᵐ (y : ℝ), y ∈ dyadicGridCell G I.1 I.2
      → zga I y = Xga.val I y) ∧ ∀ᵐ (y : ℝ), y ∈ dyadicGridCell G I.1 I.2 → zgb I y =
      Xgb.val I y) → (∀ I ∈ Tc, kernelHull G J N w I) → ∀ {Bd : ℝ}, (∃ (z₁ : ℤ × ℤ → ℝ →
      ℂ) (z₂ : ℤ × ℤ → ℝ → ℂ), IsBasicOn G R (dyadicRemainingDepth J N R) (1 : ℝ) Bd
      (max c₂ cp) H w z₁ ∧ IsBasicOn G R (dyadicRemainingDepth J N R) (1 : ℝ) Bd (max c₂
      cp) H w z₂ ∧ ∀ I ∈ Tc, ∀ᵐ (y : ℝ), y ∈ dyadicGridCell G I.1 I.2 → Xi.val I y = z₁
      I y - z₂ I y) → (∃ (z₁ : ℤ × ℤ → ℝ → ℂ) (z₂ : ℤ × ℤ → ℝ → ℂ), IsBasicOn G R
      (dyadicRemainingDepth J N R) (1 : ℝ) Bd (max c₂ cp) H w z₁ ∧ IsBasicOn G R
      (dyadicRemainingDepth J N R) (1 : ℝ) Bd (max c₂ cp) H w z₂ ∧ ∀ I ∈ Tc, ∀ᵐ (y : ℝ),
      y ∈ dyadicGridCell G I.1 I.2 → Xk.val I y = z₁ I y - z₂ I y) → IsBasicOn G R
      (dyadicRemainingDepth J N R) (1 : ℝ) Bd (max c₂ cp) H w zga → IsBasicOn G R
      (dyadicRemainingDepth J N R) (1 : ℝ) Bd (max c₂ cp) H w zgb → Bd ≤ (2 : ℝ) +
      (↑(Fintype.card Xi.Λ + Fintype.card Xk.Λ + Fintype.card Xga.Λ + Fintype.card
      Xgb.Λ) : ℝ) → (∀ I ∈ Tc, eLpNorm (Xi.val I) (2 : ℝ≥0∞) (normalizedIntervalMeasure
      (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1)) ≤ ENNReal.ofReal (2 : ℝ)) →
      (∀ I ∈ Tc, eLpNorm (Xk.val I) (2 : ℝ≥0∞) (normalizedIntervalMeasure
      (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1)) ≤ ENNReal.ofReal (2 : ℝ)) →
      (∀ I ∈ Tc, eLpNorm (Xga.val I) (2 : ℝ≥0∞) (normalizedIntervalMeasure
      (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1)) ≤ ENNReal.ofReal (1 : ℝ)) →
      (∀ I ∈ Tc, eLpNorm (Xgb.val I) (2 : ℝ≥0∞) (normalizedIntervalMeasure
      (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1)) ≤ ENNReal.ofReal (1 : ℝ)) → ∀
      {η₀ : ℝ}, (0 : ℝ) ≤ η₀ → (∀ I ∈ Tc, ∀ (s s' : Fin (4 : ℕ)), s ≠ s' → PairSmall
      (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1) (w I) s s' (slots4 a i k (f a
      - Xga.val I) (Xi.val I) (Xk.val I) (f b - Xgb.val I) s) (slots4 a i k (f a -
      Xga.val I) (Xi.val I) (Xk.val I) (f b - Xgb.val I) s') η₀) → ∀ (Bp ε : ℝ) (ka kb
      Ma Mb : ℕ), (1 : ℝ) ≤ Bp → (0 : ℝ) < ε → ε ≤ (1 : ℝ) → (1 : ℕ) ≤ ka → (1 : ℕ) ≤ kb
      → (16 : ℝ) * fitBudget Cqa Ca ka ^ (2 : ℕ) < (↑Ma : ℝ) → (16 : ℝ) * fitBudget Cqa
      Ca kb ^ (2 : ℕ) < (↑Mb : ℝ) →
    have D := max H (Real.exp ((↑C₁ : ℝ) * ((1 : ℝ) + Bp + Real.log H) ^ C₁));
    have Wa := Fintype.card Xi.Λ * Fintype.card Xk.Λ * ⌊D⌋₊ + Ma;
    have Wb := Fintype.card Xi.Λ * Fintype.card Xk.Λ * ⌊D⌋₊ + Mb;
    have S₀ := (1 : ℝ) + (↑(Fintype.card Xi.Λ) : ℝ) + (↑(Fintype.card Xk.Λ) : ℝ) +
      (↑(Fintype.card Xga.Λ) : ℝ) + (↑(Fintype.card Xgb.Λ) : ℝ);
    have Sp := (↑Wa : ℝ) * √((2 : ℝ) ^ K₀ / ε) + (1 : ℝ);
    ∃ (P : Finset ((ℤ × ℤ) × ℤ × ℤ)) (A : ↥P → ActiveSetup κ (max (max c₁ (max c₂ cp))
      c₂a)), ∑ p : ↥P, dyadicGridLength G (A p).R.1 ≤ (8 / 3 : ℝ) * dyadicGridLength G
      R.1 ∧ (∀ I ∈ Tc, ∃ (p : ↥P), I ∈ (A p).cells) ∧ (∀ (p p' : ↥P), ∀ I ∈ (A p).cells,
      I ∈ (A p').cells → p = p') ∧ ∀ (p : ↥P), (A p).cells ⊆ Tc ∧ (∀ I ∈ (A p).cells, ∀
      J' ∈ Tc, dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G J'.1 J'.2 → dyadicGridCell G
      J'.1 J'.2 ⊆ dyadicGridCell G (A p).R.1 (A p).R.2 → J' ∈ (A p).cells) ∧ (A p).G = G
      ∧ (A p).w = w ∧ (A p).a = a ∧ (A p).b = b ∧ (A p).R ∈ dyadicFiniteTree G J N ∧
      dyadicGridCell G (A p).R.1 (A p).R.2 ⊆ dyadicGridCell G R.1 R.2 ∧ (A p).H = max D
      (max (fitBudget Cqa Ca ka) (fitBudget Cqa Ca kb)) ∧ (A p).Dc = √ε⁻¹ ∧ (A p).S = (2
      : ℝ) ∧ (A p).η = (4 : ℝ) * η₀ ∧ Fintype.card (A p).L = Fintype.card Xi.Λ +
      Fintype.card Xk.Λ + (Wa + Fintype.card Xga.Λ) + (Wb + Fintype.card Xgb.Λ) ∧ ∑ I ∈
      (A p).cells, dyadicGridLength G I.1 * ‖localProgressionForm (dyadicGridLength G
      I.1) (w I) (slots4 a i k (f a - Xga.val I) (Xi.val I) (Xk.val I) (f b - Xgb.val
      I)) - (A p).Hf I ((A p).Y I)‖ ≤ baseErr κ (Fintype.card Xi.Λ) (Fintype.card Xk.Λ)
      D Bp ε K₀ Wa Wb Cga Cgb * dyadicGridLength G (A p).R.1 ∧ (∀ I ∈ (A p).cells, ∀ (s
      s' : Fin (4 : ℕ)), s ≠ s' → PairSmall (dyadicGridLeft G I.1 I.2) (dyadicGridLength
      G I.1) (w I) s s' ((A p).Y I s) ((A p).Y I s') (η₀ + ((2 : ℝ) + (2 : ℝ) * S₀) *
      (Real.exp (-(↑ka : ℝ)) + Real.exp (-(↑kb : ℝ))) + ((1 : ℝ) + Sp) * Real.exp (-(↑kb
      : ℝ)))) ∧ (∀ I ∈ (A p).cells, ∀ (l : Fin (4 : ℕ)), (eLpNorm ((A p).Y I l) (2 :
      ℝ≥0∞) ((A p).μ I)).toReal ≤ (2 : ℝ)) ∧ (∀ (l : Fin (4 : ℕ)), ∑ I ∈ (A p).cells,
      dyadicGridLength G I.1 * (eLpNorm ((A p).U l I) (2 : ℝ≥0∞) ((A p).μ I)).toReal ^
      (2 : ℕ) ≤ (↑K₀ : ℝ) ^ (2 : ℕ) * dyadicGridLength G (A p).R.1) ∧ ∑ I ∈ (A p).cells,
      dyadicGridLength G I.1 * ‖(A p).Hf I ((A p).z (3 : Fin (4 : ℕ)) I)‖ ≤ η₀ * ((↑K₀ :
      ℝ) ^ (2 : ℕ) * dyadicGridLength G (A p).R.1) ∧ (A p).HasColumnRep (1 : ℝ) ∧ (A
      p).SubRootProps η₀ ((↑K₀ : ℝ) ^ (2 : ℕ)))
    (G : RealDyadicGrid)
    (J : ℤ × ℤ)
    (N : ℕ)
    (w : ℤ × ℤ → ℝ × ℝ → ℂ)
    (_ : ∀ (I : ℤ × ℤ), IsAdmissibleLocalKernel κ (dyadicGridLeft G I.1 I.2)
      (dyadicGridLength G I.1) (w I))
    (f : Fin (4 : ℕ) → ℝ → ℂ)
    (_ : ∀ (l : Fin (4 : ℕ)), Measurable (f l))
    (_ : ∀ (l : Fin (4 : ℕ)), ∀ I ∈ dyadicFiniteTree G J N, I = J ∨ kernelHull G J N w I →
      eLpNorm (f l) (ENNReal.ofReal q) (normalizedIntervalMeasure (dyadicGridLeft G I.1
      I.2) (dyadicGridLength G I.1)) ≤ (1 : ℝ≥0∞))
    (Bf : ℕ → ℝ)
    (kk : ℕ → ℕ)
    (M : ℕ → ℕ)
    (roots : ℕ → Finset (ℤ × ℤ))
    (seg : ℕ → ℤ × ℤ → ℤ × ℤ)
    (n : ℕ → ℤ × ℤ → ℕ)
    (a : ℕ → ℤ × ℤ → ℕ → ℝ → ℂ)
    (g : ℕ → ℤ × ℤ → ℝ → ℂ)
    (cnt : ℕ → ℤ × ℤ → ℤ × ℤ → ℕ)
    (atm : ℕ → ℤ × ℤ → ℤ × ℤ → ℕ → ℝ → ℂ)
    (_ : ∀ (ℓ : ℕ), IsAdaptiveFit c₂ (Bf ℓ) G J N w (stagPos ℓ) q (f (stagPos ℓ)) (kk ℓ) (M
      ℓ) (roots ℓ) (seg ℓ) (n ℓ) (a ℓ) (g ℓ) ∧ IsAttemptData c₂ (Bf ℓ) G J N (M ℓ)
      (roots ℓ) (seg ℓ) (n ℓ) (a ℓ) (cnt ℓ) (atm ℓ) ∧ IsFitOpponent G J N (f (stagPos
      ℓ)) (roots ℓ) (seg ℓ) (g ℓ) (fitOpponentConst (M ℓ)) (max (2 : ℝ) (↑(M ℓ) : ℝ)) c₂
      (Bf ℓ))
    (u : ℕ)
    (t : ℕ)
    (hut : u < t)
    (Hc : ℝ)
    (Mt : ℕ)
    (_ : ∀ ℓ ≤ t, M ℓ ≤ Mt)
    (η₀ : ℝ)
    (_ : (0 : ℝ) ≤ η₀)
    (_ : ∀ I ∈ dyadicFiniteTree G J N, kernelHull G J N w I → ∀ (s s' : Fin (4 : ℕ)), s ≠ s'
      → PairSmall (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1) (w I) s s'
      (stagTuple f g u t I s) (stagTuple f g u t I s') η₀)
    (_ : ∀ I ∈ dyadicFiniteTree G J N, kernelHull G J N w I → ∀ (l : Fin (4 : ℕ)), eLpNorm
      (stagTuple f g u t I l) (2 : ℝ≥0∞) (normalizedIntervalMeasure (dyadicGridLeft G
      I.1 I.2) (dyadicGridLength G I.1)) ≤ ENNReal.ofReal (2 : ℝ))
    (Bp : ℝ)
    (ε : ℝ)
    (K₀ : ℕ)
    (ka : ℕ)
    (kb : ℕ)
    (Ma : ℕ)
    (Mb : ℕ)
    (_ : (1 : ℝ) ≤ Bp)
    (_ : (0 : ℝ) < ε)
    (_ : ε ≤ (1 : ℝ))
    (_ : (1 : ℕ) ≤ ka)
    (_ : (1 : ℕ) ≤ kb)
    (_ : (16 : ℝ) * fitBudget Cqa Ca ka ^ (2 : ℕ) < (↑Ma : ℝ))
    (_ : (16 : ℝ) * fitBudget Cqa Ca kb ^ (2 : ℕ) < (↑Mb : ℝ)),
  let H : ℝ :=
    max Hc Wp ^ (6 : ℕ)
  let D : ℝ :=
    max H (Real.exp ((↑C₁ : ℝ) * ((1 : ℝ) + Bp + Real.log H) ^ C₁))
  let Wa : ℕ :=
    (2 : ℕ) * Mt * ((2 : ℕ) * Mt) * ⌊D⌋₊ + Ma
  let Wb : ℕ :=
    (2 : ℕ) * Mt * ((2 : ℕ) * Mt) * ⌊D⌋₊ + Mb
  let E : ℝ :=
    baseErr κ ((2 : ℕ) * Mt) ((2 : ℕ) * Mt) D Bp ε K₀ Wa Wb (fitOpponentConst Mt)
      (fitOpponentConst Mt)
  let S₀ : ℝ :=
    (1 : ℝ) + (6 : ℝ) * (↑Mt : ℝ)
  let Sp : ℝ :=
    (↑Wa : ℝ) * √((2 : ℝ) ^ K₀ / ε) + (1 : ℝ)
  let i : Fin (4 : ℕ) :=
    stagPos u
  let k : Fin (4 : ℕ) :=
    stagPos t
  ∀ (_ : i ≠ k)
    (sa : Fin (4 : ℕ))
    (sb : Fin (4 : ℕ))
    (_ : sa ≠ sb)
    (_ : sa ≠ i)
    (_ : sa ≠ k)
    (_ : sb ≠ i)
    (_ : sb ≠ k),
  let la : ℕ :=
    StaggerCell.lastLevel sa t
  ∀ (hla2 : la < t)
    (_ : (1 : ℕ) ≤ la → stagPos la = sa),
  let lb : ℕ :=
    StaggerCell.lastLevel sb t
  ∀ (hlb2 : lb < t)
    (_ : (1 : ℕ) ≤ lb → stagPos lb = sb),
  let Lset : Finset ℕ :=
    {u, u - (4 : ℕ), t, t - (4 : ℕ), la, lb}
  ∀ (_ : Lset = {u, u - (4 : ℕ), t, t - (4 : ℕ), la, lb})
    (hLne : Lset.Nonempty)
    (_ : SegData G J N seg Lset),
  let Rf : ℤ × ℤ → ℤ × ℤ :=
    firstRoot seg Lset hLne
  let Tup : Finset (ℤ × ℤ) :=
    {I ∈ dyadicFiniteTree G J N | I.1 + (↑K₀ : ℤ) ≤ J.1 + (↑N : ℤ) ∧ kernelHull G J N w
      I}
  let Rs : Finset (ℤ × ℤ) :=
    Finset.image Rf Tup
  ∀ (hRtree : ∀ I ∈ dyadicFiniteTree G J N, Rf I ∈ dyadicFiniteTree G J N ∧ dyadicGridCell G I.1
      I.2 ⊆ dyadicGridCell G (Rf I).1 (Rf I).2)
    (_ : ∀ R ∈ Rs, R ∈ dyadicFiniteTree G J N)
    (_ : (1 : ℝ) ≤ Wp)
    (hHl : ∀ ℓ ≤ t, max (Bf ℓ) Wp ^ (6 : ℕ) ≤ H)
    (_ : (1 : ℝ) ≤ H)
    (_ : Wp ≤ H)
    (X : (ℓ : ℕ) → (R : ℤ × ℤ) → R ∈ dyadicFiniteTree G J N → LowList G J N R (max c₂ cp)
      (max (Bf ℓ) Wp ^ (6 : ℕ))),
  let Y : (ℓ : ℕ) → ℓ ≤ t → (R : ℤ × ℤ) → R ∈ dyadicFiniteTree G J N → LowList G J N R (max c₂
      cp) H :=
    fun ℓ hℓ R hR => (X ℓ R hR).mono le_rfl (hHl ℓ hℓ)
  ∀ (_ : ∀ (ℓ : ℕ) (hℓ : ℓ ≤ t) (R : ℤ × ℤ) (hR : R ∈ dyadicFiniteTree G J N), ∀ I ∈
      dyadicFiniteTree G J N, dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G R.1 R.2 → seg
      ℓ I = seg ℓ R → kernelHull G J N w I → ∀ (y : ℝ), (Y ℓ hℓ R hR).val I y = g ℓ I y)
    (_ : ∀ (ℓ : ℕ) (hℓ : ℓ ≤ t) (R : ℤ × ℤ) (hR : R ∈ dyadicFiniteTree G J N), Fintype.card
      (Y ℓ hℓ R hR).Λ = M ℓ)
    (hu4 : u - (4 : ℕ) ≤ t)
    (ht4 : t - (4 : ℕ) ≤ t),
  let Xi : (R : ℤ × ℤ) → R ∈ dyadicFiniteTree G J N → LowList G J N R (max c₂ cp) H :=
    fun R hR => if u ≤ 4 then Y u hut.le R hR else (Y u hut.le R hR).sub (Y (u - 4) hu4
      R hR)
  let Xk : (R : ℤ × ℤ) → R ∈ dyadicFiniteTree G J N → LowList G J N R (max c₂ cp) H :=
    fun R hR => if t ≤ 4 then Y t le_rfl R hR else (Y t le_rfl R hR).sub (Y (t - 4) ht4
      R hR)
  let Xga : (R : ℤ × ℤ) → R ∈ dyadicFiniteTree G J N → LowList G J N R (max c₂ cp) H :=
    fun R hR => if 1 ≤ la then Y la hla2.le R hR else LowList.empty
  let Xgb : (R : ℤ × ℤ) → R ∈ dyadicFiniteTree G J N → LowList G J N R (max c₂ cp) H :=
    fun R hR => if 1 ≤ lb then Y lb hlb2.le R hR else LowList.empty
  ∀ (_ : u ∈ Lset)
    (_ : u - (4 : ℕ) ∈ Lset)
    (_ : t ∈ Lset)
    (_ : t - (4 : ℕ) ∈ Lset)
    (_ : la ∈ Lset)
    (_ : lb ∈ Lset)
    (_ : ∀ I ∈ dyadicFiniteTree G J N, ∀ ℓ ∈ Lset, seg ℓ I = seg ℓ (Rf I))
    (_ : ∀ (I : ℤ × ℤ) (hI : I ∈ dyadicFiniteTree G J N), kernelHull G J N w I → slots4 sa i
      k (f sa - (Xga (Rf I) (hRtree I hI).left).val I) ((Xi (Rf I) (hRtree I
      hI).left).val I) ((Xk (Rf I) (hRtree I hI).left).val I) (f sb - (Xgb (Rf I)
      (hRtree I hI).left).val I) = stagTuple f g u t I),
  ∃ (ι : Type) (_ : Fintype ι) (A : ι → ActiveSetup κ (max (max c₁ (max c₂ cp)) c₂a)),
    ∑ p : ι, dyadicGridLength G (A p).R.1 ≤ (91 / 3 : ℝ) * dyadicGridLength G J.1 ∧ (∀
    (p p' : ι), ∀ I ∈ (A p).cells, I ∈ (A p').cells → p = p') ∧ (∀ (p : ι), (A
    p).cells ⊆ dyadicFiniteTree G J N ∧ (∀ I ∈ (A p).cells, kernelHull G J N w I) ∧ (∀
    I ∈ (A p).cells, ∀ (J' : ℤ × ℤ), dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G J'.1
    J'.2 → dyadicGridCell G J'.1 J'.2 ⊆ dyadicGridCell G (A p).R.1 (A p).R.2 → J' ∈ (A
    p).cells) ∧ (A p).G = G ∧ (A p).w = w ∧ (A p).R ∈ dyadicFiniteTree G J N ∧ (A p).H
    = max D (max (fitBudget Cqa Ca ka) (fitBudget Cqa Ca kb)) ∧ (A p).Dc = √ε⁻¹ ∧ (A
    p).S = (2 : ℝ) ∧ (A p).η = (4 : ℝ) * η₀ ∧ Fintype.card (A p).L ≤ (6 : ℕ) * Mt + Wa
    + Wb ∧ (∀ I ∈ (A p).cells, ∀ (s s' : Fin (4 : ℕ)), s ≠ s' → PairSmall
    (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1) (w I) s s' ((A p).Y I s) ((A
    p).Y I s') (η₀ + ((2 : ℝ) + (2 : ℝ) * S₀) * (Real.exp (-(↑ka : ℝ)) + Real.exp
    (-(↑kb : ℝ))) + ((1 : ℝ) + Sp) * Real.exp (-(↑kb : ℝ)))) ∧ (∀ I ∈ (A p).cells, ∀
    (l : Fin (4 : ℕ)), (eLpNorm ((A p).Y I l) (2 : ℝ≥0∞) ((A p).μ I)).toReal ≤ (2 :
    ℝ)) ∧ (∀ (l : Fin (4 : ℕ)), ∑ I ∈ (A p).cells, dyadicGridLength G I.1 * (eLpNorm
    ((A p).U l I) (2 : ℝ≥0∞) ((A p).μ I)).toReal ^ (2 : ℕ) ≤ (↑K₀ : ℝ) ^ (2 : ℕ) *
    dyadicGridLength G (A p).R.1) ∧ ∑ I ∈ (A p).cells, dyadicGridLength G I.1 * ‖(A
    p).Hf I ((A p).z (3 : Fin (4 : ℕ)) I)‖ ≤ η₀ * ((↑K₀ : ℝ) ^ (2 : ℕ) *
    dyadicGridLength G (A p).R.1) ∧ (A p).HasColumnRep (1 : ℝ) ∧ (A p).SubRootProps η₀
    ((↑K₀ : ℝ) ^ (2 : ℕ))) ∧ ∑ I ∈ dyadicFiniteTree G J N, dyadicGridLength G I.1 *
    ‖localProgressionForm (dyadicGridLength G I.1) (w I) (stagTuple f g u t I)‖ ≤ ∑ p
    : ι, ∑ I ∈ (A p).cells, dyadicGridLength G I.1 * ‖(A p).Hf I ((A p).Y I)‖ + E *
    ((91 / 3 : ℝ) * dyadicGridLength G J.1)

private theorem baseTuple_hbpack : BaseTupleHbpackStatement := by
  classical
  intro κ c₂ cp Wp c₁ C₁ c₂a Ca Cqa G J N w f Bf seg u t hut Hc η₀ Bp ε K₀ ka kb H D i k sa sb la
    hla2 lb hlb2 Lset hLne Rf hHl X Y hu4 ht4 Xi Xk Xga Xgb hRsumT d₀ Bot hBot anc hanc Rb hRb Bs
    hQ AB hAB
  have e : ∑ R' : Bs, dyadicGridLength G (AB R'.1 R'.2).R.1 =
      ∑ R' ∈ Bs, dyadicGridLength G R'.1 := by
    rw [← Finset.sum_coe_sort Bs]
    refine Finset.sum_congr rfl fun R' _ => ?_
    rw [(hAB R'.1 R'.2).2.1]
  rw [e]
  have hsub : Bs ⊆ Bot.image Rf ∪ (dyadicFiniteTree G J N).filter (fun c => c.1 = d₀) := by
    intro R' hR'
    obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hR'
    obtain ⟨hIt, hdI, -⟩ := hBot I hI
    by_cases hd : d₀ ≤ (Rf I).1
    · have e1 : Rb I = Rf I := by simp only [Rb, hd, ↓reduceIte]
      rw [e1]
      exact Finset.mem_union_left _ (Finset.mem_image_of_mem Rf hI)
    · have e1 : Rb I = anc I := by simp only [Rb, hd, ↓reduceIte]
      refine Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨(hRb I hIt hdI).1, ?_⟩)
      rw [e1]
      exact (hanc I hdI).1
  have h1 := hRsumT Bot fun I hI => (hBot I hI).1
  have h2 := sum_tree_depth_le G J N d₀
  have h3 : 0 ≤ ∑ c ∈ Bot.image Rf ∩ (dyadicFiniteTree G J N).filter (fun c => c.1 = d₀),
      dyadicGridLength G c.1 := Finset.sum_nonneg fun c _ => (dyadicGridLength_pos G c.1).le
  have h4 := Finset.sum_union_inter (s₁ := Bot.image Rf)
    (s₂ := (dyadicFiniteTree G J N).filter (fun c => c.1 = d₀))
    (f := fun c : ℤ × ℤ => dyadicGridLength G c.1)
  have h5 := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (f := fun c : ℤ × ℤ => dyadicGridLength G c.1) fun c _ _ => (dyadicGridLength_pos G c.1).le
  linarith
-- all active setups

private theorem baseTuple_hcards : BaseTupleHcardsStatement := by
  classical
  intro c₂ cp Wp C₁ G J N Bf M u t hut Hc Mt hMt Bp Ma Mb H D Wa Wb sa sb la hla2 lb hlb2 hHl X Y
    hYcard hu4 ht4 Xi Xk Xga Xgb R hRT
  have hci : Fintype.card (Xi R hRT).Λ ≤ 2 * Mt := by
    by_cases hu4' : u ≤ 4
    · have e : Xi R hRT = Y u hut.le R hRT := by simp only [Xi, hu4', ↓reduceIte]
      rw [e, hYcard u hut.le R hRT]; have := hMt u hut.le; omega
    · have e : Xi R hRT = (Y u hut.le R hRT).sub (Y (u - 4) hu4 R hRT) := by
        simp only [Xi, hu4', ↓reduceIte]
      rw [e, LowList.sub_card, hYcard u hut.le R hRT, hYcard (u - 4) hu4 R hRT]
      have := hMt u hut.le; have := hMt (u - 4) hu4; omega
  have hck : Fintype.card (Xk R hRT).Λ ≤ 2 * Mt := by
    by_cases ht4' : t ≤ 4
    · have e : Xk R hRT = Y t le_rfl R hRT := by simp only [Xk, ht4', ↓reduceIte]
      rw [e, hYcard t le_rfl R hRT]; have := hMt t le_rfl; omega
    · have e : Xk R hRT = (Y t le_rfl R hRT).sub (Y (t - 4) ht4 R hRT) := by
        simp only [Xk, ht4', ↓reduceIte]
      rw [e, LowList.sub_card, hYcard t le_rfl R hRT, hYcard (t - 4) ht4 R hRT]
      have := hMt t le_rfl; have := hMt (t - 4) ht4; omega
  have hcga : Fintype.card (Xga R hRT).Λ ≤ Mt := by
    by_cases h1 : 1 ≤ la
    · have e : Xga R hRT = Y la hla2.le R hRT := by simp only [Xga, h1, ↓reduceIte]
      rw [e, hYcard la hla2.le R hRT]; exact hMt la hla2.le
    · have e : Xga R hRT = LowList.empty := by simp only [Xga, h1, ↓reduceIte]
      rw [e, LowList.empty_card]; exact Nat.zero_le _
  have hcgb : Fintype.card (Xgb R hRT).Λ ≤ Mt := by
    by_cases h1 : 1 ≤ lb
    · have e : Xgb R hRT = Y lb hlb2.le R hRT := by simp only [Xgb, h1, ↓reduceIte]
      rw [e, hYcard lb hlb2.le R hRT]; exact hMt lb hlb2.le
    · have e : Xgb R hRT = LowList.empty := by simp only [Xgb, h1, ↓reduceIte]
      rw [e, LowList.empty_card]; exact Nat.zero_le _
  have hWa : Fintype.card (Xi R hRT).Λ * Fintype.card (Xk R hRT).Λ * ⌊D⌋₊ + Ma ≤ Wa :=
    Nat.add_le_add_right (Nat.mul_le_mul_right _ (Nat.mul_le_mul hci hck)) _
  have hWb : Fintype.card (Xi R hRT).Λ * Fintype.card (Xk R hRT).Λ * ⌊D⌋₊ + Mb ≤ Wb :=
    Nat.add_le_add_right (Nat.mul_le_mul_right _ (Nat.mul_le_mul hci hck)) _
  exact ⟨hci, hck, hcga, hcgb, hWa, hWb⟩

private theorem baseTuple_hslots : BaseTupleHslotsStatement := by
  classical
  intro c₂ cp Wp G J N w f Bf seg g u t hut Hc H i hi_def k hpos hk_def sa sb hab hai hak hbi hbk
    la hla2 hla_def lb hlb2 hlb_def Lset hLne Rf hRtree hHl X Y hYval hu4 ht4 Xi Xk Xga Xgb huL
    hu4L htL ht4L hlaL hlbL hcellR I hI hIH
  have hIR := (hRtree I hI).2
  have hv : ∀ ℓ (hℓ : ℓ ≤ t), ℓ ∈ Lset → ∀ y,
      (Y ℓ hℓ (Rf I) (hRtree I hI).1).val I y = g ℓ I y := fun ℓ hℓ hℓL y =>
    hYval ℓ hℓ _ _ I hI hIR (hcellR I hI ℓ hℓL) hIH y
  funext l y
  rcases fin_four_cover hai hak hab hpos hbi.symm hbk.symm l with h | h | h | h <;> rw [h]
  · rw [slots4_a]
    by_cases h1 : 1 ≤ la
    · simp only [stagTuple, ← hi_def, ← hk_def, ← hla_def, hai, hak, ↓reduceIte, h1,
        Pi.sub_apply]
      rw [show (Xga (Rf I) (hRtree I hI).1).val I y = g la I y by
        simp only [Xga, h1, ↓reduceIte]; exact hv la hla2.le hlaL y]
    · simp only [stagTuple, ← hi_def, ← hk_def, ← hla_def, hai, hak, ↓reduceIte, h1,
        Pi.sub_apply, Xga, LowList.empty_val, Pi.zero_apply]
  · rw [slots4_i hai]
    simp only [stagTuple, ← hi_def, ↓reduceIte]
    by_cases hu4' : u ≤ 4
    · simp only [Xi, hu4', ↓reduceIte, sub_zero]
      exact hv u hut.le huL y
    · simp only [Xi, hu4', ↓reduceIte, Pi.sub_apply, LowList.sub_val]
      rw [hv u hut.le huL y, hv (u - 4) hu4 hu4L y]
  · rw [slots4_k hak hpos]
    by_cases ht4' : t ≤ 4
    · simp only [stagTuple, ← hi_def, ← hk_def, Ne.symm hpos, ↓reduceIte, ht4', sub_zero]
      simp only [Xk, ht4', ↓reduceIte]
      exact hv t le_rfl htL y
    · simp only [stagTuple, ← hi_def, ← hk_def, Ne.symm hpos, ↓reduceIte, ht4', Pi.sub_apply]
      simp only [Xk, ht4', ↓reduceIte, LowList.sub_val]
      rw [hv t le_rfl htL y, hv (t - 4) ht4 ht4L y]
  · rw [slots4_b hab hbi.symm hbk.symm]
    by_cases h1 : 1 ≤ lb
    · simp only [stagTuple, ← hi_def, ← hk_def, ← hlb_def, hbi, hbk, ↓reduceIte, h1,
        Pi.sub_apply]
      rw [show (Xgb (Rf I) (hRtree I hI).1).val I y = g lb I y by
        simp only [Xgb, h1, ↓reduceIte]; exact hv lb hlb2.le hlbL y]
    · simp only [stagTuple, ← hi_def, ← hk_def, ← hlb_def, hbi, hbk, ↓reduceIte, h1,
        Pi.sub_apply, Xgb, LowList.empty_val, Pi.zero_apply]
-- the low arguments are the tuple entries

private theorem baseTuple_conclusion_39 : BaseTupleConclusion39Statement := by
  classical
  intro κ c₂ cp Wp c₁ C₁ c₂a Ca Cqa G J N w f Bf M seg u t hut Hc Mt η₀ Bp ε K₀ ka kb Ma Mb hε0 H
    D Wa Wb S₀ Sp i k sa sb la hla2 lb hlb2 Lset hLne hsegd Rf Tup Rs hRtree hRsT hHl X Y hu4 ht4
    Xi Xk Xga Xgb P A hPA ιt A' hcellsT hcards d₀ Bot hBot anc hanc Rb hRbu Bs hBsT hQ hTc AB hAB
    ι Atot
  -- the bounds of each setup
  rintro (⟨⟨R, hR⟩, p⟩ | ⟨R', hR'⟩)
  swap
  · dsimp only [Atot, Sum.elim_inr]
    obtain ⟨hG', hR'', hcells', hw', -, -, hH', hDc', hS', hη', hcard', -, hpairs', hsize',
      hside', htwo', hcol', hsr'⟩ := hAB R' hR'
    rw [hcells', hR'']
    refine ⟨fun I hI => (hTc R' hR' I hI).1, fun I hI => (hTc R' hR' I hI).2.1, ?_, hG', hw',
      (hBsT R' hR').1, hH', hDc', hS', hη', ?_, ?_, hsize', hside', htwo', hcol', hsr'⟩
    · intro I hI J' hIJ hJR
      obtain ⟨hIB, hIR⟩ := Finset.mem_filter.mp hI
      obtain ⟨hIt, hdI, hIH⟩ := hBot I hIB
      obtain ⟨hR'T, hdR'⟩ := hBsT R' hR'
      have hJt : J' ∈ dyadicFiniteTree G J N := dyadicFiniteTree_ancestor_mem G J I J' N hIt hIJ
        (hJR.trans ((dyadicFiniteTree_mem_iff G J R' N).mp hR'T).1)
      have hdJ : d₀ ≤ J'.1 := hdR'.trans (dyadicGridCell_depth_le_of_subset G J' R' hJR)
      refine Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hJt, by omega, hIH.mono hIJ⟩, ?_⟩
      rw [← hIR]
      exact hRbu I hIt hdI J' hJt hIJ (by rw [hIR]; exact hJR)
    · refine le_trans (le_of_eq hcard') ?_
      obtain ⟨hci, hck, hcga, hcgb, -, -⟩ := hcards (Rf R') (hQ R' hR')
      simp only [LowList.reroot_card]
      omega
    · intro I hI s s' hss
      refine (hpairs' I hI s s' hss).mono ?_
      have hS₀ : 0 ≤ S₀ := by simp only [S₀]; positivity
      have hSp : 0 ≤ Sp := by simp only [Sp]; positivity
      have hea := (Real.exp_pos (-(ka : ℝ))).le
      have heb := (Real.exp_pos (-(kb : ℝ))).le
      have k1 := mul_nonneg (by linarith : (0 : ℝ) ≤ 2 + 2 * S₀) (add_nonneg hea heb)
      have k2 := mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + Sp) heb
      linarith
  dsimp only [Atot, Sum.elim_inl]
  obtain ⟨hcells, hclos, hG, hw', -, -, hRp, hRsub, hH', hDc, hS, hη, hcard, -, hpairs, hsize,
    hside, htwo, hcol, hsr⟩ := (hPA R hR).2.2.2 p
  have hRT := hRsT R hR
  obtain ⟨hci, hck, hcga, hcgb, hWa, hWb⟩ := hcards R hRT
  have hanc : ∀ I ∈ (A R hR p).cells, ∀ J' : ℤ × ℤ,
      dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G J'.1 J'.2 →
      dyadicGridCell G J'.1 J'.2 ⊆ dyadicGridCell G (A R hR p).R.1 (A R hR p).R.2 →
      J' ∈ (A R hR p).cells := by
    intro I hI J' hIJ hJR
    obtain ⟨hIt, hIK, hRI, hIH⟩ := hcellsT R hR p I hI
    have hJR' := hJR.trans hRsub
    have hRJ := (hRtree I hIt).1
    have hdIJ := dyadicGridCell_depth_le_of_subset G I J' hIJ
    have hJt : J' ∈ dyadicFiniteTree G J N := (dyadicFiniteTree_mem_iff G J J' N).mpr
      ⟨hJR'.trans (((dyadicFiniteTree_mem_iff G J R N).mp (hRsT R hR)).1),
        by have := ((dyadicFiniteTree_mem_iff G J I N).mp hIt).2; omega⟩
    have hRf : Rf J' = R := by
      rw [← hRI]
      exact firstRoot_between (hL := hLne) hsegd hIt hJt hIJ
        (by rw [show firstRoot seg Lset hLne I = R from hRI]; exact hJR')
    refine hclos I hI J' (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hJt, by omega,
      hIH.mono hIJ⟩, hRf⟩) hIJ hJR
  refine ⟨fun I hI => (hcellsT R hR p I hI).1, fun I hI => (hcellsT R hR p I hI).2.2.2, hanc,
    hG, hw', hRp, hH', hDc, hS, hη, ?_, ?_, hsize, hside, htwo, hcol, hsr⟩
  · have hcard' : Fintype.card (A R hR p).L = Fintype.card (Xi R hRT).Λ +
        Fintype.card (Xk R hRT).Λ +
        ((Fintype.card (Xi R hRT).Λ * Fintype.card (Xk R hRT).Λ * ⌊D⌋₊ + Ma) +
          Fintype.card (Xga R hRT).Λ) +
        ((Fintype.card (Xi R hRT).Λ * Fintype.card (Xk R hRT).Λ * ⌊D⌋₊ + Mb) +
          Fintype.card (Xgb R hRT).Λ) := hcard
    change Fintype.card (A R hR p).L ≤ _
    rw [hcard']
    omega
  · intro I hI s s' hss
    refine (hpairs I hI s s' hss).mono ?_
    have hS₀ : (1 : ℝ) + Fintype.card (Xi R hRT).Λ + Fintype.card (Xk R hRT).Λ +
        Fintype.card (Xga R hRT).Λ + Fintype.card (Xgb R hRT).Λ ≤ S₀ := by
      have h1 : (Fintype.card (Xi R hRT).Λ : ℝ) ≤ 2 * Mt := by exact_mod_cast hci
      have h2 : (Fintype.card (Xk R hRT).Λ : ℝ) ≤ 2 * Mt := by exact_mod_cast hck
      have h3 : (Fintype.card (Xga R hRT).Λ : ℝ) ≤ Mt := by exact_mod_cast hcga
      have h4 : (Fintype.card (Xgb R hRT).Λ : ℝ) ≤ Mt := by exact_mod_cast hcgb
      simp only [S₀]; linarith
    have hSp : ((Fintype.card (Xi R hRT).Λ * Fintype.card (Xk R hRT).Λ * ⌊D⌋₊ + Ma : ℕ) : ℝ) *
        Real.sqrt (2 ^ K₀ / ε) + 1 ≤ Sp := by
      have : ((Fintype.card (Xi R hRT).Λ * Fintype.card (Xk R hRT).Λ * ⌊D⌋₊ + Ma : ℕ) : ℝ) ≤
          (Wa : ℝ) := by exact_mod_cast hWa
      simp only [Sp]
      have := mul_le_mul_of_nonneg_right this (Real.sqrt_nonneg (2 ^ K₀ / ε))
      linarith only [this]
    have hea := (Real.exp_pos (-(ka : ℝ))).le
    have heb := (Real.exp_pos (-(kb : ℝ))).le
    have k1 := mul_le_mul_of_nonneg_right (show 2 + 2 * ((1 : ℝ) + Fintype.card (Xi R hRT).Λ +
      Fintype.card (Xk R hRT).Λ + Fintype.card (Xga R hRT).Λ + Fintype.card (Xgb R hRT).Λ) ≤
        2 + 2 * S₀ by linarith only [hS₀]) (add_nonneg hea heb)
    have k2 := mul_le_mul_of_nonneg_right (show 1 + (((Fintype.card (Xi R hRT).Λ *
      Fintype.card (Xk R hRT).Λ * ⌊D⌋₊ + Ma : ℕ) : ℝ) * Real.sqrt (2 ^ K₀ / ε) + 1) ≤ 1 + Sp by
        linarith only [hSp]) heb
    push_cast at k1 k2 ⊢
    linarith only [k1, k2]

private theorem baseTuple_conclusion_40 : BaseTupleConclusion40Statement := by
  classical
  intro κ c₂ cp Wp c₁ C₁ c₂a Ca q Cqa G J N w f Bf kk M roots seg n a g cnt atm hfit u t hut Hc Mt
    hMt η₀ Bp ε K₀ ka kb Ma Mb H D Wa Wb E i k sa sb la hla2 lb hlb2 Lset hLne Rf Tup Rs hRtree
    hRsT hHl hH1 X Y hu4 ht4 Xi Xk Xga Xgb hslots P A hPA ιt A' hcellsT hcards hpack d₀ Bot
    hBot_def anc Rb Bs hQ hslotsB AB hAB ι Atot
  -- the tuple sum
  set F : ℤ × ℤ → ℝ := fun I => dyadicGridLength G I.1 *
    ‖localProgressionForm (dyadicGridLength G I.1) (w I) (stagTuple f g u t I)‖ with hF_def
  have hD0 : (0 : ℝ) ≤ D := le_trans (by linarith) (le_max_left H _)
  have hE0 : 0 ≤ E := baseErr_nonneg κ _ _ Bp _ _ _ hD0 (fitOpponentConst_nonneg _)
    (fitOpponentConst_nonneg _)
  have hgm : ∀ ℓ, ∀ I ∈ dyadicFiniteTree G J N, Measurable (g ℓ I) := fun ℓ I hI =>
    ((hfit ℓ).1.2.2.2.2 I hI).2.2.2.2.2.2.1
  -- the cells of the first-level roots
  have hRmap : ∀ I ∈ Tup, Rf I ∈ Rs := fun I hI => Finset.mem_image_of_mem Rf hI
  have htop : ∑ I ∈ Tup, F I ≤
      ∑ x : ιt, ∑ I ∈ (A' x).cells, dyadicGridLength G I.1 * ‖(A' x).Hf I ((A' x).Y I)‖ +
        E * ∑ x : ιt, dyadicGridLength G (A' x).R.1 := by
    rw [← Finset.sum_fiberwise_of_maps_to hRmap, ← Finset.sum_coe_sort Rs]
    rw [Fintype.sum_sigma, Fintype.sum_sigma, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun R _ => ?_
    obtain ⟨R, hR⟩ := R
    obtain ⟨-, hcover, hdisj, hAp⟩ := hPA R hR
    have hunion : Tup.filter (fun I => Rf I = R) =
        (Finset.univ : Finset (P R hR)).biUnion (fun p => (A R hR p).cells) := by
      ext I
      constructor
      · intro hI
        obtain ⟨p, hp⟩ := hcover I hI
        exact Finset.mem_biUnion.mpr ⟨p, Finset.mem_univ _, hp⟩
      · intro hI
        obtain ⟨p, -, hp⟩ := Finset.mem_biUnion.mp hI
        exact (hAp p).1 hp
    have hpd : ((Finset.univ : Finset (P R hR)) : Set (P R hR)).PairwiseDisjoint
        (fun p => (A R hR p).cells) := by
      intro p _ p' _ hpp
      exact Finset.disjoint_left.mpr fun I h1 h2 => hpp (hdisj p p' I h1 h2)
    rw [hunion, Finset.sum_biUnion hpd, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun p _ => ?_
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hrep, -⟩ := hAp p
    have hRT := hRsT R hR
    obtain ⟨hci, hck, hcga, hcgb, hWa, hWb⟩ := hcards R hRT
    have hrep' := hrep.trans (mul_le_mul_of_nonneg_right
      (baseErr_mono κ hci hck hWa hWb (fitOpponentConst_nonneg _) (fitOpponentConst_nonneg _)
        (fitOpponentConst_mono (hMt la hla2.le)) (fitOpponentConst_mono (hMt lb hlb2.le)) hD0)
      (dyadicGridLength_pos G _).le)
    have hcellI : ∀ I ∈ (A R hR p).cells, F I ≤
        dyadicGridLength G I.1 * ‖(A R hR p).Hf I ((A R hR p).Y I)‖ +
        dyadicGridLength G I.1 * ‖localProgressionForm (dyadicGridLength G I.1) (w I)
          (slots4 sa i k (f sa - (Xga R hRT).val I) ((Xi R hRT).val I) ((Xk R hRT).val I)
            (f sb - (Xgb R hRT).val I)) - (A R hR p).Hf I ((A R hR p).Y I)‖ := by
      intro I hI
      obtain ⟨hIt, -, hRI, hIH⟩ := hcellsT R hR p I hI
      have hr := (dyadicGridLength_pos G I.1).le
      have e : localProgressionForm (dyadicGridLength G I.1) (w I) (stagTuple f g u t I) =
          localProgressionForm (dyadicGridLength G I.1) (w I)
            (slots4 sa i k (f sa - (Xga R hRT).val I) ((Xi R hRT).val I) ((Xk R hRT).val I)
              (f sb - (Xgb R hRT).val I)) := by
        subst hRI
        rw [← hslots I hIt hIH]
      rw [← mul_add]
      refine mul_le_mul_of_nonneg_left ?_ hr
      rw [e]
      exact norm_le_norm_add_norm_sub' _ _
    calc ∑ I ∈ (A R hR p).cells, F I
        ≤ ∑ I ∈ (A R hR p).cells, (dyadicGridLength G I.1 *
            ‖(A R hR p).Hf I ((A R hR p).Y I)‖ +
          dyadicGridLength G I.1 * ‖localProgressionForm (dyadicGridLength G I.1) (w I)
            (slots4 sa i k (f sa - (Xga R hRT).val I) ((Xi R hRT).val I) ((Xk R hRT).val I)
              (f sb - (Xgb R hRT).val I)) - (A R hR p).Hf I ((A R hR p).Y I)‖) :=
          Finset.sum_le_sum hcellI
      _ = _ + _ := Finset.sum_add_distrib
      _ ≤ _ := add_le_add le_rfl hrep'
  -- the cells of the last `K₀` levels
  have hbotsum : ∑ I ∈ Bot, F I = ∑ R' : Bs, ∑ I ∈ (AB R'.1 R'.2).cells,
      dyadicGridLength G I.1 * ‖(AB R'.1 R'.2).Hf I ((AB R'.1 R'.2).Y I)‖ := by
    have hmaps : ∀ I ∈ Bot, Rb I ∈ Bs := fun I hI => Finset.mem_image_of_mem Rb hI
    rw [← Finset.sum_fiberwise_of_maps_to hmaps, ← Finset.sum_coe_sort Bs]
    refine Finset.sum_congr rfl fun R' _ => ?_
    obtain ⟨R', hR'⟩ := R'
    obtain ⟨hG', -, hcells', hw', -, -, -, -, -, -, -, hY', -⟩ := hAB R' hR'
    rw [hcells']
    refine Finset.sum_congr rfl fun I hI => ?_
    rw [hY' I hI, hslotsB R' hR' I hI]
    simp only [ActiveSetup.Hf]
    rw [hG', hw']
  have hrest : ∑ I ∈ (dyadicFiniteTree G J N).filter
      (fun I => ¬ (I.1 + K₀ ≤ J.1 + N ∧ kernelHull G J N w I)), F I = ∑ I ∈ Bot, F I := by
    rw [← Finset.sum_filter_add_sum_filter_not ((dyadicFiniteTree G J N).filter
      (fun I => ¬ (I.1 + K₀ ≤ J.1 + N ∧ kernelHull G J N w I))) (fun I => kernelHull G J N w I)]
    have hz : ∑ I ∈ ((dyadicFiniteTree G J N).filter
        (fun I => ¬ (I.1 + K₀ ≤ J.1 + N ∧ kernelHull G J N w I))).filter
          (fun I => ¬ kernelHull G J N w I), F I = 0 := by
      refine Finset.sum_eq_zero fun I hI => ?_
      obtain ⟨hI1, hIH⟩ := Finset.mem_filter.mp hI
      have hIt := (Finset.mem_filter.mp hI1).1
      simp only [hF_def, eq_zero_of_not_kernelHull hIt hIH, localProgressionForm_zero_kernel,
        norm_zero, mul_zero]
    rw [hz, add_zero, Finset.filter_filter, hBot_def]
    refine Finset.sum_congr (Finset.filter_congr fun I _ => ?_) fun _ _ => rfl
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨fun h => h1 ⟨h, h2⟩, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨fun h => h1 h.1, h2⟩
  calc ∑ I ∈ dyadicFiniteTree G J N, F I
      = ∑ I ∈ Tup, F I +
        ∑ I ∈ (dyadicFiniteTree G J N).filter
          (fun I => ¬ (I.1 + K₀ ≤ J.1 + N ∧ kernelHull G J N w I)), F I :=
        (Finset.sum_filter_add_sum_filter_not _ _ _).symm
    _ ≤ (∑ x : ιt, ∑ I ∈ (A' x).cells, dyadicGridLength G I.1 * ‖(A' x).Hf I ((A' x).Y I)‖ +
          E * ∑ x : ιt, dyadicGridLength G (A' x).R.1) +
        ∑ R' : Bs, ∑ I ∈ (AB R'.1 R'.2).cells,
          dyadicGridLength G I.1 * ‖(AB R'.1 R'.2).Hf I ((AB R'.1 R'.2).Y I)‖ := by
        rw [hrest, hbotsum]
        exact add_le_add htop le_rfl
    _ ≤ _ := by
        rw [Fintype.sum_sum_type]
        dsimp only [Atot, Sum.elim_inl, Sum.elim_inr]
        have h1 := mul_le_mul_of_nonneg_left hpack hE0
        have h2 : E * (64 / 3 * dyadicGridLength G J.1) ≤ E * (91 / 3 * dyadicGridLength G J.1) :=
          mul_le_mul_of_nonneg_left (by have := dyadicGridLength_pos G J.1; linarith) hE0
        linarith

private theorem baseTuple_stage_5 : BaseTupleStage5Statement := by
  classical
  intro κ c₂ cp Wp hdefc c₁ C₁ c₂a Ca q hq Cqa G J N w hw f hfm hfq Bf kk M roots seg n a g cnt
    atm hfit u t hut Hc Mt hMt η₀ hη₀ hpair hsz Bp ε K₀ ka kb Ma Mb hε0 hε1 H D Wa Wb E S₀ Sp i k
    hpos sa sb hab hai hak hbi hbk la hla2 lb hlb2 Lset hLne hsegd Rf Tup Rs hRtree hRsT hHl hH1
    hWpH X Y hu4 ht4 Xi Xk Xga Xgb htL ht4L hslots z BdR hzt hzt4 z0 hz0ae hz0R za zb hzaB hzbB P
    A hPA hRsumT ιt A' hcellsT hcards hpack d₀ Bot hBot_def hBot anc hanc Rb hRb hRbu Bs hBsT hQ
    hR'Q hTc hTB hslotsB hvY' hzga' hzgb' hriB
  have hrkB : ∀ R' (hR' : R' ∈ Bs), ∃ z₁ z₂,
      IsBasicOn G (Rf R') (dyadicRemainingDepth J N (Rf R')) 1 (BdR (Rf R') (hQ R' hR'))
        (max c₂ cp) H w z₁ ∧
      IsBasicOn G (Rf R') (dyadicRemainingDepth J N (Rf R')) 1 (BdR (Rf R') (hQ R' hR'))
        (max c₂ cp) H w z₂ ∧
      ∀ I ∈ Bot.filter (fun I => Rb I = R'), ∀ᵐ y ∂volume, y ∈ dyadicGridCell G I.1 I.2 →
        ((Xk (Rf R') (hQ R' hR')).reroot (hQ R' hR')).val I y = z₁ I y - z₂ I y := by
    intro R' hR'
    have hQT := hQ R' hR'
    by_cases ht4' : t ≤ 4
    · refine ⟨z t (Rf R') hQT, z0 (Rf R') hQT, hzt _ _, hz0R _ _, fun I hI => ?_⟩
      obtain ⟨hIt, hIH, hRfI, -, -⟩ := hTc R' hR' I hI
      filter_upwards [hvY' t le_rfl htL (Rf R') hQT I hIt hIH hRfI, hz0ae (Rf R') hQT I] with
        y hy h0 hyI
      rw [LowList.reroot_val, h0, sub_zero, ← hy hyI]
      simp only [Xk, ht4', ↓reduceIte]
    · refine ⟨z t (Rf R') hQT, z (t - 4) (Rf R') hQT, hzt _ _, hzt4 _ _ ht4', fun I hI => ?_⟩
      obtain ⟨hIt, hIH, hRfI, -, -⟩ := hTc R' hR' I hI
      filter_upwards [hvY' t le_rfl htL (Rf R') hQT I hIt hIH hRfI,
        hvY' (t - 4) ht4 ht4L (Rf R') hQT I hIt hIH hRfI] with y h1 h2 hyI
      rw [LowList.reroot_val, ← h1 hyI, ← h2 hyI]
      simp only [Xk, ht4', ↓reduceIte, LowList.sub_val]
  have hcc : max c₂ cp ≤ max (max c₁ (max c₂ cp)) c₂a :=
    le_trans (le_max_right c₁ _) (le_max_left _ _)
  have hHH' : H ≤ max D (max (fitBudget Cqa Ca ka) (fitBudget Cqa Ca kb)) :=
    le_trans (le_max_left _ _) (le_max_left _ _)
  have hdef₀' : ∃ (d : ℕ) (Φ : QuadraticChartData d), QuadraticChartComplexity (max c₂ cp) H Φ ∧
      IsBoundedQuadraticChart Φ := by
    obtain ⟨d, Φ, -, h1, h2⟩ := hdefc _ H (le_max_right _ _) hWpH
    exact ⟨d, Φ, h1, h2⟩
  have hbotS : ∀ (R' : ℤ × ℤ) (hR' : R' ∈ Bs), _ := fun R' hR' =>
    baseBottom κ ((Xi (Rf R') (hQ R' hR')).reroot (hQ R' hR'))
      ((Xk (Rf R') (hQ R' hR')).reroot (hQ R' hR'))
      ((Xga (Rf R') (hQ R' hR')).reroot (hQ R' hR'))
      ((Xgb (Rf R') (hQ R' hR')).reroot (hQ R' hR'))
      hai hak hab hpos hbi.symm hbk.symm K₀ f hfm w hw (hR'Q R' hR')
      (Bot.filter (fun I => Rb I = R')) (hTB R' hR')
      (fun l I hI => eLpNorm_two_le_of_q (dyadicGridLength_pos G I.1) hq.le
        (hfq l I (hTc R' hR' I hI).1 (Or.inr (hTc R' hR' I hI).2.1)))
      (fun I hI l => by
        rw [hslotsB R' hR' I hI]
        exact hsz I (hTc R' hR' I hI).1 (hTc R' hR' I hI).2.1 l)
      hη₀
      (fun I hI s s' hss => by
        rw [hslotsB R' hR' I hI]
        exact hpair I (hTc R' hR' I hI).1 (hTc R' hR' I hI).2.1 s s' hss)
      (c' := max (max c₁ (max c₂ cp)) c₂a)
      (H' := max D (max (fitBudget Cqa Ca ka) (fitBudget Cqa Ca kb)))
      hcc hHH' hdef₀' hε0 hε1 (hriB R' hR') (hrkB R' hR')
      (za (Rf R') (hQ R' hR')) (zb (Rf R') (hQ R' hR'))
      (hzaB (Rf R') (hQ R' hR')) (hzbB (Rf R') (hQ R' hR')) le_rfl hcc hHH'
      (fun I hI => hzga' (Rf R') (hQ R' hR') I (hTc R' hR' I hI).1 (hTc R' hR' I hI).2.1
        (hTc R' hR' I hI).2.2.1)
      (fun I hI => hzgb' (Rf R') (hQ R' hR') I (hTc R' hR' I hI).1 (hTc R' hR' I hI).2.1
        (hTc R' hR' I hI).2.2.1)
  choose AB hAB using hbotS
  have hBc : ∀ R' (hR' : R' ∈ Bs), ∀ I ∈ (AB R' hR').cells,
      I ∈ Bot.filter (fun I => Rb I = R') := fun R' hR' I hI => by
    rw [← (hAB R' hR').2.2.1]; exact hI
  -- the fresh roots have total length at most `9 |J|`
  have hbpack : ∑ R' : Bs, dyadicGridLength G (AB R'.1 R'.2).R.1 ≤
      9 * dyadicGridLength G J.1 := by
    expose_names
    exact @baseTuple_hbpack κ c₂ cp Wp c₁ C₁ c₂a Ca Cqa G J N w f Bf seg u t hut Hc η₀ Bp ε K₀ ka
      kb sa sb hla2 hlb2 hLne hHl X hu4 ht4 hRsumT hBot hanc hRb hQ AB hAB
  let ι := ιt ⊕ Bs
  let Atot : ι → ActiveSetup κ (max (max c₁ (max c₂ cp)) c₂a) :=
    Sum.elim A' fun R' => AB R'.1 R'.2
  refine ⟨ι, inferInstance, Atot, ?_, ?_, ?_, ?_⟩
  · rw [Fintype.sum_sum_type]
    dsimp only [Atot, Sum.elim_inl, Sum.elim_inr]
    linarith
  · -- disjointness
    rintro (⟨⟨R, hR⟩, p⟩ | ⟨R₁, hR₁⟩) (⟨⟨R', hR'⟩, p'⟩ | ⟨R₂, hR₂⟩) I hx hx'
    · have e1 := (hcellsT R hR p I hx).2.2.1
      have e2 := (hcellsT R' hR' p' I hx').2.2.1
      obtain rfl : R = R' := e1.symm.trans e2
      have := (hPA R hR).2.2.1 p p' I hx hx'
      subst this
      rfl
    · exact absurd (hcellsT R hR p I hx).2.1
        (Finset.mem_filter.mp (Finset.mem_filter.mp (hBc R₂ hR₂ I hx')).1).2.1
    · exact absurd (hcellsT R' hR' p' I hx').2.1
        (Finset.mem_filter.mp (Finset.mem_filter.mp (hBc R₁ hR₁ I hx)).1).2.1
    · have h1 := (Finset.mem_filter.mp (hBc R₁ hR₁ I hx)).2
      have h2 := (Finset.mem_filter.mp (hBc R₂ hR₂ I hx')).2
      obtain rfl : R₁ = R₂ := h1.symm.trans h2
      rfl
  · expose_names
    exact @baseTuple_conclusion_39 κ c₂ cp Wp c₁ C₁ c₂a Ca Cqa G J N w f Bf M seg u t hut Hc Mt η₀
      Bp ε K₀ ka kb Ma Mb hε0 sa sb hla2 hlb2 hLne hsegd hRtree hRsT hHl X hu4 ht4 P A hPA hcellsT
      hcards hBot hanc hRbu hBsT hQ hTc AB hAB
  · expose_names
    exact @baseTuple_conclusion_40 κ c₂ cp Wp c₁ C₁ c₂a Ca q Cqa G J N w f Bf kk M roots seg n a g
      cnt atm hfit u t hut Hc Mt hMt η₀ Bp ε K₀ ka kb Ma Mb sa sb hla2 hlb2 hLne hRtree hRsT hHl
      hH1 X hu4 ht4 hslots P A hPA hcellsT hcards hpack hBot_def hQ hslotsB AB hAB

private theorem baseTuple_stage_4 : BaseTupleStage4Statement := by
  classical
  intro κ c₂ cp Wp hdefc c₁ C₁ c₂a Ca q hq Cqa G J N w hw f hfm hfq Bf kk M roots seg n a g cnt
    atm hfit u t hut Hc Mt hMt η₀ hη₀ hpair hsz Bp ε K₀ ka kb Ma Mb hε0 hε1 H D Wa Wb E S₀ Sp i k
    hpos sa sb hab hai hak hbi hbk la hla2 lb hlb2 Lset hLne hsegd Rf Tup Rs hRtree hRsT hHl hH1
    hWpH X Y hYval hu4 ht4 Xi Xk Xga Xgb huL hu4L htL ht4L hlaL hlbL hcellR hslots hgav hgbv z hz2
    BdR hzu hzu4 hzt hzt4 z0 hz0ae hz0R za zb hzaB hzbB P A hPA hRsumT ιt A' hcellsT hcards hpack
    d₀ Bot hBot_def hBot anc hanc Rb hRb
  have hRbRf : ∀ I ∈ dyadicFiniteTree G J N, d₀ ≤ I.1 → Rf (Rb I) = Rf I := fun I hI hdI => by
    obtain ⟨hRbT, -, hIRb, hRbRf⟩ := hRb I hI hdI
    exact firstRoot_between (hL := hLne) hsegd hI hRbT hIRb hRbRf
  have hRbu : ∀ I ∈ dyadicFiniteTree G J N, d₀ ≤ I.1 → ∀ I' ∈ dyadicFiniteTree G J N,
      dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G I'.1 I'.2 →
      dyadicGridCell G I'.1 I'.2 ⊆ dyadicGridCell G (Rb I).1 (Rb I).2 → Rb I' = Rb I := by
    intro I hI hdI I' hI' hII' hI'Rb
    obtain ⟨-, hdRb, -, hRbRf'⟩ := hRb I hI hdI
    have hdI' : d₀ ≤ I'.1 := hdRb.trans (dyadicGridCell_depth_le_of_subset G I' (Rb I) hI'Rb)
    have he : Rf I' = Rf I :=
      firstRoot_between (hL := hLne) hsegd hI hI' hII' (hI'Rb.trans hRbRf')
    by_cases hd : d₀ ≤ (Rf I).1
    · have e1 : Rb I = Rf I := by simp only [Rb, hd, ↓reduceIte]
      have e2 : Rb I' = Rf I' := by simp only [Rb, he, hd, ↓reduceIte]
      rw [e1, e2, he]
    · have e1 : Rb I = anc I := by simp only [Rb, hd, ↓reduceIte]
      have e2 : Rb I' = anc I' := by simp only [Rb, he, hd, ↓reduceIte]
      rw [e1] at hI'Rb ⊢
      rw [e2]
      obtain ⟨ha1, ha2⟩ := hanc I' hdI'
      obtain ⟨hb1, -⟩ := hanc I hdI
      have hx := dyadicGridCell_left_mem G I'.1 I'.2
      exact (dyadicGridCell_eq_of_common_point G (hI'Rb hx) (ha2 hx) (by omega)).symm
  set! Bs := Bot.image Rb with hBs_def
  have hBsT : ∀ R' ∈ Bs, R' ∈ dyadicFiniteTree G J N ∧ d₀ ≤ R'.1 := fun R' hR' => by
    obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hR'
    obtain ⟨hIt, hdI, -⟩ := hBot I hI
    exact ⟨(hRb I hIt hdI).1, (hRb I hIt hdI).2.1⟩
  have hQ : ∀ R' ∈ Bs, Rf R' ∈ dyadicFiniteTree G J N := fun R' hR' =>
    (hRtree R' (hBsT R' hR').1).1
  have hR'Q : ∀ R' ∈ Bs, R' ∈ dyadicFiniteTree G (Rf R') (dyadicRemainingDepth J N (Rf R')) :=
    fun R' hR' => (dyadicFiniteTree_below_iff G J N (hQ R' hR') R').mpr
      ⟨(hBsT R' hR').1, (hRtree R' (hBsT R' hR').1).2⟩
  have hTc : ∀ R' ∈ Bs, ∀ I ∈ Bot.filter (fun I => Rb I = R'), I ∈ dyadicFiniteTree G J N ∧
      kernelHull G J N w I ∧ Rf I = Rf R' ∧
      dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G R'.1 R'.2 ∧ I.1 < R'.1 + K₀ := by
    intro R' _ I hI
    obtain ⟨hIB, hIR⟩ := Finset.mem_filter.mp hI
    obtain ⟨hIt, hdI, hIH⟩ := hBot I hIB
    obtain ⟨-, hdRb, hIRb, -⟩ := hRb I hIt hdI
    rw [hIR] at hdRb hIRb
    refine ⟨hIt, hIH, ?_, hIRb, ?_⟩
    · rw [← hIR]; exact (hRbRf I hIt hdI).symm
    · have := ((dyadicFiniteTree_mem_iff G J I N).mp hIt).2; omega
  have hTB : ∀ R' (hR' : R' ∈ Bs), ∀ I ∈ Bot.filter (fun I => Rb I = R'),
      I ∈ dyadicFiniteTree G (Rf R') (dyadicRemainingDepth J N (Rf R')) ∧
      kernelHull G (Rf R') (dyadicRemainingDepth J N (Rf R')) w I ∧
      dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G R'.1 R'.2 ∧ I.1 < R'.1 + K₀ := by
    intro R' hR' I hI
    obtain ⟨hIt, hIH, -, hIR', hd⟩ := hTc R' hR' I hI
    have hIQ : dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G (Rf R').1 (Rf R').2 :=
      hIR'.trans (hRtree R' (hBsT R' hR').1).2
    exact ⟨(dyadicFiniteTree_below_iff G J N (hQ R' hR') I).mpr ⟨hIt, hIQ⟩,
      (kernelHull_below_iff (hQ R' hR') hIQ).mpr hIH, hIR', hd⟩
  -- the tuple on the bottom cells, read from the low lists of their first-level roots
  have hslots' : ∀ (I : ℤ × ℤ) (hI : I ∈ dyadicFiniteTree G J N), kernelHull G J N w I →
      ∀ (R : ℤ × ℤ) (hR : R ∈ dyadicFiniteTree G J N), Rf I = R →
      slots4 sa i k (f sa - (Xga R hR).val I) ((Xi R hR).val I) ((Xk R hR).val I)
        (f sb - (Xgb R hR).val I) = stagTuple f g u t I := by
    intro I hI hIH R hR hRI
    subst hRI
    exact hslots I hI hIH
  have hslotsB : ∀ R' (hR' : R' ∈ Bs), ∀ I ∈ Bot.filter (fun I => Rb I = R'),
      slots4 sa i k (f sa - ((Xga (Rf R') (hQ R' hR')).reroot (hQ R' hR')).val I)
        (((Xi (Rf R') (hQ R' hR')).reroot (hQ R' hR')).val I)
        (((Xk (Rf R') (hQ R' hR')).reroot (hQ R' hR')).val I)
        (f sb - ((Xgb (Rf R') (hQ R' hR')).reroot (hQ R' hR')).val I) = stagTuple f g u t I := by
    intro R' hR' I hI
    obtain ⟨hIt, hIH, hRfI, -, -⟩ := hTc R' hR' I hI
    exact hslots' I hIt hIH (Rf R') (hQ R' hR') hRfI
  have hvY' : ∀ ℓ (hℓ : ℓ ≤ t), ℓ ∈ Lset → ∀ (R : ℤ × ℤ) (hR : R ∈ dyadicFiniteTree G J N),
      ∀ I ∈ dyadicFiniteTree G J N, kernelHull G J N w I → Rf I = R →
      ∀ᵐ y ∂volume, y ∈ dyadicGridCell G I.1 I.2 → (Y ℓ hℓ R hR).val I y = z ℓ R hR I y := by
    intro ℓ hℓ hℓL R hR I hIt hIH hRI
    subst hRI
    filter_upwards [hz2 ℓ (Rf I) hR I hIt (hcellR I hIt ℓ hℓL)] with y hy hyI
    rw [hy hyI]
    exact hYval ℓ hℓ _ _ I hIt (hRtree I hIt).2 (hcellR I hIt ℓ hℓL) hIH y
  have hzga' : ∀ (R : ℤ × ℤ) (hR : R ∈ dyadicFiniteTree G J N), ∀ I ∈ dyadicFiniteTree G J N,
      kernelHull G J N w I → Rf I = R →
      ∀ᵐ y ∂volume, y ∈ dyadicGridCell G I.1 I.2 → za R hR I y = (Xga R hR).val I y := by
    intro R hR I hIt hIH hRI
    subst hRI
    rw [hgav I hIt hIH]
    by_cases h1 : 1 ≤ la
    · simp only [za, h1, ↓reduceIte]
      filter_upwards [hz2 la (Rf I) hR I hIt (hcellR I hIt la hlaL)] with y hy hyI
      rw [hy hyI]
    · simp only [za, h1, ↓reduceIte]
      filter_upwards [hz0ae (Rf I) hR I] with y hy _
      rw [hy, Pi.zero_apply]
  have hzgb' : ∀ (R : ℤ × ℤ) (hR : R ∈ dyadicFiniteTree G J N), ∀ I ∈ dyadicFiniteTree G J N,
      kernelHull G J N w I → Rf I = R →
      ∀ᵐ y ∂volume, y ∈ dyadicGridCell G I.1 I.2 → zb R hR I y = (Xgb R hR).val I y := by
    intro R hR I hIt hIH hRI
    subst hRI
    rw [hgbv I hIt hIH]
    by_cases h1 : 1 ≤ lb
    · simp only [zb, h1, ↓reduceIte]
      filter_upwards [hz2 lb (Rf I) hR I hIt (hcellR I hIt lb hlbL)] with y hy hyI
      rw [hy hyI]
    · simp only [zb, h1, ↓reduceIte]
      filter_upwards [hz0ae (Rf I) hR I] with y hy _
      rw [hy, Pi.zero_apply]
  have hriB : ∀ R' (hR' : R' ∈ Bs), ∃ z₁ z₂,
      IsBasicOn G (Rf R') (dyadicRemainingDepth J N (Rf R')) 1 (BdR (Rf R') (hQ R' hR'))
        (max c₂ cp) H w z₁ ∧
      IsBasicOn G (Rf R') (dyadicRemainingDepth J N (Rf R')) 1 (BdR (Rf R') (hQ R' hR'))
        (max c₂ cp) H w z₂ ∧
      ∀ I ∈ Bot.filter (fun I => Rb I = R'), ∀ᵐ y ∂volume, y ∈ dyadicGridCell G I.1 I.2 →
        ((Xi (Rf R') (hQ R' hR')).reroot (hQ R' hR')).val I y = z₁ I y - z₂ I y := by
    intro R' hR'
    have hQT := hQ R' hR'
    by_cases hu4' : u ≤ 4
    · obtain ⟨z₀, hz₀, hz₀0⟩ := (hzu (Rf R') hQT).zero zero_le_one
      refine ⟨z u (Rf R') hQT, z₀, hzu _ _, hz₀, fun I hI => ?_⟩
      obtain ⟨hIt, hIH, hRfI, -, -⟩ := hTc R' hR' I hI
      filter_upwards [hvY' u hut.le huL (Rf R') hQT I hIt hIH hRfI, hz₀0 I] with y hy h0 hyI
      rw [LowList.reroot_val, h0, sub_zero, ← hy hyI]
      simp only [Xi, hu4', ↓reduceIte]
    · refine ⟨z u (Rf R') hQT, z (u - 4) (Rf R') hQT, hzu _ _, hzu4 _ _ hu4', fun I hI => ?_⟩
      obtain ⟨hIt, hIH, hRfI, -, -⟩ := hTc R' hR' I hI
      filter_upwards [hvY' u hut.le huL (Rf R') hQT I hIt hIH hRfI,
        hvY' (u - 4) hu4 hu4L (Rf R') hQT I hIt hIH hRfI] with y h1 h2 hyI
      rw [LowList.reroot_val, ← h1 hyI, ← h2 hyI]
      simp only [Xi, hu4', ↓reduceIte, LowList.sub_val]
  expose_names
  exact @baseTuple_stage_5 κ c₂ cp Wp hdefc c₁ C₁ c₂a Ca q hq Cqa G J N w hw f hfm hfq Bf kk M
    roots seg n a g cnt atm hfit u t hut Hc Mt hMt η₀ hη₀ hpair hsz Bp ε K₀ ka kb Ma Mb hε0 hε1
    hpos sa sb hab hai hak hbi hbk hla2 hlb2 hLne hsegd hRtree hRsT hHl hH1 hWpH X hu4 ht4 htL
    ht4L hslots z hzt hzt4 z0 hz0ae hz0R hzaB hzbB P A hPA hRsumT hcellsT hcards hpack hBot_def
    hBot hanc hRb hRbu hBsT hQ hR'Q hTc hTB hslotsB hvY' hzga' hzgb' hriB

private theorem baseTuple_stage_3 : BaseTupleStage3Statement := by
  classical
  intro κ c₂ cp Wp hdefc c₁ C₁ c₂a Ca q hq Cqa G J N w hw f hfm hfq Bf kk M roots seg n a g cnt
    atm hfit u t hut Hc Mt hMt η₀ hη₀ hpair hsz Bp ε K₀ ka kb Ma Mb hε0 hε1 H D Wa Wb E S₀ Sp i k
    hpos sa sb hab hai hak hbi hbk la hla2 lb hlb2 Lset hL_def hLne hsegd Rf Tup Rs hRtree hRsT
    hHl hH1 hWpH X Y hYval hYcard hu4 ht4 Xi Xk Xga Xgb huL hu4L htL ht4L hlaL hlbL hcellR hslots
    hgav hgbv z hz2 BdR hzu hzu4 hzt hzt4 z0 hz0ae hz0R za zb hzaB hzbB hbase
  dsimp only at hbase
  choose P A hPA using hbase
  -- the length of the first-level roots
  have hLcard : Lset.card ≤ 6 := by
    have c1 := Finset.card_insert_le u ({u - 4, t, t - 4, la, lb} : Finset ℕ)
    have c2 := Finset.card_insert_le (u - 4) ({t, t - 4, la, lb} : Finset ℕ)
    have c3 := Finset.card_insert_le t ({t - 4, la, lb} : Finset ℕ)
    have c4 := Finset.card_insert_le (t - 4) ({la, lb} : Finset ℕ)
    have c5 := Finset.card_insert_le la ({lb} : Finset ℕ)
    rw [Finset.card_singleton] at c5
    simp only [hL_def]
    omega
  have hRsumT : ∀ T : Finset (ℤ × ℤ), (∀ I ∈ T, I ∈ dyadicFiniteTree G J N) →
      ∑ R ∈ T.image Rf, dyadicGridLength G R.1 ≤ 8 * dyadicGridLength G J.1 := by
    intro T hT
    have h1 := sum_firstRoot_le (hL := hLne) roots
      (fun ℓ _ I hI => ((hfit ℓ).1.2.2.2.2 I hI).1) T hT
    have h2 := finite_union_weight_le Lset roots (fun c => dyadicGridLength G c.1)
      (fun c => (dyadicGridLength_pos G c.1).le)
    have h3 : ∑ ℓ ∈ Lset, ∑ c ∈ roots ℓ, dyadicGridLength G c.1 ≤
        ∑ _ℓ ∈ Lset, 4 / 3 * dyadicGridLength G J.1 :=
      Finset.sum_le_sum fun ℓ _ => (hfit ℓ).1.2.2.2.1
    rw [Finset.sum_const, nsmul_eq_mul] at h3
    have h4 : (Lset.card : ℝ) * (4 / 3 * dyadicGridLength G J.1) ≤
        6 * (4 / 3 * dyadicGridLength G J.1) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hLcard)
        (by have := dyadicGridLength_pos G J.1; positivity)
    unfold dyadicRootLength at h1
    linarith
  have hRsum : ∑ R ∈ Rs, dyadicGridLength G R.1 ≤ 8 * dyadicGridLength G J.1 :=
    hRsumT Tup fun I hI => (Finset.mem_filter.mp hI).1
  -- the index of the active setups above the last `K₀` levels
  let ιt := Σ R : Rs, (P R.1 R.2)
  let A' : ιt → ActiveSetup κ (max (max c₁ (max c₂ cp)) c₂a) := fun x => A x.1.1 x.1.2 x.2
  have hcellsT : ∀ (R : ℤ × ℤ) (hR : R ∈ Rs) (p : P R hR) (I : ℤ × ℤ), I ∈ (A R hR p).cells →
      I ∈ dyadicFiniteTree G J N ∧ I.1 + K₀ ≤ J.1 + N ∧ Rf I = R ∧ kernelHull G J N w I :=
    fun R hR p I hI => by
    have h := ((hPA R hR).2.2.2 p).1 hI
    obtain ⟨hIT, hRI⟩ := Finset.mem_filter.mp h
    exact ⟨(Finset.mem_filter.mp hIT).1, (Finset.mem_filter.mp hIT).2.1, hRI,
      (Finset.mem_filter.mp hIT).2.2⟩
  have hcards : ∀ (R : ℤ × ℤ) (hRT : R ∈ dyadicFiniteTree G J N),
      Fintype.card (Xi R hRT).Λ ≤ 2 * Mt ∧ Fintype.card (Xk R hRT).Λ ≤ 2 * Mt ∧
      Fintype.card (Xga R hRT).Λ ≤ Mt ∧ Fintype.card (Xgb R hRT).Λ ≤ Mt ∧
      Fintype.card (Xi R hRT).Λ * Fintype.card (Xk R hRT).Λ * ⌊D⌋₊ + Ma ≤ Wa ∧
      Fintype.card (Xi R hRT).Λ * Fintype.card (Xk R hRT).Λ * ⌊D⌋₊ + Mb ≤ Wb := by
    expose_names
    exact @baseTuple_hcards c₂ cp Wp C₁ G J N Bf M u t hut Hc Mt hMt Bp Ma Mb sa sb hla2 hlb2 hHl
      X hYcard hu4 ht4
  have hpack : ∑ x : ιt, dyadicGridLength G (A' x).R.1 ≤ 64 / 3 * dyadicGridLength G J.1 := by
    calc ∑ x : ιt, dyadicGridLength G (A' x).R.1
        = ∑ R : Rs, ∑ p : P R.1 R.2, dyadicGridLength G (A R.1 R.2 p).R.1 :=
          Fintype.sum_sigma _
      _ ≤ ∑ R : Rs, 8 / 3 * dyadicGridLength G R.1.1 :=
          Finset.sum_le_sum fun R _ => (hPA R.1 R.2).1
      _ = 8 / 3 * ∑ R ∈ Rs, dyadicGridLength G R.1 := by
          rw [← Finset.mul_sum, Finset.sum_coe_sort Rs (fun R => dyadicGridLength G R.1)]
      _ ≤ 8 / 3 * (8 * dyadicGridLength G J.1) := by linarith
      _ = 64 / 3 * dyadicGridLength G J.1 := by ring
  -- the last `K₀` levels: fresh roots at depth `max d₀ (first-level root)`
  set! d₀ : ℤ := J.1 + N + 1 - K₀ with hd₀
  set! Bot := (dyadicFiniteTree G J N).filter
    (fun I => ¬ (I.1 + K₀ ≤ J.1 + N) ∧ kernelHull G J N w I) with hBot_def
  have hBot : ∀ I ∈ Bot, I ∈ dyadicFiniteTree G J N ∧ d₀ ≤ I.1 ∧ kernelHull G J N w I :=
    fun I hI => by
      obtain ⟨hIt, hIK, hIH⟩ := Finset.mem_filter.mp hI
      exact ⟨hIt, by omega, hIH⟩
  let anc : ℤ × ℤ → ℤ × ℤ := fun I =>
    if h : d₀ ≤ I.1 then (d₀, Classical.choose (dyadicGridCell_ancestor G h I.2)) else I
  have hanc : ∀ I : ℤ × ℤ, d₀ ≤ I.1 → (anc I).1 = d₀ ∧
      dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G (anc I).1 (anc I).2 := fun I h => by
    refine ⟨by simp only [anc, h, ↓reduceDIte], ?_⟩
    simp only [anc, h, ↓reduceDIte]
    exact Classical.choose_spec (dyadicGridCell_ancestor G h I.2)
  let Rb : ℤ × ℤ → ℤ × ℤ := fun I => if d₀ ≤ (Rf I).1 then Rf I else anc I
  have hRb : ∀ I ∈ dyadicFiniteTree G J N, d₀ ≤ I.1 →
      Rb I ∈ dyadicFiniteTree G J N ∧ d₀ ≤ (Rb I).1 ∧
      dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G (Rb I).1 (Rb I).2 ∧
      dyadicGridCell G (Rb I).1 (Rb I).2 ⊆ dyadicGridCell G (Rf I).1 (Rf I).2 := by
    intro I hI hdI
    obtain ⟨hRfT, hIRf⟩ := hRtree I hI
    have hx := dyadicGridCell_left_mem G I.1 I.2
    by_cases hd : d₀ ≤ (Rf I).1
    · have e : Rb I = Rf I := by simp only [Rb, hd, ↓reduceIte]
      rw [e]
      exact ⟨hRfT, hd, hIRf, subset_rfl⟩
    · have e : Rb I = anc I := by simp only [Rb, hd, ↓reduceIte]
      rw [e]
      obtain ⟨ha1, ha2⟩ := hanc I hdI
      have hsub : dyadicGridCell G (anc I).1 (anc I).2 ⊆ dyadicGridCell G (Rf I).1 (Rf I).2 :=
        dyadicGridCell_subset_of_common_point G (ha2 hx) (hIRf hx) (by omega)
      exact ⟨dyadicFiniteTree_ancestor_mem G J I (anc I) N hI ha2
        (hsub.trans ((dyadicFiniteTree_mem_iff G J (Rf I) N).mp hRfT).1), by omega, ha2, hsub⟩
  expose_names
  exact @baseTuple_stage_4 κ c₂ cp Wp hdefc c₁ C₁ c₂a Ca q hq Cqa G J N w hw f hfm hfq Bf kk M
    roots seg n a g cnt atm hfit u t hut Hc Mt hMt η₀ hη₀ hpair hsz Bp ε K₀ ka kb Ma Mb hε0 hε1
    hpos sa sb hab hai hak hbi hbk hla2 hlb2 hLne hsegd hRtree hRsT hHl hH1 hWpH X hYval hu4 ht4
    huL hu4L htL ht4L hlaL hlbL hcellR hslots hgav hgbv z hz2 hzu hzu4 hzt hzt4 z0 hz0ae hz0R hzaB
    hzbB P A hPA hRsumT hcellsT hcards hpack hBot_def hBot hanc hRb

private theorem baseTuple_stage_2 : BaseTupleStage2Statement := by
  classical
  intro κ c₂ cp Wp hdefc c₁ C₁ c₂a Ca q hq Cqa hfr' G J N w hw f hfm hfq Bf kk M roots seg n a g
    cnt atm hfit u t hut Hc Mt hMt η₀ hη₀ hpair hsz Bp ε K₀ ka kb Ma Mb hBp hε0 hε1 hka hkb hMa
    hMb H D Wa Wb E S₀ Sp i k hpos sa sb hab hai hak hbi hbk la hla2 hla lb hlb2 hlb Lset hL_def
    hLne hsegd Rf Tup Rs hRtree hRsT hHl hH1 hWpH X Y hYval hYcard hu4 ht4 Xi Xk Xga Xgb huL hu4L
    htL ht4L hlaL hlbL hcellR hslots hXiv hXkv hfitL2 hgav hgbv z hz1 hz2 hzR hzB hBfH BdR hzBd
    hcXi hcXk hcXga hcXgb hzu hzu4 hzt
  have hzt4 : ∀ (R : ℤ × ℤ) (hR : R ∈ dyadicFiniteTree G J N), ¬ t ≤ 4 →
      IsBasicOn G R (dyadicRemainingDepth J N R) 1 (BdR R hR) (max c₂ cp) H w (z (t - 4) R hR) :=
    fun R hR h => ((hzB (t - 4) R hR).mono_budget
      (hzBd (t - 4) R hR (by have := (hcXk R hR).2 h; omega))).mono_chart (le_max_left _ _)
        (hBfH (t - 4) ht4)
  have hvY : ∀ ℓ (hℓ : ℓ ≤ t), ℓ ∈ Lset → ∀ (R : ℤ × ℤ) (hR : R ∈ dyadicFiniteTree G J N),
      ∀ I ∈ Tup.filter (fun I => Rf I = R), ∀ᵐ y ∂volume, y ∈ dyadicGridCell G I.1 I.2 →
        (Y ℓ hℓ R hR).val I y = z ℓ R hR I y := by
    intro ℓ hℓ hℓL R hR I hI
    obtain ⟨hIT, hRI⟩ := Finset.mem_filter.mp hI
    have hIt := (Finset.mem_filter.mp hIT).1
    have hIH := (Finset.mem_filter.mp hIT).2.2
    subst hRI
    filter_upwards [hz2 ℓ (Rf I) hR I hIt (hcellR I hIt ℓ hℓL)] with y hy hyI
    rw [hy hyI]
    exact hYval ℓ hℓ _ _ I hIt (hRtree I hIt).2 (hcellR I hIt ℓ hℓL) hIH y
  -- the base data on each first-level root
  -- the opponents of the two remaining slots (zero before their first update)
  have hz0 := fun (R : ℤ × ℤ) (hR : R ∈ dyadicFiniteTree G J N) => (hzB u R hR).zero zero_le_one
  choose z0 hz0B hz0ae using hz0
  have hz0R : ∀ (R : ℤ × ℤ) (hR : R ∈ dyadicFiniteTree G J N),
      IsBasicOn G R (dyadicRemainingDepth J N R) 1 (BdR R hR) (max c₂ cp) H w (z0 R hR) :=
    fun R hR => ((hz0B R hR).mono_budget (hzBd u R hR (by have := (hcXi R hR).1; omega))).mono_chart
      (le_max_left _ _) (hBfH u hut.le)
  let za : ∀ R, R ∈ dyadicFiniteTree G J N → ℤ × ℤ → ℝ → ℂ := fun R hR =>
    if 1 ≤ la then z la R hR else z0 R hR
  let zb : ∀ R, R ∈ dyadicFiniteTree G J N → ℤ × ℤ → ℝ → ℂ := fun R hR =>
    if 1 ≤ lb then z lb R hR else z0 R hR
  have hz0O : ∀ (R : ℤ × ℤ) (hR : R ∈ dyadicFiniteTree G J N) (F : ℝ → ℂ) (K : ℝ),
      (∀ I, Measurable (z0 R hR I) ∧
        MemLp (z0 R hR I) 2 (volume.restrict (dyadicGridCell G I.1 I.2))) ∧
      ∀ J' ∈ dyadicFiniteTree G J N, dyadicGridCell G J'.1 J'.2 ⊆ dyadicGridCell G R.1 R.2 →
        IsAdmissibleOpponent G J' F (z0 R hR) K ∧ HasDepthEnergy G J' F (z0 R hR) 1 :=
    fun R hR F K => ⟨fun I => ⟨(hz0B R hR).measurable I,
      MemLp.ae_eq (show (0 : ℝ → ℂ) =ᵐ[volume.restrict (dyadicGridCell G I.1 I.2)] z0 R hR I
        from (ae_restrict_of_ae (hz0ae R hR I)).mono fun y hy => hy.symm) MemLp.zero⟩,
      fun J' _ _ => ⟨isAdmissibleOpponent_of_ae_zero (hz0ae R hR) K,
        hasDepthEnergy_of_ae_zero (hz0ae R hR)⟩⟩
  have hzaO : ∀ (R : ℤ × ℤ) (hR : R ∈ dyadicFiniteTree G J N),
      (∀ I, Measurable (za R hR I) ∧
        MemLp (za R hR I) 2 (volume.restrict (dyadicGridCell G I.1 I.2))) ∧
      ∀ J' ∈ dyadicFiniteTree G J N, dyadicGridCell G J'.1 J'.2 ⊆ dyadicGridCell G R.1 R.2 →
        IsAdmissibleOpponent G J' (f sa) (za R hR) (fitOpponentConst (M la)) ∧
          HasDepthEnergy G J' (f sa) (za R hR) 1 := fun R hR => by
    by_cases h1 : 1 ≤ la
    · simp only [za, h1, ↓reduceIte]
      exact ⟨hz1 la R _, fun J' hJ' hJ'R => (hla h1) ▸ hzR la R _ J' hJ' hJ'R⟩
    · simp only [za, h1, ↓reduceIte]
      exact hz0O R hR _ _
  have hzbO : ∀ (R : ℤ × ℤ) (hR : R ∈ dyadicFiniteTree G J N),
      (∀ I, Measurable (zb R hR I) ∧
        MemLp (zb R hR I) 2 (volume.restrict (dyadicGridCell G I.1 I.2))) ∧
      ∀ J' ∈ dyadicFiniteTree G J N, dyadicGridCell G J'.1 J'.2 ⊆ dyadicGridCell G R.1 R.2 →
        IsAdmissibleOpponent G J' (f sb) (zb R hR) (fitOpponentConst (M lb)) ∧
          HasDepthEnergy G J' (f sb) (zb R hR) 1 := fun R hR => by
    by_cases h1 : 1 ≤ lb
    · simp only [zb, h1, ↓reduceIte]
      exact ⟨hz1 lb R _, fun J' hJ' hJ'R => (hlb h1) ▸ hzR lb R _ J' hJ' hJ'R⟩
    · simp only [zb, h1, ↓reduceIte]
      exact hz0O R hR _ _
  have hzaB : ∀ (R : ℤ × ℤ) (hR : R ∈ dyadicFiniteTree G J N),
      IsBasicOn G R (dyadicRemainingDepth J N R) 1 (BdR R hR) (max c₂ cp) H w (za R hR) :=
    fun R hR => by
    by_cases h1 : 1 ≤ la
    · simp only [za, h1, ↓reduceIte]
      exact ((hzB la R hR).mono_budget (hzBd la R hR (by have := hcXga R hR h1; omega))).mono_chart
        (le_max_left _ _) (hBfH la hla2.le)
    · simp only [za, h1, ↓reduceIte]; exact hz0R R hR
  have hzbB : ∀ (R : ℤ × ℤ) (hR : R ∈ dyadicFiniteTree G J N),
      IsBasicOn G R (dyadicRemainingDepth J N R) 1 (BdR R hR) (max c₂ cp) H w (zb R hR) :=
    fun R hR => by
    by_cases h1 : 1 ≤ lb
    · simp only [zb, h1, ↓reduceIte]
      exact ((hzB lb R hR).mono_budget (hzBd lb R hR (by have := hcXgb R hR h1; omega))).mono_chart
        (le_max_left _ _) (hBfH lb hlb2.le)
    · simp only [zb, h1, ↓reduceIte]; exact hz0R R hR
  have hbase : ∀ (R : ℤ × ℤ) (hR : R ∈ Rs), _ := fun R hR =>
    hfr' (hRsT R hR) hH1 hai hak hab hpos hbi.symm hbk.symm w hw f hfm
      (fun l I hI hIH => hfq l I hI (Or.inr hIH)) (Xi R (hRsT R hR))
      (Xk R (hRsT R hR)) (Xga R (hRsT R hR)) (Xgb R (hRsT R hR))
      (hdefc _ H (le_max_right _ _) hWpH) (za R (hRsT R hR)) (zb R (hRsT R hR))
      (fitOpponentConst_nonneg (M la)) (fitOpponentConst_nonneg (M lb))
      (hzaO R (hRsT R hR)) (hzbO R (hRsT R hR)) K₀
      (Tup.filter (fun I => Rf I = R)) (fun I hI => by
        obtain ⟨hIT, hRI⟩ := Finset.mem_filter.mp hI
        obtain ⟨hIt, hIK, hIH⟩ := Finset.mem_filter.mp hIT
        subst hRI
        refine ⟨hIt, (hRtree I hIt).2, hIK, ?_, ?_⟩
        · rw [hgav I hIt hIH]
          by_cases h1 : 1 ≤ la
          · simp only [za, h1, ↓reduceIte]
            filter_upwards [hz2 la (Rf I) _ I hIt (hcellR I hIt la hlaL)] with y hy hyI
            rw [hy hyI]
          · simp only [za, h1, ↓reduceIte]
            filter_upwards [hz0ae (Rf I) (hRsT (Rf I) hR) I] with y hy _
            rw [hy, Pi.zero_apply]
        · rw [hgbv I hIt hIH]
          by_cases h1 : 1 ≤ lb
          · simp only [zb, h1, ↓reduceIte]
            filter_upwards [hz2 lb (Rf I) _ I hIt (hcellR I hIt lb hlbL)] with y hy hyI
            rw [hy hyI]
          · simp only [zb, h1, ↓reduceIte]
            filter_upwards [hz0ae (Rf I) (hRsT (Rf I) hR) I] with y hy _
            rw [hy, Pi.zero_apply])
      (fun I hI => ((Finset.mem_filter.mp (Finset.mem_filter.mp hI).1).2).2)
      (by
        by_cases hu4' : u ≤ 4
        · obtain ⟨z₀, hz₀, hz₀0⟩ := (hzu R (hRsT R hR)).zero zero_le_one
          refine ⟨z u R (hRsT R hR), z₀, hzu R _, hz₀, fun I hI => ?_⟩
          filter_upwards [hvY u hut.le huL R (hRsT R hR) I hI, hz₀0 I] with y hy h0 hyI
          rw [h0, sub_zero, ← hy hyI]
          simp only [Xi, hu4', ↓reduceIte]
        · refine ⟨z u R (hRsT R hR), z (u - 4) R (hRsT R hR), hzu R _, hzu4 R _ hu4',
            fun I hI => ?_⟩
          filter_upwards [hvY u hut.le huL R (hRsT R hR) I hI,
            hvY (u - 4) hu4 hu4L R (hRsT R hR) I hI] with y h1 h2 hyI
          rw [← h1 hyI, ← h2 hyI]
          simp only [Xi, hu4', ↓reduceIte, LowList.sub_val])
      (by
        by_cases ht4' : t ≤ 4
        · refine ⟨z t R (hRsT R hR), z0 R (hRsT R hR), hzt R _, hz0R R _, fun I hI => ?_⟩
          filter_upwards [hvY t le_rfl htL R (hRsT R hR) I hI, hz0ae R (hRsT R hR) I] with
            y hy h0 hyI
          rw [h0, sub_zero, ← hy hyI]
          simp only [Xk, ht4', ↓reduceIte]
        · refine ⟨z t R (hRsT R hR), z (t - 4) R (hRsT R hR), hzt R _, hzt4 R _ ht4',
            fun I hI => ?_⟩
          filter_upwards [hvY t le_rfl htL R (hRsT R hR) I hI,
            hvY (t - 4) ht4 ht4L R (hRsT R hR) I hI] with y h1 h2 hyI
          rw [← h1 hyI, ← h2 hyI]
          simp only [Xk, ht4', ↓reduceIte, LowList.sub_val])
      (hzaB R (hRsT R hR)) (hzbB R (hRsT R hR)) le_rfl
      (fun I hI => by
        obtain ⟨hIT, hRI⟩ := Finset.mem_filter.mp hI
        have hIt := (Finset.mem_filter.mp hIT).1
        have hIH := (Finset.mem_filter.mp hIT).2.2
        subst hRI
        rw [hXiv I hIt hIH]; exact hsz I hIt hIH i)
      (fun I hI => by
        obtain ⟨hIT, hRI⟩ := Finset.mem_filter.mp hI
        have hIt := (Finset.mem_filter.mp hIT).1
        have hIH := (Finset.mem_filter.mp hIT).2.2
        subst hRI
        rw [hXkv I hIt hIH]; exact hsz I hIt hIH k)
      (fun I hI => by
        obtain ⟨hIT, hRI⟩ := Finset.mem_filter.mp hI
        have hIt := (Finset.mem_filter.mp hIT).1
        have hIH := (Finset.mem_filter.mp hIT).2.2
        subst hRI
        rw [hgav I hIt hIH]
        split_ifs
        · exact hfitL2 la I hIt hIH
        · simp)
      (fun I hI => by
        obtain ⟨hIT, hRI⟩ := Finset.mem_filter.mp hI
        have hIt := (Finset.mem_filter.mp hIT).1
        have hIH := (Finset.mem_filter.mp hIT).2.2
        subst hRI
        rw [hgbv I hIt hIH]
        split_ifs
        · exact hfitL2 lb I hIt hIH
        · simp)
      hη₀ (fun I hI s s' hss => by
        obtain ⟨hIT, hRI⟩ := Finset.mem_filter.mp hI
        have hIt := (Finset.mem_filter.mp hIT).1
        have hIH := (Finset.mem_filter.mp hIT).2.2
        subst hRI
        rw [hslots I hIt hIH]; exact hpair I hIt hIH s s' hss)
      Bp ε ka kb Ma Mb hBp hε0 hε1 hka hkb hMa hMb
  expose_names
  exact @baseTuple_stage_3 κ c₂ cp Wp hdefc c₁ C₁ c₂a Ca q hq Cqa G J N w hw f hfm hfq Bf kk M
    roots seg n a g cnt atm hfit u t hut Hc Mt hMt η₀ hη₀ hpair hsz Bp ε K₀ ka kb Ma Mb hε0 hε1
    hpos sa sb hab hai hak hbi hbk hla2 hlb2 hL_def hLne hsegd hRtree hRsT hHl hH1 hWpH X hYval
    hYcard hu4 ht4 huL hu4L htL ht4L hlaL hlbL hcellR hslots hgav hgbv z hz2 hzu hzu4 hzt hzt4 z0
    hz0ae hz0R hzaB hzbB hbase

private theorem baseTuple_stage_1 : BaseTupleStage1Statement := by
  classical
  intro κ c₂ cp Wp hdefc c₁ C₁ c₂a Ca q hq Cqa hfr' G J N w hw f hfm hfq Bf kk M roots seg n a g
    cnt atm hfit u t hut Hc Mt hMt η₀ hη₀ hpair hsz Bp ε K₀ ka kb Ma Mb hBp hε0 hε1 hka hkb hMa
    hMb H D Wa Wb E S₀ Sp i k hpos sa sb hab hai hak hbi hbk la hla2 hla lb hlb2 hlb Lset hL_def
    hLne hsegd Rf Tup Rs hRtree hRsT hWp1 hHl hH1 hWpH X Y hYval hYcard hu4 ht4 Xi Xk Xga Xgb huL
    hu4L htL ht4L hlaL hlbL hcellR hslots
  have hXiv : ∀ (I : ℤ × ℤ) (hI : I ∈ dyadicFiniteTree G J N), kernelHull G J N w I →
      (Xi (Rf I) (hRtree I hI).1).val I = stagTuple f g u t I i := fun I hI hIH => by
    have := congrFun (hslots I hI hIH) i
    rwa [slots4_i hai] at this
  have hXkv : ∀ (I : ℤ × ℤ) (hI : I ∈ dyadicFiniteTree G J N), kernelHull G J N w I →
      (Xk (Rf I) (hRtree I hI).1).val I = stagTuple f g u t I k := fun I hI hIH => by
    have := congrFun (hslots I hI hIH) k
    rwa [slots4_k hak hpos] at this
  have hfitL2 : ∀ ℓ, ∀ I ∈ dyadicFiniteTree G J N, kernelHull G J N w I → eLpNorm (g ℓ I) 2
      (normalizedIntervalMeasure (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1)) ≤
        ENNReal.ofReal 1 := fun ℓ I hI hIH => by
    obtain ⟨-, -, -, -, -, -, hm, hb, hL, -⟩ := ((hfit ℓ).1.2.2.2.2 I hI)
    rw [ENNReal.ofReal_one]
    exact eLpNorm_fit_le hm (hb hIH) (hL hIH)
  have hgav : ∀ (I : ℤ × ℤ) (hI : I ∈ dyadicFiniteTree G J N), kernelHull G J N w I →
      (Xga (Rf I) (hRtree I hI).1).val I = if 1 ≤ la then g la I else 0 := fun I hI hIH => by
    by_cases h1 : 1 ≤ la
    · simp only [Xga, h1, ↓reduceIte]
      exact funext fun y =>
        hYval la hla2.le _ _ I hI (hRtree I hI).2 (hcellR I hI la hlaL) hIH y
    · simp only [Xga, h1, ↓reduceIte, LowList.empty_val]
  have hgbv : ∀ (I : ℤ × ℤ) (hI : I ∈ dyadicFiniteTree G J N), kernelHull G J N w I →
      (Xgb (Rf I) (hRtree I hI).1).val I = if 1 ≤ lb then g lb I else 0 := fun I hI hIH => by
    by_cases h1 : 1 ≤ lb
    · simp only [Xgb, h1, ↓reduceIte]
      exact funext fun y =>
        hYval lb hlb2.le _ _ I hI (hRtree I hI).2 (hcellR I hI lb hlbL) hIH y
    · simp only [Xgb, h1, ↓reduceIte, LowList.empty_val]
  -- the fit opponents
  have hopp := fun (ℓ : ℕ) (R : ℤ × ℤ) (hR : R ∈ dyadicFiniteTree G J N) =>
    (hfit ℓ).2.2 (seg ℓ R) ((hfit ℓ).1.2.2.2.2 R hR).1
  choose z hz1 hz2 hz3 using hopp
  have hzR : ∀ ℓ (R : ℤ × ℤ) (hR : R ∈ dyadicFiniteTree G J N),
      ∀ J' ∈ dyadicFiniteTree G J N, dyadicGridCell G J'.1 J'.2 ⊆ dyadicGridCell G R.1 R.2 →
        IsAdmissibleOpponent G J' (f (stagPos ℓ)) (z ℓ R hR) (fitOpponentConst (M ℓ)) ∧
          HasDepthEnergy G J' (f (stagPos ℓ)) (z ℓ R hR) 1 := fun ℓ R hR J' hJ' hJ'R =>
    (hz3 ℓ R hR).1 J' hJ' (hJ'R.trans ((hfit ℓ).1.2.2.2.2 R hR).2.1)
  -- the fit opponents as basic families below each first-level root
  have hzB : ∀ ℓ (R : ℤ × ℤ) (hR : R ∈ dyadicFiniteTree G J N),
      IsBasicOn G R (dyadicRemainingDepth J N R) 1 (max 2 (M ℓ : ℝ)) c₂ (Bf ℓ) w (z ℓ R hR) :=
    fun ℓ R hR => isBasicOn_of_current hq.le (fun I hI hIH => hfq (stagPos ℓ) I hI (Or.inr hIH))
      hR ((hfit ℓ).1.2.2.2.2 R hR).2.1 (hz3 ℓ R hR).2
  have hBfH : ∀ ℓ ≤ t, Bf ℓ ≤ H := fun ℓ hℓ => by
    have h1 : 1 ≤ max (Bf ℓ) Wp := le_trans hWp1 (le_max_right _ _)
    calc Bf ℓ ≤ max (Bf ℓ) Wp := le_max_left _ _
      _ = max (Bf ℓ) Wp ^ 1 := (pow_one _).symm
      _ ≤ max (Bf ℓ) Wp ^ 6 := pow_le_pow_right₀ h1 (by norm_num)
      _ ≤ H := hHl ℓ hℓ
  -- the column budgets of the fit opponents below a first-level root
  let BdR : ∀ R, R ∈ dyadicFiniteTree G J N → ℝ := fun R hR =>
    2 + ((Fintype.card (Xi R hR).Λ + Fintype.card (Xk R hR).Λ + Fintype.card (Xga R hR).Λ +
      Fintype.card (Xgb R hR).Λ : ℕ) : ℝ)
  have hzBd : ∀ ℓ (R : ℤ × ℤ) (hR : R ∈ dyadicFiniteTree G J N),
      M ℓ ≤ Fintype.card (Xi R hR).Λ + Fintype.card (Xk R hR).Λ + Fintype.card (Xga R hR).Λ +
        Fintype.card (Xgb R hR).Λ → max 2 (M ℓ : ℝ) ≤ BdR R hR := by
    intro ℓ R hR h
    have h' : (M ℓ : ℝ) ≤ ((Fintype.card (Xi R hR).Λ + Fintype.card (Xk R hR).Λ +
        Fintype.card (Xga R hR).Λ + Fintype.card (Xgb R hR).Λ : ℕ) : ℝ) := by exact_mod_cast h
    have h0 : (0 : ℝ) ≤ ((Fintype.card (Xi R hR).Λ + Fintype.card (Xk R hR).Λ +
        Fintype.card (Xga R hR).Λ + Fintype.card (Xgb R hR).Λ : ℕ) : ℝ) := Nat.cast_nonneg _
    exact max_le (by simp only [BdR]; linarith) (by simp only [BdR]; linarith)
  have hcXi : ∀ (R : ℤ × ℤ) (hR : R ∈ dyadicFiniteTree G J N),
      M u ≤ Fintype.card (Xi R hR).Λ ∧ (¬ u ≤ 4 → M (u - 4) ≤ Fintype.card (Xi R hR).Λ) := by
    intro R hR
    by_cases hu4' : u ≤ 4
    · have e : Xi R hR = Y u hut.le R hR := by simp only [Xi, hu4', ↓reduceIte]
      rw [e, hYcard u hut.le R hR]
      exact ⟨le_rfl, fun h => absurd hu4' h⟩
    · have e : Xi R hR = (Y u hut.le R hR).sub (Y (u - 4) hu4 R hR) := by
        simp only [Xi, hu4', ↓reduceIte]
      rw [e, LowList.sub_card, hYcard u hut.le R hR, hYcard (u - 4) hu4 R hR]
      exact ⟨by omega, fun _ => by omega⟩
  have hcXk : ∀ (R : ℤ × ℤ) (hR : R ∈ dyadicFiniteTree G J N),
      M t ≤ Fintype.card (Xk R hR).Λ ∧ (¬ t ≤ 4 → M (t - 4) ≤ Fintype.card (Xk R hR).Λ) := by
    intro R hR
    by_cases ht4' : t ≤ 4
    · have e : Xk R hR = Y t le_rfl R hR := by simp only [Xk, ht4', ↓reduceIte]
      rw [e, hYcard t le_rfl R hR]
      exact ⟨le_rfl, fun h => absurd ht4' h⟩
    · have e : Xk R hR = (Y t le_rfl R hR).sub (Y (t - 4) ht4 R hR) := by
        simp only [Xk, ht4', ↓reduceIte]
      rw [e, LowList.sub_card, hYcard t le_rfl R hR, hYcard (t - 4) ht4 R hR]
      exact ⟨by omega, fun _ => by omega⟩
  have hcXga : ∀ (R : ℤ × ℤ) (hR : R ∈ dyadicFiniteTree G J N), 1 ≤ la →
      M la ≤ Fintype.card (Xga R hR).Λ := by
    intro R hR h1
    have e : Xga R hR = Y la hla2.le R hR := by simp only [Xga, h1, ↓reduceIte]
    rw [e, hYcard la hla2.le R hR]
  have hcXgb : ∀ (R : ℤ × ℤ) (hR : R ∈ dyadicFiniteTree G J N), 1 ≤ lb →
      M lb ≤ Fintype.card (Xgb R hR).Λ := by
    intro R hR h1
    have e : Xgb R hR = Y lb hlb2.le R hR := by simp only [Xgb, h1, ↓reduceIte]
    rw [e, hYcard lb hlb2.le R hR]
  have hzu : ∀ (R : ℤ × ℤ) (hR : R ∈ dyadicFiniteTree G J N),
      IsBasicOn G R (dyadicRemainingDepth J N R) 1 (BdR R hR) (max c₂ cp) H w (z u R hR) :=
    fun R hR => ((hzB u R hR).mono_budget
      (hzBd u R hR (by have := (hcXi R hR).1; omega))).mono_chart (le_max_left _ _)
        (hBfH u hut.le)
  have hzu4 : ∀ (R : ℤ × ℤ) (hR : R ∈ dyadicFiniteTree G J N), ¬ u ≤ 4 →
      IsBasicOn G R (dyadicRemainingDepth J N R) 1 (BdR R hR) (max c₂ cp) H w (z (u - 4) R hR) :=
    fun R hR h => ((hzB (u - 4) R hR).mono_budget
      (hzBd (u - 4) R hR (by have := (hcXi R hR).2 h; omega))).mono_chart (le_max_left _ _)
        (hBfH (u - 4) hu4)
  have hzt : ∀ (R : ℤ × ℤ) (hR : R ∈ dyadicFiniteTree G J N),
      IsBasicOn G R (dyadicRemainingDepth J N R) 1 (BdR R hR) (max c₂ cp) H w (z t R hR) :=
    fun R hR => ((hzB t R hR).mono_budget
      (hzBd t R hR (by have := (hcXk R hR).1; omega))).mono_chart (le_max_left _ _)
        (hBfH t le_rfl)
  expose_names
  exact @baseTuple_stage_2 κ c₂ cp Wp hdefc c₁ C₁ c₂a Ca q hq Cqa hfr' G J N w hw f hfm hfq Bf kk
    M roots seg n a g cnt atm hfit u t hut Hc Mt hMt η₀ hη₀ hpair hsz Bp ε K₀ ka kb Ma Mb hBp hε0
    hε1 hka hkb hMa hMb hpos sa sb hab hai hak hbi hbk hla2 hla hlb2 hlb hL_def hLne hsegd hRtree
    hRsT hHl hH1 hWpH X hYval hYcard hu4 ht4 huL hu4L htL ht4L hlaL hlbL hcellR hslots hXiv hXkv
    hfitL2 hgav hgbv z hz1 hz2 hzR hzB hBfH hzBd hcXi hcXk hcXga hcXgb hzu hzu4 hzt

/-- Blueprint prop:base for one tuple `eq:base-tuple` of the levels `u < t`: the first-level
roots refine the segments of the six fits entering the tuple; on each, `baseFirstRoot` gives
active setups on the cells outside the last `K₀` levels, and `baseBottom` gives active setups
with `Y = X` on the cells of the last `K₀` levels, grouped below fresh roots at depth
`max (J.1 + N + 1 - K₀) (first-level root)`. Every kernel-hull cell of the tree lies in exactly one
active setup, the roots have total length at most `91/3 |J|`, and the length-weighted sum of
`|H_I(X)|` is at most the sum of `|H_I(Y)|` over the active setups plus the replacement error
`baseErr` times the root length. -/
theorem baseTuple (κ : LocalKernelClass) (c₂ : ℕ) (hc₂ : 1 ≤ c₂) :
    ∃ (cp : ℕ) (Wp : ℝ) (c₁ C₁ c₂a Ca : ℕ), 1 ≤ cp ∧ Real.exp 2 ≤ Wp ∧ 1 ≤ c₁ ∧ 1 ≤ c₂a ∧
    ∀ q : ℝ, 2 < q → ∃ (Cqa : ℝ), 0 < Cqa ∧
    ∀ {G : RealDyadicGrid} {J : ℤ × ℤ} {N : ℕ} (w : ℤ × ℤ → ℝ × ℝ → ℂ),
    (∀ I, IsAdmissibleLocalKernel κ (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1) (w I)) →
    ∀ (f : Fin 4 → ℝ → ℂ), (∀ l, Measurable (f l)) →
    (∀ l, ∀ I ∈ dyadicFiniteTree G J N, (I = J ∨ kernelHull G J N w I) →
      eLpNorm (f l) (ENNReal.ofReal q)
        (normalizedIntervalMeasure (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1)) ≤ 1) →
    ∀ {Bf : ℕ → ℝ} {kk M : ℕ → ℕ} {roots : ℕ → Finset (ℤ × ℤ)}
      {seg : ℕ → ℤ × ℤ → ℤ × ℤ} {n : ℕ → ℤ × ℤ → ℕ} {a : ℕ → ℤ × ℤ → ℕ → ℝ → ℂ}
      {g : ℕ → ℤ × ℤ → ℝ → ℂ} {cnt : ℕ → ℤ × ℤ → ℤ × ℤ → ℕ}
      {atm : ℕ → ℤ × ℤ → ℤ × ℤ → ℕ → ℝ → ℂ},
    (∀ ℓ, IsAdaptiveFit c₂ (Bf ℓ) G J N w (stagPos ℓ) q (f (stagPos ℓ)) (kk ℓ) (M ℓ) (roots ℓ)
        (seg ℓ) (n ℓ) (a ℓ) (g ℓ) ∧
      IsAttemptData c₂ (Bf ℓ) G J N (M ℓ) (roots ℓ) (seg ℓ) (n ℓ) (a ℓ) (cnt ℓ) (atm ℓ) ∧
      IsFitOpponent G J N (f (stagPos ℓ)) (roots ℓ) (seg ℓ) (g ℓ) (fitOpponentConst (M ℓ))
        (max 2 (M ℓ : ℝ)) c₂ (Bf ℓ)) →
    ∀ {u t : ℕ}, 1 ≤ u → u < t → stagPos u ≠ stagPos t →
    ∀ {Hc : ℝ} {Mt : ℕ}, (∀ ℓ ≤ t, Bf ℓ ≤ Hc) → (∀ ℓ ≤ t, M ℓ ≤ Mt) →
    ∀ {η₀ : ℝ}, 0 ≤ η₀ →
    (∀ I ∈ dyadicFiniteTree G J N, kernelHull G J N w I → ∀ s s', s ≠ s' →
      PairSmall (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1) (w I) s s'
        (stagTuple f g u t I s) (stagTuple f g u t I s') η₀) →
    (∀ I ∈ dyadicFiniteTree G J N, kernelHull G J N w I → ∀ l, eLpNorm (stagTuple f g u t I l) 2
      (normalizedIntervalMeasure (dyadicGridLeft G I.1 I.2) (dyadicGridLength G I.1)) ≤
        ENNReal.ofReal 2) →
    ∀ (Bp ε : ℝ) (K₀ ka kb Ma Mb : ℕ), 1 ≤ Bp → 0 < ε → ε ≤ 1 → 1 ≤ ka → 1 ≤ kb →
    16 * fitBudget Cqa Ca ka ^ 2 < Ma → 16 * fitBudget Cqa Ca kb ^ 2 < Mb →
    let H := max Hc Wp ^ 6
    let D := max H (Real.exp (C₁ * (1 + Bp + Real.log H) ^ C₁))
    let Wa := 2 * Mt * (2 * Mt) * ⌊D⌋₊ + Ma
    let Wb := 2 * Mt * (2 * Mt) * ⌊D⌋₊ + Mb
    let E := baseErr κ (2 * Mt) (2 * Mt) D Bp ε K₀ Wa Wb (fitOpponentConst Mt)
      (fitOpponentConst Mt)
    let S₀ : ℝ := 1 + 6 * Mt
    let Sp : ℝ := Wa * Real.sqrt (2 ^ K₀ / ε) + 1
    ∃ (ι : Type) (_ : Fintype ι) (A : ι → ActiveSetup κ (max (max c₁ (max c₂ cp)) c₂a)),
      ∑ p, dyadicGridLength G (A p).R.1 ≤ 91 / 3 * dyadicGridLength G J.1 ∧
      (∀ p p' : ι, ∀ I, I ∈ (A p).cells → I ∈ (A p').cells → p = p') ∧
      (∀ p, (A p).cells ⊆ dyadicFiniteTree G J N ∧ (∀ I ∈ (A p).cells, kernelHull G J N w I) ∧
        (∀ I ∈ (A p).cells, ∀ J' : ℤ × ℤ, dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G J'.1 J'.2 →
          dyadicGridCell G J'.1 J'.2 ⊆ dyadicGridCell G (A p).R.1 (A p).R.2 → J' ∈ (A p).cells) ∧
        (A p).G = G ∧ (A p).w = w ∧
        (A p).R ∈ dyadicFiniteTree G J N ∧
        (A p).H = max D (max (fitBudget Cqa Ca ka) (fitBudget Cqa Ca kb)) ∧
        (A p).Dc = Real.sqrt ε⁻¹ ∧ (A p).S = 2 ∧ (A p).η = 4 * η₀ ∧
        Fintype.card (A p).L ≤ 6 * Mt + Wa + Wb ∧
        (∀ I ∈ (A p).cells, ∀ s s', s ≠ s' → PairSmall (dyadicGridLeft G I.1 I.2)
          (dyadicGridLength G I.1) (w I) s s' ((A p).Y I s) ((A p).Y I s')
          (η₀ + (2 + 2 * S₀) * (Real.exp (-(ka : ℝ)) + Real.exp (-(kb : ℝ))) +
            (1 + Sp) * Real.exp (-(kb : ℝ)))) ∧
        (∀ I ∈ (A p).cells, ∀ l, (eLpNorm ((A p).Y I l) 2 ((A p).μ I)).toReal ≤ 2) ∧
        (∀ l, ∑ I ∈ (A p).cells, dyadicGridLength G I.1 *
          (eLpNorm ((A p).U l I) 2 ((A p).μ I)).toReal ^ 2 ≤
            (K₀ : ℝ) ^ 2 * dyadicGridLength G (A p).R.1) ∧
        ∑ I ∈ (A p).cells, dyadicGridLength G I.1 * ‖(A p).Hf I ((A p).z 3 I)‖ ≤
          η₀ * ((K₀ : ℝ) ^ 2 * dyadicGridLength G (A p).R.1) ∧
        (A p).HasColumnRep 1 ∧ (A p).SubRootProps η₀ ((K₀ : ℝ) ^ 2)) ∧
      ∑ I ∈ dyadicFiniteTree G J N, dyadicGridLength G I.1 *
          ‖localProgressionForm (dyadicGridLength G I.1) (w I) (stagTuple f g u t I)‖ ≤
        ∑ p, ∑ I ∈ (A p).cells, dyadicGridLength G I.1 * ‖(A p).Hf I ((A p).Y I)‖ +
          E * (91 / 3 * dyadicGridLength G J.1) := by
  obtain ⟨cp, Wp, hcp, hWp, hdefc, hfl⟩ := fitLowList_exists
  have hc₀ : 1 ≤ max c₂ cp := le_trans hc₂ (le_max_left _ _)
  obtain ⟨c₁, C₁, c₂a, Ca, hc₁, hc₂a, hfr⟩ := baseFirstRoot κ (max c₂ cp) hc₀
  refine ⟨cp, Wp, c₁, C₁, c₂a, Ca, hcp, hWp, hc₁, hc₂a, fun q hq => ?_⟩
  obtain ⟨Cqa, hCqa, hfr'⟩ := hfr q hq
  refine ⟨Cqa, hCqa, ?_⟩
  intro G J N w hw f hfm hfq Bf kk M roots seg n a g cnt atm hfit u t hu hut hpos Hc Mt hHc hMt
    η₀ hη₀ hpair hsz Bp ε K₀ ka kb Ma Mb hBp hε0 hε1 hka hkb hMa hMb H D Wa Wb E S₀ Sp
  classical
  -- the slots
  set i := stagPos u with hi_def
  set k := stagPos t with hk_def
  obtain ⟨sa, sb, hab, hai, hak, hbi, hbk, -⟩ := fin4_other_two i k hpos
  obtain ⟨hla2, hla⟩ := StaggerCell.lastLevel_spec' hak (by omega : 1 ≤ t)
  obtain ⟨hlb2, hlb⟩ := StaggerCell.lastLevel_spec' hbk (by omega : 1 ≤ t)
  set la := StaggerCell.lastLevel sa t with hla_def
  set lb := StaggerCell.lastLevel sb t with hlb_def
  -- the levels and their segments
  set! Lset : Finset ℕ := {u, u - 4, t, t - 4, la, lb} with hL_def
  have hLne : Lset.Nonempty := ⟨u, by simp [hL_def]⟩
  have hLt : ∀ ℓ ∈ Lset, ℓ ≤ t := by
    intro ℓ hℓ
    simp only [hL_def, Finset.mem_insert, Finset.mem_singleton] at hℓ
    omega
  have hsegd : SegData G J N seg Lset := by
    intro ℓ _ I hI
    obtain ⟨hF1, hF2, hF3, -, hF5⟩ := (hfit ℓ).1
    obtain ⟨hs1, hs2, -, hs4, -⟩ := hF5 I hI
    exact ⟨hs2, hF3 hs1, fun I' hI' h1 h2 => (hs4 I' hI' h1 h2).1⟩
  set! Rf := firstRoot seg Lset hLne with hRf_def
  set! Tup := (dyadicFiniteTree G J N).filter (fun I => I.1 + K₀ ≤ J.1 + N ∧ kernelHull G J N w I)
    with hTup_def
  set! Rs := Tup.image Rf with hRs_def
  have hRtree : ∀ I ∈ dyadicFiniteTree G J N, Rf I ∈ dyadicFiniteTree G J N ∧
      dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G (Rf I).1 (Rf I).2 := fun I hI =>
    firstRoot_mem hsegd hI
  have hRsT : ∀ R ∈ Rs, R ∈ dyadicFiniteTree G J N := fun R hR => by
    obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hR
    exact (hRtree I (Finset.mem_filter.mp hI).1).1
  have hsegR : ∀ I ∈ dyadicFiniteTree G J N, ∀ ℓ ∈ Lset, seg ℓ (Rf I) = seg ℓ I :=
    fun I hI ℓ hℓ => seg_firstRoot hsegd hI hℓ
  -- the low lists
  have hWp1 : 1 ≤ Wp := le_trans (by linarith [Real.add_one_le_exp (2 : ℝ)]) hWp
  have hHl : ∀ ℓ ≤ t, max (Bf ℓ) Wp ^ 6 ≤ H := fun ℓ hℓ =>
    pow_le_pow_left₀ (le_trans (by linarith) (le_max_right _ _))
      (max_le_max (hHc ℓ hℓ) le_rfl) 6
  have hH1 : 1 ≤ H := by
    have : 1 ≤ max Hc Wp := le_trans hWp1 (le_max_right _ _)
    exact one_le_pow₀ this
  have hWpH : Wp ≤ H := by
    have h1 : Wp ≤ max Hc Wp := le_max_right _ _
    have h2 : 1 ≤ max Hc Wp := le_trans hWp1 h1
    calc Wp ≤ max Hc Wp := h1
      _ = max Hc Wp ^ 1 := (pow_one _).symm
      _ ≤ max Hc Wp ^ 6 := pow_le_pow_right₀ h2 (by norm_num)
  have hX := fun ℓ (R : ℤ × ℤ) (hR : R ∈ dyadicFiniteTree G J N) =>
    hfl hc₂ (hfit ℓ).1 (hfit ℓ).2.1 hR
  choose X hXcard hXval using hX
  let Y : ∀ ℓ, ℓ ≤ t → ∀ R, R ∈ dyadicFiniteTree G J N → LowList G J N R (max c₂ cp) H :=
    fun ℓ hℓ R hR => (X ℓ R hR).mono le_rfl (hHl ℓ hℓ)
  have hYval : ∀ ℓ (hℓ : ℓ ≤ t) R (hR : R ∈ dyadicFiniteTree G J N), ∀ I ∈ dyadicFiniteTree G J N,
      dyadicGridCell G I.1 I.2 ⊆ dyadicGridCell G R.1 R.2 → seg ℓ I = seg ℓ R →
      kernelHull G J N w I → ∀ y, (Y ℓ hℓ R hR).val I y = g ℓ I y :=
    fun ℓ hℓ R hR I hI hIR hs hIH y => hXval ℓ R hR I hI hIR hs hIH y
  have hYcard : ∀ ℓ (hℓ : ℓ ≤ t) R (hR : R ∈ dyadicFiniteTree G J N),
      Fintype.card (Y ℓ hℓ R hR).Λ = M ℓ := fun ℓ hℓ R hR => hXcard ℓ R hR
  have hu4 : u - 4 ≤ t := by omega
  have ht4 : t - 4 ≤ t := by omega
  let Xi : ∀ R, R ∈ dyadicFiniteTree G J N → LowList G J N R (max c₂ cp) H := fun R hR =>
    if u ≤ 4 then Y u hut.le R hR else (Y u hut.le R hR).sub (Y (u - 4) hu4 R hR)
  let Xk : ∀ R, R ∈ dyadicFiniteTree G J N → LowList G J N R (max c₂ cp) H := fun R hR =>
    if t ≤ 4 then Y t le_rfl R hR else (Y t le_rfl R hR).sub (Y (t - 4) ht4 R hR)
  let Xga : ∀ R, R ∈ dyadicFiniteTree G J N → LowList G J N R (max c₂ cp) H := fun R hR =>
    if 1 ≤ la then Y la hla2.le R hR else LowList.empty
  let Xgb : ∀ R, R ∈ dyadicFiniteTree G J N → LowList G J N R (max c₂ cp) H := fun R hR =>
    if 1 ≤ lb then Y lb hlb2.le R hR else LowList.empty
  -- membership of the levels
  have huL : u ∈ Lset := by simp [hL_def]
  have hu4L : u - 4 ∈ Lset := by simp [hL_def]
  have htL : t ∈ Lset := by simp [hL_def]
  have ht4L : t - 4 ∈ Lset := by simp [hL_def]
  have hlaL : la ∈ Lset := by simp [hL_def]
  have hlbL : lb ∈ Lset := by simp [hL_def]
  -- the cells of a first-level root
  have hcellR : ∀ I ∈ dyadicFiniteTree G J N, ∀ ℓ ∈ Lset,
      seg ℓ I = seg ℓ (Rf I) := fun I hI ℓ hℓ => (hsegR I hI ℓ hℓ).symm
  have hslots : ∀ (I : ℤ × ℤ) (hI : I ∈ dyadicFiniteTree G J N), kernelHull G J N w I →
      slots4 sa i k (f sa - (Xga (Rf I) (hRtree I hI).1).val I) ((Xi (Rf I) (hRtree I hI).1).val I)
        ((Xk (Rf I) (hRtree I hI).1).val I) (f sb - (Xgb (Rf I) (hRtree I hI).1).val I) =
      stagTuple f g u t I := by
    expose_names
    exact @baseTuple_hslots c₂ cp Wp G J N w f Bf seg g u t hut Hc hi_def hpos hk_def sa sb hab
      hai hak hbi hbk hla2 hla_def hlb2 hlb_def hLne hRtree hHl X hYval hu4 ht4 huL hu4L htL ht4L
      hlaL hlbL hcellR
  expose_names
  exact @baseTuple_stage_1 κ c₂ cp Wp hdefc c₁ C₁ c₂a Ca q hq Cqa hfr' G J N w hw f hfm hfq Bf kk
    M roots seg n a g cnt atm hfit u t hut Hc Mt hMt η₀ hη₀ hpair hsz Bp ε K₀ ka kb Ma Mb hBp hε0
    hε1 hka hkb hMa hMb hpos sa sb hab hai hak hbi hbk hla2 hla hlb2 hlb hL_def hLne hsegd hRtree
    hRsT hWp1 hHl hH1 hWpH X hYval hYcard hu4 ht4 huL hu4L htL ht4L hlaL hlbL hcellR hslots

/-! ### Asymptotic toolbox for the parameter choices of prop:base -/

open Filter in
theorem ev_mul_pow_le_exp (c : ℝ) (n : ℕ) : ∀ᶠ L : ℝ in atTop, c * L ^ n ≤ Real.exp L := by
  have h := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero n
  have hc : (0 : ℝ) < 1 / (|c| + 1) := by positivity
  filter_upwards [(h.eventually (gt_mem_nhds hc)), eventually_ge_atTop 0] with L hL hL0
  have he := Real.exp_pos L
  have h1 : L ^ n ≤ Real.exp L / (|c| + 1) := by
    rw [le_div_iff₀ (by positivity)]
    have : L ^ n * Real.exp (-L) * Real.exp L = L ^ n := by
      rw [mul_assoc, ← Real.exp_add]; simp
    have h2 : L ^ n * Real.exp (-L) * (|c| + 1) ≤ 1 := by
      have h3 : L ^ n * Real.exp (-L) * (|c| + 1) < 1 :=
        (lt_div_iff₀ (show (0 : ℝ) < |c| + 1 by positivity)).mp hL
      exact h3.le
    have h4 := mul_le_mul_of_nonneg_right h2 he.le
    have h5 : L ^ n * Real.exp (-L) * (|c| + 1) * Real.exp L = L ^ n * (|c| + 1) := by
      rw [show L ^ n * Real.exp (-L) * (|c| + 1) * Real.exp L =
        (L ^ n * Real.exp (-L) * Real.exp L) * (|c| + 1) by ring, this]
    linarith
  have hcn : c * L ^ n ≤ |c| * L ^ n := mul_le_mul_of_nonneg_right (le_abs_self c)
    (pow_nonneg hL0 n)
  calc c * L ^ n ≤ |c| * L ^ n := hcn
    _ ≤ |c| * (Real.exp L / (|c| + 1)) := mul_le_mul_of_nonneg_left h1 (abs_nonneg c)
    _ ≤ Real.exp L := by
        rw [mul_div_assoc', div_le_iff₀ (by positivity)]
        nlinarith [abs_nonneg c]

open Filter in
theorem ev_mul_pow_le_pow (c : ℝ) (n : ℕ) : ∀ᶠ L : ℝ in atTop, c * L ^ n ≤ L ^ (n + 1) := by
  filter_upwards [eventually_ge_atTop c, eventually_ge_atTop 0] with L hL hL0
  rw [pow_succ]
  nlinarith [pow_nonneg hL0 n]

open Filter in
/-- A polynomial bound eventually below any larger power. -/
theorem ev_poly_le_pow (c : ℝ) {n m : ℕ} (h : n < m) :
    ∀ᶠ L : ℝ in atTop, c * L ^ n ≤ L ^ m := by
  filter_upwards [ev_mul_pow_le_pow c n, eventually_ge_atTop 1] with L hL hL1
  exact hL.trans (pow_le_pow_right₀ hL1 h)

/-- `L^m ≤ e^{m L}`. -/
theorem pow_le_exp_mul {L : ℝ} (hL : 0 ≤ L) (m : ℕ) : L ^ m ≤ Real.exp (m * L) := by
  have h : L ≤ Real.exp L := by linarith [Real.add_one_le_exp L]
  calc L ^ m ≤ Real.exp L ^ m := pow_le_pow_left₀ hL h m
    _ = Real.exp (m * L) := by rw [← Real.exp_nat_mul]

/-- The compression bound of a system of size at most `e^y` with weight `ε = e^{-z}`. -/
theorem compBound_le {W : ℕ} {y z : ℝ} (hy : 0 ≤ y) (hz : 0 ≤ z) (hW : (W : ℝ) ≤ Real.exp y) :
    compBound W (Real.exp (-z)) ≤
      (512 * ((1 : ℕ) + 1 : ℝ) ^ 512 * (3 + y + z)) ^ (512 * (1 + 1)) := by
  unfold compBound
  have hs : (Real.sqrt (Real.exp (-z)))⁻¹ = Real.exp (z / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.exp_mul, ← Real.exp_neg]; ring_nf
  rw [hs]
  have hW0 : (0 : ℝ) ≤ W := Nat.cast_nonneg W
  have he1 : 1 ≤ Real.exp (z / 2) := Real.one_le_exp (by linarith)
  have hey : 1 ≤ Real.exp y := Real.one_le_exp hy
  have hX : 2 * (2 + W + W * Real.exp (z / 2)) ≤ Real.exp (3 + y + z) := by
    have h1 : (W : ℝ) * Real.exp (z / 2) ≤ Real.exp y * Real.exp (z / 2) :=
      mul_le_mul_of_nonneg_right hW (Real.exp_pos _).le
    have h2 : Real.exp y * Real.exp (z / 2) = Real.exp (y + z / 2) := (Real.exp_add _ _).symm
    have h3 : 1 ≤ Real.exp (y + z / 2) := Real.one_le_exp (by linarith)
    have h4 : Real.exp (3 + y + z) = Real.exp 3 * Real.exp (y + z / 2) * Real.exp (z / 2) := by
      rw [← Real.exp_add, ← Real.exp_add]; ring_nf
    have h5 : (8 : ℝ) ≤ Real.exp 3 := by
      have := Real.add_one_le_exp (3 : ℝ)
      have h6 : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
      have h7 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      rw [h6]
      calc (8 : ℝ) = 2 ^ 3 := by norm_num
        _ ≤ Real.exp 1 ^ 3 := pow_le_pow_left₀ (by norm_num) h7 3
    rw [h4]
    have hA : Real.exp y ≤ Real.exp (y + z / 2) := Real.exp_le_exp.mpr (by linarith)
    have hWA : (W : ℝ) ≤ Real.exp (y + z / 2) := hW.trans hA
    have hWB : (W : ℝ) * Real.exp (z / 2) ≤ Real.exp (y + z / 2) := h1.trans h2.le
    have k1 : 2 * (2 + W + W * Real.exp (z / 2)) ≤ 8 * Real.exp (y + z / 2) := by linarith
    have k2 : 8 * Real.exp (y + z / 2) ≤ Real.exp 3 * Real.exp (y + z / 2) :=
      mul_le_mul_of_nonneg_right h5 (Real.exp_pos _).le
    have k3 : Real.exp 3 * Real.exp (y + z / 2) ≤ Real.exp 3 * Real.exp (y + z / 2) *
        Real.exp (z / 2) := le_mul_of_one_le_right (by positivity) he1
    linarith
  have hpos : 0 < 2 * (2 + W + W * Real.exp (z / 2)) := by positivity
  have hlog : Real.log (2 * (2 + W + W * Real.exp (z / 2))) ≤ 3 + y + z := by
    rw [← Real.exp_le_exp, Real.exp_log hpos]; exact hX
  have hl0 : 0 ≤ Real.log (2 * (2 + W + W * Real.exp (z / 2))) :=
    Real.log_nonneg (by nlinarith)
  gcongr

/-- The opponent constant of a fit with at most `e^L` labels. -/
theorem fitOpponentConst_le {M : ℕ} {L : ℝ} (hL : 0 ≤ L) (hM : (M : ℝ) ≤ Real.exp L) :
    fitOpponentConst M ≤ (512 * ((1 : ℕ) + 1 : ℝ) ^ 512 * (L + 2)) ^ (512 * (1 + 1)) := by
  unfold fitOpponentConst
  have h2 : (2 : ℝ) ≤ max 2 (M : ℝ) := le_max_left _ _
  have hmax : max 2 (M : ℝ) ≤ 2 * Real.exp L := by
    have := Real.one_le_exp hL
    exact max_le (by linarith) (by linarith)
  have hlog : Real.log (2 * max 2 (M : ℝ)) ≤ L + 2 := by
    rw [← Real.exp_le_exp, Real.exp_log (by linarith)]
    have h4 : Real.exp (L + 2) = Real.exp L * Real.exp 2 := Real.exp_add _ _
    have h5 : (4 : ℝ) ≤ Real.exp 2 := by
      have h7 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      have h6 : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
      rw [h6]
      calc (4 : ℝ) = 2 ^ 2 := by norm_num
        _ ≤ Real.exp 1 ^ 2 := pow_le_pow_left₀ (by norm_num) h7 2
    rw [h4]; nlinarith [Real.exp_pos L]
  have hl0 : 0 ≤ Real.log (2 * max 2 (M : ℝ)) := Real.log_nonneg (by linarith)
  gcongr

/-- The error expression with uniform bounds on its ingredients. -/
theorem errExpr_le {c cU e T TU K ba bb Cg U : ℝ} (hc : 0 ≤ c) (hcU : c ≤ cU) (he : 0 ≤ e)
    (hT : 0 ≤ T) (hTU : T ≤ TU) (hK : 0 ≤ K) (hKU : K ≤ U) (hba : 0 ≤ ba) (hbaU : ba ≤ U)
    (hbb : 0 ≤ bb) (hbbU : bb ≤ U) (hCg : 0 ≤ Cg) (hCgU : Cg ≤ U) :
    c * ((2 * e * (2 * (ba + K) + 1) + T) * (2 * (1 + Cg) + 4) +
      (2 * e * (2 * (bb + K) + 1) + T) * (2 * (2 * (ba + K) + Cg) + 4)) ≤
    cU * ((2 * e * (4 * U + 1) + TU) * (12 * U + 10)) := by
  have hU : 0 ≤ U := hK.trans hKU
  have h1 : 2 * e * (2 * (ba + K) + 1) + T ≤ 2 * e * (4 * U + 1) + TU := by
    have := mul_le_mul_of_nonneg_left (show 2 * (ba + K) + 1 ≤ 4 * U + 1 by linarith)
      (mul_nonneg zero_le_two he)
    linarith
  have h2 : 2 * e * (2 * (bb + K) + 1) + T ≤ 2 * e * (4 * U + 1) + TU := by
    have := mul_le_mul_of_nonneg_left (show 2 * (bb + K) + 1 ≤ 4 * U + 1 by linarith)
      (mul_nonneg zero_le_two he)
    linarith
  have p1 : 0 ≤ 2 * e * (2 * (ba + K) + 1) + T := by positivity
  have p2 : 0 ≤ 2 * e * (2 * (bb + K) + 1) + T := by positivity
  have hin : (2 * e * (2 * (ba + K) + 1) + T) * (2 * (1 + Cg) + 4) +
      (2 * e * (2 * (bb + K) + 1) + T) * (2 * (2 * (ba + K) + Cg) + 4) ≤
      (2 * e * (4 * U + 1) + TU) * (12 * U + 10) := by
    have k1 := mul_le_mul h1 (show 2 * (1 + Cg) + 4 ≤ 2 * (1 + U) + 4 by linarith) (by positivity)
      (p1.trans h1)
    have k2 := mul_le_mul h2 (show 2 * (2 * (ba + K) + Cg) + 4 ≤ 2 * (2 * (U + U) + U) + 4 by
      linarith) (by positivity) (p2.trans h2)
    nlinarith only [hK, hKU, hba, hbaU, hCg, hCgU, h1, h2, p1]
  have hin0 : 0 ≤ (2 * e * (2 * (ba + K) + 1) + T) * (2 * (1 + Cg) + 4) +
      (2 * e * (2 * (bb + K) + 1) + T) * (2 * (2 * (ba + K) + Cg) + 4) := by positivity
  exact mul_le_mul hcU hin hin0 (hc.trans hcU)

open Filter in
/-- Five-term polynomial sums are eventually below a larger power. -/
theorem ev_sum5_le_pow {c₁ c₂ c₃ c₄ c₅ : ℝ} {n₁ n₂ n₃ n₄ n₅ m : ℕ} (h₁ : n₁ < m) (h₂ : n₂ < m)
    (h₃ : n₃ < m) (h₄ : n₄ < m) (h₅ : n₅ < m) :
    ∀ᶠ L : ℝ in atTop, c₁ * L ^ n₁ + c₂ * L ^ n₂ + c₃ * L ^ n₃ + c₄ * L ^ n₄ + c₅ * L ^ n₅ ≤
      L ^ m := by
  filter_upwards [ev_poly_le_pow (5 * c₁) h₁, ev_poly_le_pow (5 * c₂) h₂,
    ev_poly_le_pow (5 * c₃) h₃, ev_poly_le_pow (5 * c₄) h₄, ev_poly_le_pow (5 * c₅) h₅]
    with L e₁ e₂ e₃ e₄ e₅
  linarith

open Filter in
/-- A polynomial in a power of `L` is eventually below `e^L`. -/
theorem ev_poly_pow_le_exp (c : ℝ) (a b p : ℕ) :
    ∀ᶠ L : ℝ in atTop, (c * (3 + L ^ a + L ^ b)) ^ p ≤ Real.exp L := by
  set m := max a b
  filter_upwards [ev_mul_pow_le_exp ((|c| * 5) ^ p) (m * p), eventually_ge_atTop 1]
    with L hL hL1
  have ha : L ^ a ≤ L ^ m := pow_le_pow_right₀ hL1 (le_max_left _ _)
  have hb : L ^ b ≤ L ^ m := pow_le_pow_right₀ hL1 (le_max_right _ _)
  have h1 : 1 ≤ L ^ m := one_le_pow₀ hL1
  have hs : 3 + L ^ a + L ^ b ≤ 5 * L ^ m := by linarith
  have hs0 : 0 ≤ 3 + L ^ a + L ^ b := by positivity
  calc (c * (3 + L ^ a + L ^ b)) ^ p ≤ (|c| * (5 * L ^ m)) ^ p := by
        calc (c * (3 + L ^ a + L ^ b)) ^ p ≤ |c * (3 + L ^ a + L ^ b)| ^ p := by
              rw [← abs_pow]; exact le_abs_self _
          _ ≤ (|c| * (5 * L ^ m)) ^ p := by
              rw [abs_mul, abs_of_nonneg hs0]
              exact pow_le_pow_left₀ (by positivity)
                (mul_le_mul_of_nonneg_left hs (abs_nonneg c)) _
    _ = (|c| * 5) ^ p * L ^ (m * p) := by rw [pow_mul]; ring
    _ ≤ Real.exp L := hL

theorem exp_add_exp_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.exp a + Real.exp b ≤ Real.exp (a + b + 1) := by
  have h1 : Real.exp a ≤ Real.exp (a + b) := Real.exp_le_exp.mpr (by linarith)
  have h2 : Real.exp b ≤ Real.exp (a + b) := Real.exp_le_exp.mpr (by linarith)
  have h3 : Real.exp (a + b + 1) = Real.exp (a + b) * Real.exp 1 := Real.exp_add _ _
  have h4 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  rw [h3]; nlinarith [Real.exp_pos (a + b)]

theorem fitBudget_le_of {Cqa : ℝ} (hCqa : 0 < Cqa) {Ca k : ℕ} {x X : ℝ} (hk : (k : ℝ) ≤ x + 1)
    (h : Cqa * (1 + Real.log 2 + (x + 1)) ^ Ca ≤ X) : fitBudget Cqa Ca k ≤ Real.exp X := by
  unfold fitBudget
  refine Real.exp_le_exp.mpr (le_trans ?_ h)
  have hl : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  gcongr

theorem nat_fit_le {B : ℝ} (hB : 1 ≤ B) : ((⌊16 * B ^ 2⌋₊ + 1 : ℕ) : ℝ) ≤ Real.exp 3 * B ^ 2 := by
  push_cast
  have h1 : (⌊16 * B ^ 2⌋₊ : ℝ) ≤ 16 * B ^ 2 := Nat.floor_le (by positivity)
  have h2 : (17 : ℝ) ≤ Real.exp 3 := by
    have h7 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have h6 : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
    have h8 : (2.7 : ℝ) ≤ Real.exp 1 := by
      have := Real.exp_one_gt_d9; linarith
    rw [h6]
    calc (17 : ℝ) ≤ 2.7 ^ 3 := by norm_num
      _ ≤ Real.exp 1 ^ 3 := pow_le_pow_left₀ (by norm_num) h8 3
  have h3 : 1 ≤ B ^ 2 := one_le_pow₀ hB
  nlinarith

theorem mul_exp_le_exp {c A B : ℝ} (hc : 0 < c) (h : Real.log c + A ≤ B) :
    c * Real.exp A ≤ Real.exp B := by
  rw [← Real.exp_log hc, ← Real.exp_add]; exact Real.exp_le_exp.mpr h

theorem sqrt_exp' (x : ℝ) : Real.sqrt (Real.exp x) = Real.exp (x / 2) := by
  rw [show Real.exp x = Real.exp (x / 2) ^ 2 by rw [← Real.exp_nat_mul]; ring_nf,
    Real.sqrt_sq (Real.exp_pos _).le]

theorem sqrt_exp_neg (a : ℝ) : Real.sqrt (Real.exp (-a)) = Real.exp (-a / 2) := by
  rw [show Real.exp (-a) = Real.exp (-a / 2) ^ 2 by rw [← Real.exp_nat_mul]; ring_nf,
    Real.sqrt_sq (Real.exp_pos _).le]

theorem final_err_aux {U e TU X : ℝ} (hU : 1 ≤ U) (he : 0 ≤ e) (hTU : 0 ≤ TU)
    (h1 : 880 * e * U ^ 4 ≤ X / 2) (h2 : 88 * U ^ 3 * TU ≤ X / 2) :
    4 * U ^ 2 * ((2 * e * (4 * U + 1) + TU) * (12 * U + 10)) ≤ X := by
  have hU0 : 0 ≤ U := by linarith
  have k1 : 2 * e * (4 * U + 1) ≤ 10 * e * U := by nlinarith
  have k2 : 12 * U + 10 ≤ 22 * U := by linarith
  have k3 : (2 * e * (4 * U + 1) + TU) * (12 * U + 10) ≤ (10 * e * U + TU) * (22 * U) :=
    mul_le_mul (by linarith) k2 (by positivity) (by positivity)
  have k4 : 4 * U ^ 2 * ((2 * e * (4 * U + 1) + TU) * (12 * U + 10)) ≤
      4 * U ^ 2 * ((10 * e * U + TU) * (22 * U)) := mul_le_mul_of_nonneg_left k3 (by positivity)
  have k5 : 4 * U ^ 2 * ((10 * e * U + TU) * (22 * U)) = 880 * e * U ^ 4 + 88 * U ^ 3 * TU := by
    ring
  linarith

end TrilinearHT.Auto
end
