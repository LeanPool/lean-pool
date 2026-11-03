/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

/- Adapted for Lean Pool from roos-j/lean-trilinearht at
7b4209609e6a7fb9d9935973ee8541495f943660. Imports, names, proof organization and
Mathlib interfaces have been updated; original authorship is retained above. -/

public import LeanPool.TrilinearHilbertTransform.Auto.Sec144FixedStacksTwoVaryingSides.Setup

/-!
# Trilinear Hilbert transform: bandStack_block
-/

@[expose] public section

section
namespace TrilinearHT.Auto
open MeasureTheory Metric
open scoped FourierTransform ComplexConjugate ENNReal
namespace ActiveSetup
variable {κ' : LocalKernelClass} {c₀ : ℕ} (A : ActiveSetup κ' c₀)

open scoped Classical in
private def BandStackBlockHlocStatement.{u_1} : Prop :=
  ∀ (κ' : LocalKernelClass)
    (c₀ : ℕ)
    (A : ActiveSetup κ' c₀)
    (V : Type u_1)
    [Fintype V]
    (Zg : ℤ → ↥(ColumnL2 V))
    (K : ℕ)
    (N : ℕ)
    (k : Fin (N + (1 : ℕ)))
    (β : ℕ)
    (Ug : Finset (ℤ × ℤ))
    (off : ℤ × ℤ → ℕ)
    (_ : ∀ (J : ℤ × ℤ), ∀ m < K, J.1 = A.R.1 + (↑(K * β + m) : ℤ) → off J = m)
    (Ah : ℕ → ℤ → ↥(ColumnL2 V) →L[ℂ] ↥(ColumnL2 V))
    (Cj : ℝ)
    (_ : ∀ (n : ℕ) {ι : Type} [Fintype ι] (r t : ι → ℕ), (∀ (i : ι), r i ≤ t i) → (∀ (i i' :
      ι), i ≠ i' → Disjoint (Finset.Ioc (r i) (t i)) (Finset.Ioc (r i') (t i'))) → ∀ (Ec
      : ι → Finset (ℤ × ℤ)), (∀ (i : ι), ∀ J ∈ Ec i, J ∈ A.cells) → ∀ (x : ↥(ColumnL2
      V)), ∑ i : ι, ‖(columnL2Restriction (⋃ J ∈ Ec i, dyadicGridCell A.G J.1 J.2)
      (Finset.measurableSet_biUnion (Ec i) fun (J : ℤ × ℤ) (_ : J ∈ Ec i) =>
      dyadicGridCell_measurable A.G J.1 J.2) : ↥(ColumnL2 V) → ↥(ColumnL2 V)) ((Ah n
      (A.R.1 + (↑(t i) : ℤ)) - Ah n (A.R.1 + (↑(r i) : ℤ)) : ↥(ColumnL2 V) → ↥(ColumnL2
      V)) x)‖ ^ (2 : ℕ) ≤ Cj * ‖x‖ ^ (2 : ℕ)),
  let U' : Finset (ℤ × ℤ) :=
    {I ∈ Ug | posAct N k (off I)}
  let sel : ℤ × ℤ → ℕ :=
    fun (I : ℤ × ℤ) => off I / (2 : ℕ) ^ ((↑k : ℕ) + (1 : ℕ))
  let Qs : Finset ℕ :=
    Finset.image sel U'
  ∀ (_ : ∀ q ∈ Qs, q * (2 : ℕ) ^ ((↑k : ℕ) + (1 : ℕ)) + (2 : ℕ) ^ (↑k : ℕ) < K),
  let dt : ℕ → ℤ :=
    fun (q : ℕ) => A.R.1 + (↑(K * β + (q * (2 : ℕ) ^ ((↑k : ℕ) + (1 : ℕ)) + (2 : ℕ) ^
      (↑k : ℕ))) : ℤ)
  let dr : ℕ → ℤ :=
    fun (q : ℕ) => A.R.1 + (↑(K * β + q * (2 : ℕ) ^ ((↑k : ℕ) + (1 : ℕ))) : ℤ)
  ∀ (_ : ∀ I ∈ U', dt (sel I) ≤ I.1)
    (_ : ∀ (q : ℕ), dr q ≤ dt q)
    (_ : ∀ (q : ℕ), ∀ J ∈ A.posEc U' off (↑k : ℕ) (K * β) q, J ∈ A.cells ∧ J.1 = dt q ∧ ∃ I ∈
      U', sel I = q ∧ J = ancAt A.G I (dt q)),
  let Eq : ℕ → ↥(ColumnL2 V) →L[ℂ] ↥(ColumnL2 V) :=
    fun q => columnL2Restriction (⋃ J ∈ A.posEc U' off k (K * β) q, dyadicGridCell A.G
      J.1 J.2) (Finset.measurableSet_biUnion _ fun J _ => dyadicGridCell_measurable A.G
      J.1 J.2)
  let At : ℕ → ℕ → ↥(ColumnL2 V) →L[ℂ] ↥(ColumnL2 V) :=
    fun (q n : ℕ) => Ah n (dt q)
  let Ar : ℕ → ℕ → ↥(ColumnL2 V) →L[ℂ] ↥(ColumnL2 V) :=
    fun (q n : ℕ) => Ah n (dr q)
  ∀ (_ : ∀ (q n : ℕ) (J : ℤ × ℤ), J.1 ≤ dr q → J.1 ≤ A.R.1 + (↑A.treeDepth : ℤ) →
      columnL2Restriction (dyadicGridCell A.G J.1 J.2) (dyadicGridCell_measurable A.G
      J.1 J.2) ∘SL (At q n - Ar q n) = (At q n - Ar q n) ∘SL columnL2Restriction
      (dyadicGridCell A.G J.1 J.2) (dyadicGridCell_measurable A.G J.1 J.2))
    (_ : ∀ I ∈ U', I.1 ≤ A.R.1 + (↑A.treeDepth : ℤ)),
  let Y : ℕ → ℕ → ↥(ColumnL2 V) :=
    fun (q k' : ℕ) => if (q * (2 : ℕ) ^ ((↑k : ℕ) + (1 : ℕ))).testBit k' = true then Zg
      (A.R.1 + (↑(K * β + (posInt (q * (2 : ℕ) ^ ((↑k : ℕ) + (1 : ℕ))) k').2) : ℤ)) - Zg
      (A.R.1 + (↑(K * β + (posInt (q * (2 : ℕ) ^ ((↑k : ℕ) + (1 : ℕ))) k').1) : ℤ)) else
      (0 : ↥(ColumnL2 V))
  let π : ℕ → ℕ → ℕ :=
    fun (k' q : ℕ) => q * (2 : ℕ) ^ ((↑k : ℕ) + (1 : ℕ)) / (2 : ℕ) ^ (k' + (1 : ℕ))
  let Lf : ℕ → Finset (ℤ × ℤ) :=
    fun (k' : ℕ) => {J ∈ A.posLeft U' off (↑k : ℕ) (K * β) | (off J).testBit k' = true}
  let X : ℕ → ℕ → ↥(ColumnL2 V) :=
    fun k' q' => columnL2Restriction (⋃ J ∈ A.posEc (Lf k') off k' (K * β) q',
      dyadicGridCell A.G J.1 J.2) (Finset.measurableSet_biUnion _ fun J _ =>
      dyadicGridCell_measurable A.G J.1 J.2) (Zg (A.R.1 + ((K * β + (q' * 2 ^ (k' + 1) +
      2 ^ k')) : ℕ)) - Zg (A.R.1 + ((K * β + q' * 2 ^ (k' + 1)) : ℕ)))
  ∀ (k' q : ℕ), q ∈ Qs → (q * (2 : ℕ) ^ ((↑k : ℕ) + (1 : ℕ))).testBit k' = true → ∀ (n
    : ℕ), (Eq q : ↥(ColumnL2 V) → ↥(ColumnL2 V)) ((At q n - Ar q n : ↥(ColumnL2 V) →
    ↥(ColumnL2 V)) (Y q k')) = (Eq q : ↥(ColumnL2 V) → ↥(ColumnL2 V)) ((At q n - Ar q
    n : ↥(ColumnL2 V) → ↥(ColumnL2 V)) (X k' (π k' q)))


open scoped Classical in
private def BandStackBlockStage1Statement.{u_1} : Prop :=
  ∀ (κ' : LocalKernelClass)
    (c₀ : ℕ)
    (A : ActiveSetup κ' c₀)
    (V : Type u_1)
    [Fintype V]
    (Zg : ℤ → ↥(ColumnL2 V))
    (K : ℕ)
    (N : ℕ)
    (k : Fin (N + (1 : ℕ)))
    (_ : (↑k : ℕ) ≠ N)
    (β : ℕ)
    (Ug : Finset (ℤ × ℤ))
    (off : ℤ × ℤ → ℕ)
    (_ : ∀ (J : ℤ × ℤ), ∀ m < K, J.1 = A.R.1 + (↑(K * β + m) : ℤ) → off J = m)
    (P : ℕ)
    (Ah : ℕ → ℤ → ↥(ColumnL2 V) →L[ℂ] ↥(ColumnL2 V))
    (Cj : ℝ)
    (_ : (0 : ℝ) ≤ Cj)
    (_ : ∀ (n : ℕ) {ι : Type} [Fintype ι] (r t : ι → ℕ), (∀ (i : ι), r i ≤ t i) → (∀ (i i' :
      ι), i ≠ i' → Disjoint (Finset.Ioc (r i) (t i)) (Finset.Ioc (r i') (t i'))) → ∀ (Ec
      : ι → Finset (ℤ × ℤ)), (∀ (i : ι), ∀ J ∈ Ec i, J ∈ A.cells) → ∀ (x : ↥(ColumnL2
      V)), ∑ i : ι, ‖(columnL2Restriction (⋃ J ∈ Ec i, dyadicGridCell A.G J.1 J.2)
      (Finset.measurableSet_biUnion (Ec i) fun (J : ℤ × ℤ) (_ : J ∈ Ec i) =>
      dyadicGridCell_measurable A.G J.1 J.2) : ↥(ColumnL2 V) → ↥(ColumnL2 V)) ((Ah n
      (A.R.1 + (↑(t i) : ℤ)) - Ah n (A.R.1 + (↑(r i) : ℤ)) : ↥(ColumnL2 V) → ↥(ColumnL2
      V)) x)‖ ^ (2 : ℕ) ≤ Cj * ‖x‖ ^ (2 : ℕ))
    (Wg : ↥(ColumnL2 V))
    (Sa : ℤ → ↥(ColumnL2 V)),
  let U' : Finset (ℤ × ℤ) :=
    {I ∈ Ug | posAct N k (off I)}
  let sel : ℤ × ℤ → ℕ :=
    fun (I : ℤ × ℤ) => off I / (2 : ℕ) ^ ((↑k : ℕ) + (1 : ℕ))
  let Qs : Finset ℕ :=
    Finset.image sel U'
  ∀ (_ : ∀ q ∈ Qs, q * (2 : ℕ) ^ ((↑k : ℕ) + (1 : ℕ)) + (2 : ℕ) ^ (↑k : ℕ) < K),
  let db : ℤ :=
    A.R.1 + (↑(K * β) : ℤ)
  ∀ (_ : ∀ (h : ℤ), Sa h = Zg h - Zg db + Wg),
  let dt : ℕ → ℤ :=
    fun (q : ℕ) => A.R.1 + (↑(K * β + (q * (2 : ℕ) ^ ((↑k : ℕ) + (1 : ℕ)) + (2 : ℕ) ^
      (↑k : ℕ))) : ℤ)
  let dr : ℕ → ℤ :=
    fun (q : ℕ) => A.R.1 + (↑(K * β + q * (2 : ℕ) ^ ((↑k : ℕ) + (1 : ℕ))) : ℤ)
  ∀ (_ : ∀ I ∈ U', dt (sel I) ≤ I.1)
    (_ : ∀ (q : ℕ), dr q ≤ dt q)
    (_ : ∀ (q : ℕ), ∀ J ∈ A.posEc U' off (↑k : ℕ) (K * β) q, J ∈ A.cells ∧ J.1 = dt q ∧ ∃ I ∈
      U', sel I = q ∧ J = ancAt A.G I (dt q)),
  let Eq : ℕ → ↥(ColumnL2 V) →L[ℂ] ↥(ColumnL2 V) :=
    fun q => columnL2Restriction (⋃ J ∈ A.posEc U' off k (K * β) q, dyadicGridCell A.G
      J.1 J.2) (Finset.measurableSet_biUnion _ fun J _ => dyadicGridCell_measurable A.G
      J.1 J.2)
  let At : ℕ → ℕ → ↥(ColumnL2 V) →L[ℂ] ↥(ColumnL2 V) :=
    fun (q n : ℕ) => Ah n (dt q)
  let Ar : ℕ → ℕ → ↥(ColumnL2 V) →L[ℂ] ↥(ColumnL2 V) :=
    fun (q n : ℕ) => Ah n (dr q)
  ∀ (_ : ∀ q ∈ Qs, ∀ (n : ℕ), Eq q ∘SL At q n = At q n ∘SL Eq q)
    (_ : ∀ (n : ℕ), ∀ s ⊆ Qs, ∀ (x : ↥(ColumnL2 V)), ∑ q ∈ s, ‖(Eq q : ↥(ColumnL2 V) →
      ↥(ColumnL2 V)) ((At q n - Ar q n : ↥(ColumnL2 V) → ↥(ColumnL2 V)) x)‖ ^ (2 : ℕ) ≤
      Cj * ‖x‖ ^ (2 : ℕ))
    (_ : ∀ q ∈ Qs, ∀ (y : ↥(ColumnL2 V)), ∑ p ∈ Finset.range (P + (1 : ℕ)), ‖(At q (p + (1 :
      ℕ)) - At q p : ↥(ColumnL2 V) → ↥(ColumnL2 V)) y‖ ^ (2 : ℕ) ≤ ‖y‖ ^ (2 : ℕ))
    (_ : ∀ (q n : ℕ) (J : ℤ × ℤ), J.1 ≤ dr q → J.1 ≤ A.R.1 + (↑A.treeDepth : ℤ) →
      columnL2Restriction (dyadicGridCell A.G J.1 J.2) (dyadicGridCell_measurable A.G
      J.1 J.2) ∘SL (At q n - Ar q n) = (At q n - Ar q n) ∘SL columnL2Restriction
      (dyadicGridCell A.G J.1 J.2) (dyadicGridCell_measurable A.G J.1 J.2))
    (_ : ∀ I ∈ U', I.1 ≤ A.R.1 + (↑A.treeDepth : ℤ)),
  let Wr : ↥(ColumnL2 V) :=
    columnL2Restriction (⋃ J ∈ U'.image (fun I => ancAt A.G I db), dyadicGridCell A.G
      J.1 J.2) (Finset.measurableSet_biUnion _ fun J _ => dyadicGridCell_measurable A.G
      J.1 J.2) Wg
  ∀ (_ : ∀ q ∈ Qs, ∀ (n : ℕ), (Eq q : ↥(ColumnL2 V) → ↥(ColumnL2 V)) ((At q n - Ar q n :
      ↥(ColumnL2 V) → ↥(ColumnL2 V)) Wg) = (Eq q : ↥(ColumnL2 V) → ↥(ColumnL2 V)) ((At q
      n - Ar q n : ↥(ColumnL2 V) → ↥(ColumnL2 V)) Wr)),
  let Y : ℕ → ℕ → ↥(ColumnL2 V) :=
    fun (q k' : ℕ) => if (q * (2 : ℕ) ^ ((↑k : ℕ) + (1 : ℕ))).testBit k' = true then Zg
      (A.R.1 + (↑(K * β + (posInt (q * (2 : ℕ) ^ ((↑k : ℕ) + (1 : ℕ))) k').2) : ℤ)) - Zg
      (A.R.1 + (↑(K * β + (posInt (q * (2 : ℕ) ^ ((↑k : ℕ) + (1 : ℕ))) k').1) : ℤ)) else
      (0 : ↥(ColumnL2 V))
  ∀ (_ : ∀ q ∈ Qs, Zg (dr q) - Zg db = ∑ k' ∈ Finset.range N, Y q k'),
  ∑ q ∈ Qs, ∑ p ∈ Finset.range (P + (1 : ℕ)), ‖gluedStack A.G U' sel (fun (q : ℕ) =>
    posVal (fun (n : ℕ) => (Ah (p + (1 : ℕ)) (A.R.1 + (↑(K * β + n) : ℤ)) - Ah p
    (A.R.1 + (↑(K * β + n) : ℤ)) : ↥(ColumnL2 V) → ↥(ColumnL2 V)) (Sa (A.R.1 + (↑(K *
    β + n) : ℤ)))) N k q) q‖ ^ (2 : ℕ) ≤ (2 : ℝ) * ∑ q ∈ Qs, ‖(columnL2Restriction (⋃
    J ∈ A.posEc U' off (↑k : ℕ) (K * β) q, dyadicGridCell A.G J.1 J.2)
    (Finset.measurableSet_biUnion (A.posEc U' off (↑k : ℕ) (K * β) q) fun (J : ℤ × ℤ)
    (_ : J ∈ A.posEc U' off (↑k : ℕ) (K * β) q) => dyadicGridCell_measurable A.G J.1
    J.2) : ↥(ColumnL2 V) → ↥(ColumnL2 V)) (Zg (A.R.1 + (↑(K * β + (q * (2 : ℕ) ^ ((↑k
    : ℕ) + (1 : ℕ)) + (2 : ℕ) ^ (↑k : ℕ))) : ℤ)) - Zg (A.R.1 + (↑(K * β + q * (2 : ℕ)
    ^ ((↑k : ℕ) + (1 : ℕ))) : ℤ)))‖ ^ (2 : ℕ) + (16 : ℝ) * ((↑P : ℝ) + (2 : ℝ)) * (Cj
    * ‖Wr‖ ^ (2 : ℕ)) + (16 : ℝ) * ((↑P : ℝ) + (2 : ℝ)) * ((↑N : ℝ) * (Cj * ∑ k' : Fin
    N, ∑ q' ∈ Finset.image (fun (J : ℤ × ℤ) => off J / (2 : ℕ) ^ ((↑k' : ℕ) + (1 :
    ℕ))) ({J ∈ A.posLeft U' off (↑k : ℕ) (K * β) | posAct N k'.castSucc (off J)}),
    ‖(columnL2Restriction (⋃ J ∈ A.posEc ({J ∈ A.posLeft U' off (↑k : ℕ) (K * β) |
    posAct N k'.castSucc (off J)}) off (↑k' : ℕ) (K * β) q', dyadicGridCell A.G J.1
    J.2) (Finset.measurableSet_biUnion (A.posEc ({J ∈ A.posLeft U' off (↑k : ℕ) (K *
    β) | posAct N k'.castSucc (off J)}) off (↑k' : ℕ) (K * β) q') fun (J : ℤ × ℤ) (_ :
    J ∈ A.posEc ({J ∈ A.posLeft U' off (↑k : ℕ) (K * β) | posAct N k'.castSucc (off
    J)}) off (↑k' : ℕ) (K * β) q') => dyadicGridCell_measurable A.G J.1 J.2) :
    ↥(ColumnL2 V) → ↥(ColumnL2 V)) (Zg (A.R.1 + (↑(K * β + (q' * (2 : ℕ) ^ ((↑k' : ℕ)
    + (1 : ℕ)) + (2 : ℕ) ^ (↑k' : ℕ))) : ℤ)) - Zg (A.R.1 + (↑(K * β + q' * (2 : ℕ) ^
    ((↑k' : ℕ) + (1 : ℕ))) : ℤ)))‖ ^ (2 : ℕ)))




private theorem bandStack_block_hloc : BandStackBlockHlocStatement := by
  classical
  intro κ' c₀ A V inst Zg K N k β Ug off hoff Ah Cj hJ U' sel Qs hQs dt dr hIdep hdrt hcellt Eq At
    Ar hcommT hN Y π Lf X k' q hq hb n
  have hlt := hQs q hq
  have hpos := posInt_le hb
  simp only [Y, hb, ite_true, X]
  refine restrict_sandwich (V := V) (T := At q n - Ar q n) (C := ⋃ J ∈ (U'.filter fun I => sel I
    = q).image
    (fun I => ancAt A.G I (dr q)), dyadicGridCell A.G J.1 J.2) _
    (Finset.measurableSet_biUnion _ fun J _ => dyadicGridCell_measurable A.G J.1 J.2) _
    ?_ ?_ ?_ _
  · intro y hy
    simp only [Set.mem_iUnion] at hy ⊢
    obtain ⟨J, hJ, hyJ⟩ := hy
    obtain ⟨-, -, I, hI, hIq, rfl⟩ := hcellt q J hJ
    refine ⟨ancAt A.G I (dr q), Finset.mem_image_of_mem _ (Finset.mem_filter.mpr ⟨hI, hIq⟩),
      ?_⟩
    have hd : dt q ≤ I.1 := by rw [← hIq]; exact hIdep I hI
    exact ancAt_mono A.G I (hdrt q) hd hyJ
  · intro y hy
    simp only [Set.mem_iUnion] at hy ⊢
    obtain ⟨J, hJ, hyJ⟩ := hy
    obtain ⟨I, hIf, rfl⟩ := Finset.mem_image.mp hJ
    obtain ⟨hI, hIq⟩ := Finset.mem_filter.mp hIf
    have hJd : (ancAt A.G I (dr q)).1 = dr q := rfl
    have hoffJ : off (ancAt A.G I (dr q)) = q * 2 ^ ((k : ℕ) + 1) :=
      hoff _ _ (lt_of_le_of_lt (Nat.le_add_right _ _) hlt) hJd
    have hJmem : ancAt A.G I (dr q) ∈ Lf k' := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨I, hI, ?_⟩, by rw [hoffJ]; exact hb⟩
      simp only [dr]
      rw [show off I / 2 ^ ((k : ℕ) + 1) = q from hIq]
    refine ⟨ancAt A.G (ancAt A.G I (dr q))
      (A.R.1 + ((K * β + (π k' q * 2 ^ (k' + 1) + 2 ^ k')) : ℕ)),
      (A.mem_posEc).mpr ⟨_, hJmem, by rw [hoffJ], rfl⟩, ?_⟩
    refine subset_ancAt A.G _ ?_ hyJ
    rw [hJd]
    have h3 : K * β + (π k' q * 2 ^ (k' + 1) + 2 ^ k') ≤ K * β + q * 2 ^ ((k : ℕ) + 1) :=
      Nat.add_le_add_left hpos.2 _
    have h4 : ((K * β + (π k' q * 2 ^ (k' + 1) + 2 ^ k') : ℕ) : ℤ) ≤
        ((K * β + q * 2 ^ ((k : ℕ) + 1) : ℕ) : ℤ) := by exact_mod_cast h3
    change A.R.1 + _ ≤ A.R.1 + _
    linarith
  · refine union_commute A.G _ (d := dr q) (fun J hJ => ?_) _
      fun J hJ => hcommT q n J ?_ ?_
    · obtain ⟨I, -, rfl⟩ := Finset.mem_image.mp hJ; rfl
    · obtain ⟨I, -, rfl⟩ := Finset.mem_image.mp hJ; exact le_rfl
    · obtain ⟨I, hIf, rfl⟩ := Finset.mem_image.mp hJ
      obtain ⟨hI, hIq⟩ := Finset.mem_filter.mp hIf
      have h1 : dt q ≤ I.1 := by rw [← hIq]; exact hIdep I hI
      exact ((hdrt q).trans h1).trans (hN I hI)
-- the used inner positions are inner positions of the pseudo-uses



private theorem bandStack_block_stage_1 : BandStackBlockStage1Statement := by
  classical
  intro κ' c₀ A V inst Zg K N k hk β Ug off hoff P Ah Cj hCj hJ Wg Sa U' sel Qs hQs db hSa dt dr
    hIdep hdrt hcellt Eq At Ar hcomm' hJ' hbes' hcommT hN Wr hW Y hY
  set! π : ℕ → ℕ → ℕ := fun k' q => q * 2 ^ ((k : ℕ) + 1) / 2 ^ (k' + 1)
  set! Lf : ℕ → Finset (ℤ × ℤ) := fun k' =>
    (A.posLeft U' off k (K * β)).filter fun J => (off J).testBit k' = true
  set! X : ℕ → ℕ → ColumnL2 V := fun k' q' =>
    columnL2Restriction (⋃ J ∈ A.posEc (Lf k') off k' (K * β) q', dyadicGridCell A.G J.1 J.2)
      (Finset.measurableSet_biUnion _ fun J _ => dyadicGridCell_measurable A.G J.1 J.2)
      (Zg (A.R.1 + ((K * β + (q' * 2 ^ (k' + 1) + 2 ^ k')) : ℕ)) -
        Zg (A.R.1 + ((K * β + q' * 2 ^ (k' + 1)) : ℕ)))
  have hloc : ∀ k', ∀ q ∈ Qs, (q * 2 ^ ((k : ℕ) + 1)).testBit k' = true → ∀ n,
      Eq q ((At q n - Ar q n) (Y q k')) = Eq q ((At q n - Ar q n) (X k' (π k' q))) := by
    expose_names
    exact @bandStack_block_hloc κ' c₀ A V inst Zg K N k β Ug off hoff Ah Cj hJ hQs hIdep hdrt
      hcellt hcommT hN
  have hinner : ∀ k', ∀ q ∈ Qs, (q * 2 ^ ((k : ℕ) + 1)).testBit k' = true →
      π k' q ∈ (Lf k').image fun J => off J / 2 ^ (k' + 1) := by
    intro k' q hq hb
    obtain ⟨I, hI, hIq⟩ := Finset.mem_image.mp hq
    have hlt := hQs q hq
    have hJd : (ancAt A.G I (dr q)).1 = dr q := rfl
    have hoffJ : off (ancAt A.G I (dr q)) = q * 2 ^ ((k : ℕ) + 1) :=
      hoff _ _ (lt_of_le_of_lt (Nat.le_add_right _ _) hlt) hJd
    refine Finset.mem_image.mpr ⟨ancAt A.G I (dr q), Finset.mem_filter.mpr
      ⟨Finset.mem_image.mpr ⟨I, hI, ?_⟩, by rw [hoffJ]; exact hb⟩, by rw [hoffJ]⟩
    simp only [dr]
    rw [show off I / 2 ^ ((k : ℕ) + 1) = q from hIq]
  have hstep1 : ∀ q ∈ Qs, ∀ p ∈ Finset.range (P + 1),
      ‖gluedStack A.G U' sel
        (fun q => posVal (fun n => (Ah (p + 1) (A.R.1 + (K * β + n : ℕ)) -
          Ah p (A.R.1 + (K * β + n : ℕ))) (Sa (A.R.1 + (K * β + n : ℕ)))) N k q) q‖ ^ 2 ≤
      ‖Eq q ((At q (p + 1) - At q p) (Sa (dt q)) - (Ar q (p + 1) - Ar q p) (Sa (dr q)))‖ ^ 2 := by
    intro q _ p _
    have hsub := selUnion_sub_anc A.G U' sel dt (fun I hI => hIdep I hI) q
    refine (gluedStack_norm_sq_le A.G _ _ _ q (Finset.measurableSet_biUnion
      (A.posEc U' off k (K * β) q) fun J _ => dyadicGridCell_measurable A.G J.1 J.2)
      hsub).trans (le_of_eq ?_)
    simp only [posVal, hk, ite_false]
    rfl
  have hYu : ∀ q k', ¬ (q * 2 ^ ((k : ℕ) + 1)).testBit k' = true → Y q k' = 0 := by
    intro q k' h
    exact ite_eq_right_iff.mpr fun h' => absurd h' h
  have hBB := band_block (P := P) Qs Eq At Ar hbes' hcomm' hJ' (fun q => Sa (dt q))
    (fun q => Sa (dr q)) (fun q => Zg (dr q) - Zg db) Wg Wr
    (fun q _ => by rw [hSa]) hW Y hY (fun k' q => (q * 2 ^ ((k : ℕ) + 1)).testBit k' = true)
    hYu π X (fun k' q hq hb n => hloc k' q hq hb n)
  calc _ ≤ ∑ q ∈ Qs, ∑ p ∈ Finset.range (P + 1),
        ‖Eq q ((At q (p + 1) - At q p) (Sa (dt q)) - (Ar q (p + 1) - Ar q p) (Sa (dr q)))‖ ^ 2 :=
        Finset.sum_le_sum fun q hq => Finset.sum_le_sum fun p hp => hstep1 q hq p hp
    _ ≤ _ := hBB
    _ ≤ _ := by
        have e1 : ∀ q, Sa (dt q) - Sa (dr q) = Zg (dt q) - Zg (dr q) := fun q => by
          rw [hSa, hSa]; abel
        simp only [e1]
        refine add_le_add le_rfl (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left ?_ hCj) (Nat.cast_nonneg _)) (by positivity))
        · rw [Finset.sum_range (fun k' => ∑ q' ∈ (Qs.filter fun q =>
            (q * 2 ^ ((k : ℕ) + 1)).testBit k' = true).image (π k'), ‖X k' q'‖ ^ 2)]
          refine Finset.sum_le_sum fun k' _ => ?_
          have hf : Lf k' = (A.posLeft U' off k (K * β)).filter
              fun J => posAct N (Fin.castSucc k') (off J) := by
            refine Finset.filter_congr fun J _ => ?_
            simp only [posAct, Fin.val_castSucc]
            have := k'.2
            constructor
            · intro h; exact Or.inr h
            · rintro (h | h)
              · omega
              · exact h
          have hsub : (Qs.filter fun q => (q * 2 ^ ((k : ℕ) + 1)).testBit k' = true).image
              (π k') ⊆ (Lf k').image fun J => off J / 2 ^ ((k' : ℕ) + 1) := by
            intro q' hq'
            obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hq'
            obtain ⟨hqQ, hb⟩ := Finset.mem_filter.mp hq
            exact hinner k' q hqQ hb
          refine (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity).trans
            (le_of_eq ?_)
          simp only [X]
          rw [hf]


open Classical in
/-- `band_block` for the uses of one group in one block, with the ancestor unions of the
positions and the inner positions of the pseudo-uses `posLeft`. -/
theorem bandStack_block (hanc : A.AncClosed) {V : Type*} [Fintype V] (Zg : ℤ → ColumnL2 V)
    {K N : ℕ} (hKN : K ≤ 2 ^ N) (k : Fin (N + 1)) (hk : (k : ℕ) ≠ N) (β : ℕ)
    (Ug : Finset (ℤ × ℤ)) (off : ℤ × ℤ → ℕ)
    (hoff : ∀ (J : ℤ × ℤ) (m : ℕ), m < K → J.1 = A.R.1 + ((K * β + m : ℕ) : ℤ) → off J = m)
    (hU : ∀ I ∈ Ug, I ∈ A.cells ∧ I.1 = A.R.1 + (K * β + off I : ℕ) ∧ off I < K)
    {P : ℕ} (Ah : ℕ → ℤ → ColumnL2 V →L[ℂ] ColumnL2 V)
    (hbes : ∀ h y, ∑ p ∈ Finset.range (P + 1), ‖(Ah (p + 1) h - Ah p h) y‖ ^ 2 ≤ ‖y‖ ^ 2)
    (hcomm : ∀ n h (J : ℤ × ℤ), J.1 ≤ h → J.1 ≤ A.R.1 + A.treeDepth →
      (columnL2Restriction (dyadicGridCell A.G J.1 J.2)
      (dyadicGridCell_measurable A.G J.1 J.2)).comp (Ah n h) =
        (Ah n h).comp (columnL2Restriction (dyadicGridCell A.G J.1 J.2)
          (dyadicGridCell_measurable A.G J.1 J.2)))
    {Cj : ℝ} (hCj : 0 ≤ Cj) (hJ : ∀ n, ∀ {ι : Type} [Fintype ι] (r t : ι → ℕ), (∀ i, r i ≤ t i) →
      (∀ i i', i ≠ i' → Disjoint (Finset.Ioc (r i) (t i)) (Finset.Ioc (r i') (t i'))) →
      ∀ Ec : ι → Finset (ℤ × ℤ), (∀ i, ∀ J ∈ Ec i, J ∈ A.cells) → ∀ x,
      ∑ i, ‖columnL2Restriction (⋃ J ∈ Ec i, dyadicGridCell A.G J.1 J.2)
        (Finset.measurableSet_biUnion _ fun J _ => dyadicGridCell_measurable A.G J.1 J.2)
        ((Ah n (A.R.1 + t i) - Ah n (A.R.1 + r i)) x)‖ ^ 2 ≤ Cj * ‖x‖ ^ 2)
    (Wg : ColumnL2 V) (Sa : ℤ → ColumnL2 V)
    (hSa : ∀ h, Sa h = Zg h - Zg (A.R.1 + ((K * β : ℕ) : ℤ)) + Wg) :
    ∑ q ∈ (Ug.filter fun I => posAct N k (off I)).image (fun I => off I / 2 ^ ((k : ℕ) + 1)),
      ∑ p ∈ Finset.range (P + 1),
      ‖gluedStack A.G (Ug.filter fun I => posAct N k (off I))
        (fun I => off I / 2 ^ ((k : ℕ) + 1))
        (fun q => posVal (fun n => (Ah (p + 1) (A.R.1 + (K * β + n : ℕ)) -
          Ah p (A.R.1 + (K * β + n : ℕ))) (Sa (A.R.1 + (K * β + n : ℕ)))) N k q) q‖ ^ 2 ≤
      2 * ∑ q ∈ (Ug.filter fun I => posAct N k (off I)).image
          (fun I => off I / 2 ^ ((k : ℕ) + 1)),
        ‖columnL2Restriction (⋃ J ∈ A.posEc (Ug.filter fun I => posAct N k (off I)) off k
            (K * β) q, dyadicGridCell A.G J.1 J.2)
          (Finset.measurableSet_biUnion _ fun J _ => dyadicGridCell_measurable A.G J.1 J.2)
          (Zg (A.R.1 + ((K * β + (q * 2 ^ ((k : ℕ) + 1) + 2 ^ (k : ℕ))) : ℕ)) -
            Zg (A.R.1 + ((K * β + q * 2 ^ ((k : ℕ) + 1)) : ℕ)))‖ ^ 2 +
      16 * (P + 2) * (Cj * ‖columnL2Restriction
        (⋃ J ∈ (Ug.filter fun I => posAct N k (off I)).image
          (fun I => ancAt A.G I (A.R.1 + ((K * β : ℕ) : ℤ))), dyadicGridCell A.G J.1 J.2)
        (Finset.measurableSet_biUnion _ fun J _ => dyadicGridCell_measurable A.G J.1 J.2) Wg‖ ^ 2) +
      16 * (P + 2) * (N * (Cj * ∑ k' : Fin N,
        ∑ q' ∈ ((A.posLeft (Ug.filter fun I => posAct N k (off I)) off k (K * β)).filter
            fun J => posAct N (Fin.castSucc k') (off J)).image
          (fun J => off J / 2 ^ ((k' : ℕ) + 1)),
        ‖columnL2Restriction (⋃ J ∈ A.posEc ((A.posLeft (Ug.filter fun I => posAct N k (off I))
            off k (K * β)).filter fun J => posAct N (Fin.castSucc k') (off J)) off k' (K * β) q',
            dyadicGridCell A.G J.1 J.2)
          (Finset.measurableSet_biUnion _ fun J _ => dyadicGridCell_measurable A.G J.1 J.2)
          (Zg (A.R.1 + ((K * β + (q' * 2 ^ ((k' : ℕ) + 1) + 2 ^ (k' : ℕ))) : ℕ)) -
            Zg (A.R.1 + ((K * β + q' * 2 ^ ((k' : ℕ) + 1)) : ℕ)))‖ ^ 2)) := by
  set U' := Ug.filter fun I => posAct N k (off I) with hU'def
  set sel : ℤ × ℤ → ℕ := fun I => off I / 2 ^ ((k : ℕ) + 1) with hseldef
  set Qs := U'.image sel with hQsdef
  have hU'U : U' ⊆ Ug := Finset.filter_subset _ _
  have huse : ∀ I ∈ U', sel I * 2 ^ ((k : ℕ) + 1) + 2 ^ (k : ℕ) ≤ off I := fun I hI =>
    posEnd_le hk (Finset.mem_filter.mp hI).2
  have hQs : ∀ q ∈ Qs, q * 2 ^ ((k : ℕ) + 1) + 2 ^ (k : ℕ) < K := by
    intro q hq
    obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hq
    exact lt_of_le_of_lt (huse I hI) (hU I (hU'U hI)).2.2
  -- depths
  set db : ℤ := A.R.1 + ((K * β : ℕ) : ℤ)
  set! dt : ℕ → ℤ := fun q => A.R.1 + ((K * β + (q * 2 ^ ((k : ℕ) + 1) + 2 ^ (k : ℕ))) : ℕ)
  set! dr : ℕ → ℤ := fun q => A.R.1 + ((K * β + q * 2 ^ ((k : ℕ) + 1)) : ℕ)
  have hIdep : ∀ I ∈ U', dt (sel I) ≤ I.1 := by
    intro I hI
    have h1 := huse I hI
    rw [(hU I (hU'U hI)).2.1]
    simp only [dt]
    push_cast
    have : ((sel I * 2 ^ ((k : ℕ) + 1) + 2 ^ (k : ℕ) : ℕ) : ℤ) ≤ (off I : ℤ) := by
      exact_mod_cast h1
    push_cast at this
    linarith
  have hdrt : ∀ q, dr q ≤ dt q := fun q => by
    simp only [dr, dt]; push_cast
    have : (0 : ℤ) ≤ 2 ^ (k : ℕ) := by positivity
    linarith
  have hbr : ∀ q, db ≤ dr q := fun q => by
    simp only [db, dr]; push_cast
    have : (0 : ℤ) ≤ (q : ℤ) * 2 ^ ((k : ℕ) + 1) := by positivity
    linarith
  have hRb : A.R.1 ≤ db := by simp only [db]; omega
  -- the cells of the ancestor unions
  have hcellt : ∀ q, ∀ J ∈ A.posEc U' off k (K * β) q, J ∈ A.cells ∧ J.1 = dt q ∧
      ∃ I ∈ U', sel I = q ∧ J = ancAt A.G I (dt q) := by
    intro q J hJ
    obtain ⟨I, hI, hq, rfl⟩ := (A.mem_posEc).mp hJ
    have hIc := (hU I (hU'U hI)).1
    have hd : dt q ≤ I.1 := by rw [← hq]; exact hIdep I hI
    exact ⟨hanc I hIc _ (subset_ancAt A.G I hd) (ancAt_subset (A.sub I hIc)
      ((hRb.trans (hbr q)).trans (hdrt q))), rfl, I, hI, hq, rfl⟩
  set! Eq : ℕ → ColumnL2 V →L[ℂ] ColumnL2 V := fun q =>
    columnL2Restriction (⋃ J ∈ A.posEc U' off k (K * β) q, dyadicGridCell A.G J.1 J.2)
      (Finset.measurableSet_biUnion _ fun J _ => dyadicGridCell_measurable A.G J.1 J.2)
  set! At : ℕ → ℕ → ColumnL2 V →L[ℂ] ColumnL2 V := fun q n => Ah n (dt q)
  set! Ar : ℕ → ℕ → ColumnL2 V →L[ℂ] ColumnL2 V := fun q n => Ah n (dr q)
  have hcomm' : ∀ q ∈ Qs, ∀ n, (Eq q).comp (At q n) = (At q n).comp (Eq q) := by
    intro q _ n
    exact union_commute A.G _ (fun J hJ => (hcellt q J hJ).2.1) _
      fun J hJ => hcomm n (dt q) J (le_of_eq (hcellt q J hJ).2.1)
        ((dyadicFiniteTree_mem_iff A.G A.R J A.treeDepth).mp
          (A.cells_mem_tree (hcellt q J hJ).1)).2
  have hJ' : ∀ n, ∀ s ⊆ Qs, ∀ x, ∑ q ∈ s, ‖Eq q ((At q n - Ar q n) x)‖ ^ 2 ≤ Cj * ‖x‖ ^ 2 := by
    intro n s hs x
    have h := hJ n (ι := {q // q ∈ s}) (fun q => K * β + q.1 * 2 ^ ((k : ℕ) + 1))
      (fun q => K * β + (q.1 * 2 ^ ((k : ℕ) + 1) + 2 ^ (k : ℕ)))
      (fun q => Nat.add_le_add_left (Nat.le_add_right _ _) _)
      (fun q q' hqq => posIoc_disjoint_shift (K * β) fun h => hqq (Subtype.ext h))
      (fun q => A.posEc U' off k (K * β) q.1) (fun q J hJ => (hcellt q.1 J hJ).1) x
    rw [← Finset.sum_coe_sort s]
    exact h
  have hbes' : ∀ q ∈ Qs, ∀ y, ∑ p ∈ Finset.range (P + 1),
      ‖(At q (p + 1) - At q p) y‖ ^ 2 ≤ ‖y‖ ^ 2 := fun q _ y => hbes (dt q) y
  have hcommT : ∀ q n (J : ℤ × ℤ), J.1 ≤ dr q → J.1 ≤ A.R.1 + A.treeDepth →
      (columnL2Restriction (dyadicGridCell A.G J.1 J.2)
        (dyadicGridCell_measurable A.G J.1 J.2)).comp (At q n - Ar q n) =
      (At q n - Ar q n).comp (columnL2Restriction (dyadicGridCell A.G J.1 J.2)
        (dyadicGridCell_measurable A.G J.1 J.2)) := by
    intro q n J hJ hJN
    rw [ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp,
      hcomm n (dt q) J (hJ.trans (hdrt q)) hJN, hcomm n (dr q) J hJ hJN]
  have hN : ∀ I ∈ U', I.1 ≤ A.R.1 + A.treeDepth := fun I hI =>
    ((dyadicFiniteTree_mem_iff A.G A.R I A.treeDepth).mp (A.cells_mem_tree (hU I (hU'U hI)).1)).2
  -- the fixed block input
  set Wr := columnL2Restriction (⋃ J ∈ U'.image (fun I => ancAt A.G I db),
    dyadicGridCell A.G J.1 J.2)
    (Finset.measurableSet_biUnion _ fun J _ => dyadicGridCell_measurable A.G J.1 J.2) Wg
  have hW : ∀ q ∈ Qs, ∀ n, Eq q ((At q n - Ar q n) Wg) = Eq q ((At q n - Ar q n) Wr) := by
    intro q _ n
    refine restrict_sandwich _ (Finset.measurableSet_biUnion _ fun J _ =>
      dyadicGridCell_measurable A.G J.1 J.2) (Finset.measurableSet_biUnion _ fun J _ =>
      dyadicGridCell_measurable A.G J.1 J.2) ?_ subset_rfl _ ?_ Wg
    · intro y hy
      simp only [Set.mem_iUnion] at hy ⊢
      obtain ⟨J, hJ, hyJ⟩ := hy
      obtain ⟨-, -, I, hI, hIq, rfl⟩ := hcellt q J hJ
      refine ⟨ancAt A.G I db, Finset.mem_image_of_mem _ hI, ?_⟩
      have hd : dt q ≤ I.1 := by rw [← hIq]; exact hIdep I hI
      exact ancAt_mono A.G I ((hbr q).trans (hdrt q)) hd hyJ
    · refine union_commute A.G _ (d := db) (fun J hJ => ?_) _ fun J hJ => hcommT q n J ?_ ?_
      · obtain ⟨I, -, rfl⟩ := Finset.mem_image.mp hJ; rfl
      · obtain ⟨I, -, rfl⟩ := Finset.mem_image.mp hJ; exact hbr q
      · obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hJ
        exact ((hbr _).trans ((hdrt _).trans (hIdep I hI))).trans (hN I hI)
  -- the inner expansion of the left values
  set! Y : ℕ → ℕ → ColumnL2 V := fun q k' => if (q * 2 ^ ((k : ℕ) + 1)).testBit k' then
    Zg (A.R.1 + ((K * β + (posInt (q * 2 ^ ((k : ℕ) + 1)) k').2 : ℕ) : ℤ)) -
      Zg (A.R.1 + ((K * β + (posInt (q * 2 ^ ((k : ℕ) + 1)) k').1 : ℕ) : ℤ)) else 0
  have hY : ∀ q ∈ Qs, Zg (dr q) - Zg db = ∑ k' ∈ Finset.range N, Y q k' := by
    intro q hq
    have hlt : q * 2 ^ ((k : ℕ) + 1) < 2 ^ N :=
      lt_of_lt_of_le (lt_of_le_of_lt (Nat.le_add_right _ _) (hQs q hq)) hKN
    have h := prefix_telescope (fun n => Zg (A.R.1 + ((K * β + n : ℕ) : ℤ))) 0
      (q * 2 ^ ((k : ℕ) + 1)) N hlt
    simp only [zero_add, add_zero] at h
    simp only [dr, db, Y]
    rw [h]
    abel
  expose_names
  exact @bandStack_block_stage_1 κ' c₀ A V inst Zg K N k hk β Ug off hoff P Ah Cj hCj hJ Wg Sa hQs
    hSa hIdep hdrt hcellt hcomm' hJ' hbes' hcommT hN hW hY

open Classical in
/-- Blueprint lines 2408-2423 (`eq:stack-energy` for the banded transferred side, one level
`k < N`): for a family `Z_g` of variation capacity `B`, a side `S = Z_h - Z_b + W` in each block,
and pad families `A_n` (`n ≤ P + 1`) with Bessel bands, local at their depths and with fixed-input
jumps bounded by `C_j`, the glued position stacks of the bands `(A_{p+1} - A_p) S` over the uses of
all groups and blocks have total square at most
`2 B + 16 (P + 2) C_j E_W + 16 (P + 2) N C_j (N B)`, with `E_W` the energy of the block inputs
`W` restricted to the block-start ancestors of the uses. -/
theorem bandStack_energy (hanc : A.AncClosed) {γ : Type*} {V : Type*} [Fintype V]
    (Gs : Finset γ) (Z : γ → ℤ → ColumnL2 V) (ok : γ → ℤ × ℤ → Prop) {B : ℝ}
    (hcap : A.VarCap Gs Z ok B) {K N : ℕ} (hKN : K ≤ 2 ^ N) (k : Fin (N + 1)) (hk : (k : ℕ) ≠ N)
    (Bs : Finset ℕ) (U : γ → ℕ → Finset (ℤ × ℤ)) (off : ℤ × ℤ → ℕ)
    (hoff : ∀ (J : ℤ × ℤ) (β m : ℕ), m < K → J.1 = A.R.1 + ((K * β + m : ℕ) : ℤ) → off J = m)
    (hU : ∀ g β, ∀ I ∈ U g β, I ∈ A.cells ∧ I.1 = A.R.1 + (K * β + off I : ℕ) ∧ off I < K)
    (hok : ∀ g ∈ Gs, ∀ β, ∀ I ∈ U g β, ∀ J ∈ A.cells,
      dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G J.1 J.2 → ok g J)
    {P : ℕ} (Ah : γ → ℕ → ℤ → ColumnL2 V →L[ℂ] ColumnL2 V)
    (hbes : ∀ g h y, ∑ p ∈ Finset.range (P + 1), ‖(Ah g (p + 1) h - Ah g p h) y‖ ^ 2 ≤ ‖y‖ ^ 2)
    (hcomm : ∀ g n h (J : ℤ × ℤ), J.1 ≤ h → J.1 ≤ A.R.1 + A.treeDepth →
      (columnL2Restriction (dyadicGridCell A.G J.1 J.2)
      (dyadicGridCell_measurable A.G J.1 J.2)).comp (Ah g n h) =
        (Ah g n h).comp (columnL2Restriction (dyadicGridCell A.G J.1 J.2)
          (dyadicGridCell_measurable A.G J.1 J.2)))
    {Cj : ℝ} (hCj : 0 ≤ Cj)
    (hJ : ∀ g ∈ Gs, ∀ n, ∀ {ι : Type} [Fintype ι] (r t : ι → ℕ), (∀ i, r i ≤ t i) →
      (∀ i i', i ≠ i' → Disjoint (Finset.Ioc (r i) (t i)) (Finset.Ioc (r i') (t i'))) →
      ∀ Ec : ι → Finset (ℤ × ℤ), (∀ i, ∀ J ∈ Ec i, J ∈ A.cells) → ∀ x,
      ∑ i, ‖columnL2Restriction (⋃ J ∈ Ec i, dyadicGridCell A.G J.1 J.2)
        (Finset.measurableSet_biUnion _ fun J _ => dyadicGridCell_measurable A.G J.1 J.2)
        ((Ah g n (A.R.1 + t i) - Ah g n (A.R.1 + r i)) x)‖ ^ 2 ≤ Cj * ‖x‖ ^ 2)
    (W : γ → ℕ → ColumnL2 V) {EW : ℝ}
    (hEW : ∑ g ∈ Gs, ∑ β ∈ Bs, ‖columnL2Restriction
      (⋃ J ∈ ((U g β).filter fun I => posAct N k (off I)).image
        (fun I => ancAt A.G I (A.R.1 + ((K * β : ℕ) : ℤ))), dyadicGridCell A.G J.1 J.2)
      (Finset.measurableSet_biUnion _ fun J _ => dyadicGridCell_measurable A.G J.1 J.2)
      (W g β)‖ ^ 2 ≤ EW)
    (Sa : γ → ℕ → ℤ → ColumnL2 V)
    (hSa : ∀ g β h, Sa g β h = Z g h - Z g (A.R.1 + ((K * β : ℕ) : ℤ)) + W g β) :
    ∑ g ∈ Gs, ∑ β ∈ Bs, ∑ q ∈ ((U g β).filter fun I => posAct N k (off I)).image
        (fun I => off I / 2 ^ ((k : ℕ) + 1)), ∑ p ∈ Finset.range (P + 1),
      ‖gluedStack A.G ((U g β).filter fun I => posAct N k (off I))
        (fun I => off I / 2 ^ ((k : ℕ) + 1))
        (fun q => posVal (fun n => (Ah g (p + 1) (A.R.1 + (K * β + n : ℕ)) -
          Ah g p (A.R.1 + (K * β + n : ℕ))) (Sa g β (A.R.1 + (K * β + n : ℕ)))) N k q) q‖ ^ 2 ≤
      2 * B + 16 * (P + 2) * (Cj * EW) + 16 * (P + 2) * (N * (Cj * (N * B))) := by
  -- block bounds
  have hblk : ∀ g ∈ Gs, ∀ β ∈ Bs, _ := fun g hg β _ =>
    A.bandStack_block hanc (Z g) hKN k hk β (U g β) off (fun J m hm hJ => hoff J β m hm hJ)
      (hU g β) (Ah g) (hbes g) (hcomm g) hCj (hJ g hg) (W g β) (Sa g β) (hSa g β)
  refine (Finset.sum_le_sum fun g hg => Finset.sum_le_sum fun β hβ => hblk g hg β hβ).trans ?_
  -- the position jumps
  have h1 := A.posAnc_energy hanc Gs Z ok hcap k hk Bs U off hU hok
  -- the inner jumps
  have h3 : ∀ k' : Fin N, ∑ g ∈ Gs, ∑ β ∈ Bs,
      ∑ q' ∈ ((A.posLeft ((U g β).filter fun I => posAct N k (off I)) off k (K * β)).filter
          fun J => posAct N (Fin.castSucc k') (off J)).image
        (fun J => off J / 2 ^ ((k' : ℕ) + 1)),
      ‖columnL2Restriction (⋃ J ∈ A.posEc ((A.posLeft ((U g β).filter fun I => posAct N k (off I))
          off k (K * β)).filter fun J => posAct N (Fin.castSucc k') (off J)) off k' (K * β) q',
          dyadicGridCell A.G J.1 J.2)
        (Finset.measurableSet_biUnion _ fun J _ => dyadicGridCell_measurable A.G J.1 J.2)
        (Z g (A.R.1 + ((K * β + (q' * 2 ^ ((k' : ℕ) + 1) + 2 ^ (k' : ℕ))) : ℕ)) -
          Z g (A.R.1 + ((K * β + q' * 2 ^ ((k' : ℕ) + 1)) : ℕ)))‖ ^ 2 ≤ B := by
    intro k'
    have hk' : ((Fin.castSucc k' : Fin (N + 1)) : ℕ) ≠ N := by
      simp only [Fin.val_castSucc]; exact k'.2.ne
    refine A.posAnc_energy hanc Gs Z ok hcap (Fin.castSucc k') hk' Bs
      (fun g β => A.posLeft ((U g β).filter fun I => posAct N k (off I)) off k (K * β)) off
      ?_ ?_
    · intro g β J hJ
      obtain ⟨I, hIf, rfl⟩ := Finset.mem_image.mp hJ
      have hIU := (Finset.mem_filter.mp hIf).1
      obtain ⟨hIc, hIdep, hIK⟩ := hU g β I hIU
      have hm : off I / 2 ^ ((k : ℕ) + 1) * 2 ^ ((k : ℕ) + 1) ≤ off I := Nat.div_mul_le_self _ _
      have hd : A.R.1 + ((K * β + off I / 2 ^ ((k : ℕ) + 1) * 2 ^ ((k : ℕ) + 1) : ℕ) : ℤ) ≤
          I.1 := by
        rw [hIdep]; push_cast
        have : ((off I / 2 ^ ((k : ℕ) + 1) * 2 ^ ((k : ℕ) + 1) : ℕ) : ℤ) ≤ (off I : ℤ) := by
          exact_mod_cast hm
        push_cast at this
        linarith
      have hR1 : A.R.1 ≤
          A.R.1 + ((K * β + off I / 2 ^ ((k : ℕ) + 1) * 2 ^ ((k : ℕ) + 1) : ℕ) : ℤ) := by
        have := Nat.cast_nonneg (α := ℤ) (K * β + off I / 2 ^ ((k : ℕ) + 1) * 2 ^ ((k : ℕ) + 1))
        linarith
      have hoffJ := hoff (ancAt A.G I (A.R.1 + ((K * β + off I / 2 ^ ((k : ℕ) + 1) *
        2 ^ ((k : ℕ) + 1) : ℕ) : ℤ))) β _ (lt_of_le_of_lt hm hIK) rfl
      refine ⟨hanc I hIc _ (subset_ancAt A.G I hd) (ancAt_subset (A.sub I hIc) hR1), ?_, ?_⟩
      · rw [hoffJ]; rfl
      · rw [hoffJ]; exact lt_of_le_of_lt hm hIK
    · intro g hg β J hJ J' hJ'c hJJ'
      obtain ⟨I, hIf, rfl⟩ := Finset.mem_image.mp hJ
      have hIU := (Finset.mem_filter.mp hIf).1
      obtain ⟨hIc, hIdep, hIK⟩ := hU g β I hIU
      have hm : off I / 2 ^ ((k : ℕ) + 1) * 2 ^ ((k : ℕ) + 1) ≤ off I := Nat.div_mul_le_self _ _
      have hd : A.R.1 + ((K * β + off I / 2 ^ ((k : ℕ) + 1) * 2 ^ ((k : ℕ) + 1) : ℕ) : ℤ) ≤
          I.1 := by
        rw [hIdep]; push_cast
        have : ((off I / 2 ^ ((k : ℕ) + 1) * 2 ^ ((k : ℕ) + 1) : ℕ) : ℤ) ≤ (off I : ℤ) := by
          exact_mod_cast hm
        push_cast at this
        linarith
      exact hok g hg β I hIU J' hJ'c ((subset_ancAt A.G I hd).trans hJJ')
  have hS3 : ∑ g ∈ Gs, ∑ β ∈ Bs, ∑ k' : Fin N,
      ∑ q' ∈ ((A.posLeft ((U g β).filter fun I => posAct N k (off I)) off k (K * β)).filter
          fun J => posAct N (Fin.castSucc k') (off J)).image
        (fun J => off J / 2 ^ ((k' : ℕ) + 1)),
      ‖columnL2Restriction (⋃ J ∈ A.posEc ((A.posLeft ((U g β).filter fun I => posAct N k (off I))
          off k (K * β)).filter fun J => posAct N (Fin.castSucc k') (off J)) off k' (K * β) q',
          dyadicGridCell A.G J.1 J.2)
        (Finset.measurableSet_biUnion _ fun J _ => dyadicGridCell_measurable A.G J.1 J.2)
        (Z g (A.R.1 + ((K * β + (q' * 2 ^ ((k' : ℕ) + 1) + 2 ^ (k' : ℕ))) : ℕ)) -
          Z g (A.R.1 + ((K * β + q' * 2 ^ ((k' : ℕ) + 1)) : ℕ)))‖ ^ 2 ≤ N * B := by
    have swap : ∀ f : γ → ℕ → Fin N → ℝ, ∑ g ∈ Gs, ∑ β ∈ Bs, ∑ k', f g β k' =
        ∑ k', ∑ g ∈ Gs, ∑ β ∈ Bs, f g β k' := fun f =>
      (Finset.sum_congr rfl fun g _ => Finset.sum_comm).trans Finset.sum_comm
    rw [swap]
    calc _ ≤ ∑ _k' : Fin N, B := Finset.sum_le_sum fun k' _ => h3 k'
      _ = N * B := by simp
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  gcongr

open Classical in
/-- Blueprint lines 2408-2409 and 2420 (the base terms of `eq:stack-energy`): the glued base
stacks (level `N`) of the bands `(A_{p+1} - A_p) S` at the block starts, where `S_b = W`, have
total square at most the energy `E_W` of the block inputs restricted to the block-start ancestors
of the uses (Bessel bands, local pads). -/
theorem baseStack_energy {γ : Type*} {V : Type*} [Fintype V] (Gs : Finset γ) {K N : ℕ}
    (hKN : K ≤ 2 ^ N) (Bs : Finset ℕ) (U : γ → ℕ → Finset (ℤ × ℤ)) (off : ℤ × ℤ → ℕ)
    (hU : ∀ g β, ∀ I ∈ U g β, I ∈ A.cells ∧ I.1 = A.R.1 + (K * β + off I : ℕ) ∧ off I < K)
    {P : ℕ} (Ah : γ → ℕ → ℤ → ColumnL2 V →L[ℂ] ColumnL2 V)
    (hbes : ∀ g h y, ∑ p ∈ Finset.range (P + 1), ‖(Ah g (p + 1) h - Ah g p h) y‖ ^ 2 ≤ ‖y‖ ^ 2)
    (hcomm : ∀ g n h (J : ℤ × ℤ), J.1 ≤ h → J.1 ≤ A.R.1 + A.treeDepth →
      (columnL2Restriction (dyadicGridCell A.G J.1 J.2)
      (dyadicGridCell_measurable A.G J.1 J.2)).comp (Ah g n h) =
        (Ah g n h).comp (columnL2Restriction (dyadicGridCell A.G J.1 J.2)
          (dyadicGridCell_measurable A.G J.1 J.2)))
    (W : γ → ℕ → ColumnL2 V) {EW : ℝ}
    (hEW : ∑ g ∈ Gs, ∑ β ∈ Bs, ‖columnL2Restriction
      (⋃ J ∈ (U g β).image (fun I => ancAt A.G I (A.R.1 + ((K * β : ℕ) : ℤ))),
        dyadicGridCell A.G J.1 J.2)
      (Finset.measurableSet_biUnion _ fun J _ => dyadicGridCell_measurable A.G J.1 J.2)
      (W g β)‖ ^ 2 ≤ EW)
    (Sa : γ → ℕ → ℤ → ColumnL2 V) (hSa : ∀ g β, Sa g β (A.R.1 + ((K * β : ℕ) : ℤ)) = W g β) :
    ∑ g ∈ Gs, ∑ β ∈ Bs, ∑ q ∈ ((U g β).filter fun I => posAct N (Fin.last N) (off I)).image
        (fun I => off I / 2 ^ (N + 1)), ∑ p ∈ Finset.range (P + 1),
      ‖gluedStack A.G ((U g β).filter fun I => posAct N (Fin.last N) (off I))
        (fun I => off I / 2 ^ (N + 1))
        (fun q => posVal (fun n => (Ah g (p + 1) (A.R.1 + (K * β + n : ℕ)) -
          Ah g p (A.R.1 + (K * β + n : ℕ))) (Sa g β (A.R.1 + (K * β + n : ℕ))))
          N (Fin.last N) q) q‖ ^ 2 ≤ EW := by
  refine le_trans (Finset.sum_le_sum fun g _ => Finset.sum_le_sum fun β _ => ?_) hEW
  set U' := (U g β).filter fun I => posAct N (Fin.last N) (off I)
  set db : ℤ := A.R.1 + ((K * β : ℕ) : ℤ)
  set! Ωb := ⋃ J ∈ (U g β).image (fun I => ancAt A.G I db), dyadicGridCell A.G J.1 J.2
  have hΩb : MeasurableSet Ωb :=
    Finset.measurableSet_biUnion _ fun J _ => dyadicGridCell_measurable A.G J.1 J.2
  -- every use selects the index zero
  have hsel0 : ∀ I ∈ U', off I / 2 ^ (N + 1) = 0 := by
    intro I hI
    have h := (hU g β I (Finset.mem_filter.mp hI).1).2.2
    refine Nat.div_eq_of_lt (lt_of_lt_of_le h (hKN.trans ?_))
    exact Nat.pow_le_pow_right (by norm_num) (Nat.le_succ N)
  have himg : U'.image (fun I => off I / 2 ^ (N + 1)) ⊆ {0} := by
    intro q hq
    obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hq
    rw [hsel0 I hI]; exact Finset.mem_singleton_self 0
  have hsub : ∀ q, selUnion A.G U' (fun I => off I / 2 ^ (N + 1)) q ⊆ Ωb := by
    intro q y hy
    simp only [selUnion, Set.mem_iUnion] at hy
    obtain ⟨I, hI, -, hyI⟩ := hy
    obtain ⟨hIc, hIdep, -⟩ := hU g β I (Finset.mem_filter.mp hI).1
    have hd : db ≤ I.1 := by rw [hIdep]; simp only [db]; push_cast; omega
    exact Set.mem_biUnion (Finset.mem_image_of_mem _ (Finset.mem_filter.mp hI).1)
      (subset_ancAt A.G I hd hyI)
  have hcommΩ : ∀ n, (columnL2Restriction Ωb hΩb).comp (Ah g n db) =
      (Ah g n db).comp (columnL2Restriction Ωb hΩb) := fun n =>
    union_commute A.G _ (d := db) (fun J hJ => by
      obtain ⟨I, -, rfl⟩ := Finset.mem_image.mp hJ; rfl) _ fun J hJ => by
      obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hJ
      obtain ⟨hIc, hIdep, -⟩ := hU g β I hI
      have hd : db ≤ I.1 := by rw [hIdep]; simp only [db]; push_cast; omega
      exact hcomm g n db _ le_rfl (hd.trans ((dyadicFiniteTree_mem_iff A.G A.R I
        A.treeDepth).mp (A.cells_mem_tree hIc)).2)
  have hterm : ∀ q, ∑ p ∈ Finset.range (P + 1),
      ‖gluedStack A.G U' (fun I => off I / 2 ^ (N + 1))
        (fun q => posVal (fun n => (Ah g (p + 1) (A.R.1 + (K * β + n : ℕ)) -
          Ah g p (A.R.1 + (K * β + n : ℕ))) (Sa g β (A.R.1 + (K * β + n : ℕ))))
          N (Fin.last N) q) q‖ ^ 2 ≤ ‖columnL2Restriction Ωb hΩb (W g β)‖ ^ 2 := by
    intro q
    refine (Finset.sum_le_sum fun p _ =>
      gluedStack_norm_sq_le A.G U' _ _ q hΩb (hsub q)).trans ?_
    have e : ∀ p, posVal (fun n => (Ah g (p + 1) (A.R.1 + (K * β + n : ℕ)) -
        Ah g p (A.R.1 + (K * β + n : ℕ))) (Sa g β (A.R.1 + (K * β + n : ℕ))))
          N (Fin.last N) q =
        (Ah g (p + 1) db - Ah g p db) (W g β) := by
      intro p
      simp only [posVal, Fin.val_last, ite_true, add_zero]
      rw [hSa]
    simp only [e]
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun p _ => ?_)) (hbes g db _)
    rw [sub_apply, map_sub, ← ContinuousLinearMap.comp_apply, hcommΩ,
      ContinuousLinearMap.comp_apply,
      ← ContinuousLinearMap.comp_apply (columnL2Restriction Ωb hΩb), hcommΩ,
      ContinuousLinearMap.comp_apply, ← sub_apply]
  calc _ ≤ ∑ q ∈ ({0} : Finset ℕ), ∑ p ∈ Finset.range (P + 1),
        ‖gluedStack A.G U' (fun I => off I / 2 ^ (N + 1))
          (fun q => posVal (fun n => (Ah g (p + 1) (A.R.1 + (K * β + n : ℕ)) -
            Ah g p (A.R.1 + (K * β + n : ℕ))) (Sa g β (A.R.1 + (K * β + n : ℕ))))
            N (Fin.last N) q) q‖ ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg himg fun _ _ _ =>
          Finset.sum_nonneg fun _ _ => by positivity
    _ ≤ _ := by rw [Finset.sum_singleton]; exact hterm 0

end ActiveSetup

section DepthStacks
variable (G : RealDyadicGrid) {V : Type*} [Fintype V]

/-! ### Depth stacks of a basic `U` side (blueprint lines 2407-2408) -/

open Classical in
/-- Blueprint line 2407 ("for a basic `U` side use each depth directly as a position"): the
depth stack of local values `v_I` on the cells of `U` of selection `m`: the sum of their
restrictions to the cells. -/
noncomputable def depthStack (U : Finset (ℤ × ℤ)) (sel : ℤ × ℤ → ℕ) (v : ℤ × ℤ → ColumnL2 V)
    (m : ℕ) : ColumnL2 V :=
  ∑ J ∈ U.filter (fun J => sel J = m), columnL2Restriction (dyadicGridCell G J.1 J.2)
    (dyadicGridCell_measurable G J.1 J.2) (v J)

end DepthStacks

section HelpPreAppend
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem helpPre_append (P : ℕ) :
    ∀ (l : List (TransferStep E)) (st : TransferStep E) (x : E),
      helpPre P (l ++ [st]) x = filterAvg P st.2.1 (helpPre P l x)
  | [], st, x => rfl
  | a :: l, st, x => by
    simp only [List.cons_append, helpPre]
    exact helpPre_append P l st _

end HelpPreAppend

namespace ActiveSetup

namespace AttemptParams

namespace LeafSplit
variable {κ' : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ' c₀} {ap : A.AttemptParams}
  (D : ap.LeafSplit)

/-! ### Global sides of a leaf (blueprint lines 2161-2162, 2414-2420) -/

end LeafSplit

end AttemptParams

end ActiveSetup

/-- In four slots, a slot distinct from three of four distinct slots is the fourth. -/
theorem fin4_last : ∀ a b c d l : Fin 4, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
    l ≠ a → l ≠ c → l ≠ d → l = b := by
  intro a b c d l h1 h2 h3 h4 h5 h6 h7 h8 h9
  omega

namespace ActiveSetup
variable {κ' : LocalKernelClass} {c₀ : ℕ} (A : ActiveSetup κ' c₀)

open Classical in
/-- Blueprint `eq:stack-energy` for the banded side of one transfer step over all levels: the
`bandStack_energy` of the levels `k < N` plus the `baseStack_energy` of the base level. -/
theorem bandStack_all (hanc : A.AncClosed) {γ : Type*} {V : Type*} [Fintype V]
    (Gs : Finset γ) (Z : γ → ℤ → ColumnL2 V) (ok : γ → ℤ × ℤ → Prop) {B : ℝ}
    (hcap : A.VarCap Gs Z ok B) {K N : ℕ} (hKN : K ≤ 2 ^ N)
    (Bs : Finset ℕ) (U : γ → ℕ → Finset (ℤ × ℤ)) (off : ℤ × ℤ → ℕ)
    (hoff : ∀ (J : ℤ × ℤ) (β m : ℕ), m < K → J.1 = A.R.1 + ((K * β + m : ℕ) : ℤ) → off J = m)
    (hU : ∀ g β, ∀ I ∈ U g β, I ∈ A.cells ∧ I.1 = A.R.1 + (K * β + off I : ℕ) ∧ off I < K)
    (hok : ∀ g ∈ Gs, ∀ β, ∀ I ∈ U g β, ∀ J ∈ A.cells,
      dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G J.1 J.2 → ok g J)
    {P : ℕ} (Ah : γ → ℕ → ℤ → ColumnL2 V →L[ℂ] ColumnL2 V)
    (hbes : ∀ g h y, ∑ p ∈ Finset.range (P + 1), ‖(Ah g (p + 1) h - Ah g p h) y‖ ^ 2 ≤ ‖y‖ ^ 2)
    (hcomm : ∀ g n h (J : ℤ × ℤ), J.1 ≤ h → J.1 ≤ A.R.1 + A.treeDepth →
      (columnL2Restriction (dyadicGridCell A.G J.1 J.2)
        (dyadicGridCell_measurable A.G J.1 J.2)).comp (Ah g n h) =
        (Ah g n h).comp (columnL2Restriction (dyadicGridCell A.G J.1 J.2)
          (dyadicGridCell_measurable A.G J.1 J.2)))
    {Cj : ℝ} (hCj : 0 ≤ Cj)
    (hJ : ∀ g ∈ Gs, ∀ n, ∀ {ι : Type} [Fintype ι] (r t : ι → ℕ), (∀ i, r i ≤ t i) →
      (∀ i i', i ≠ i' → Disjoint (Finset.Ioc (r i) (t i)) (Finset.Ioc (r i') (t i'))) →
      ∀ Ec : ι → Finset (ℤ × ℤ), (∀ i, ∀ J ∈ Ec i, J ∈ A.cells) → ∀ x,
      ∑ i, ‖columnL2Restriction (⋃ J ∈ Ec i, dyadicGridCell A.G J.1 J.2)
        (Finset.measurableSet_biUnion _ fun J _ => dyadicGridCell_measurable A.G J.1 J.2)
        ((Ah g n (A.R.1 + t i) - Ah g n (A.R.1 + r i)) x)‖ ^ 2 ≤ Cj * ‖x‖ ^ 2)
    (W : γ → ℕ → ColumnL2 V) {EW : ℝ}
    (hEW : ∑ g ∈ Gs, ∑ β ∈ Bs, ‖columnL2Restriction
      (⋃ J ∈ (U g β).image (fun I => ancAt A.G I (A.R.1 + ((K * β : ℕ) : ℤ))),
        dyadicGridCell A.G J.1 J.2)
      (Finset.measurableSet_biUnion _ fun J _ => dyadicGridCell_measurable A.G J.1 J.2)
      (W g β)‖ ^ 2 ≤ EW)
    (Sa : γ → ℕ → ℤ → ColumnL2 V)
    (hSa : ∀ g β h, Sa g β h = Z g h - Z g (A.R.1 + ((K * β : ℕ) : ℤ)) + W g β) :
    ∑ k : Fin (N + 1), ∑ g ∈ Gs, ∑ β ∈ Bs, ∑ q ∈ ((U g β).filter fun I => posAct N k (off I)).image
        (fun I => off I / 2 ^ ((k : ℕ) + 1)), ∑ p ∈ Finset.range (P + 1),
      ‖gluedStack A.G ((U g β).filter fun I => posAct N k (off I))
        (fun I => off I / 2 ^ ((k : ℕ) + 1))
        (fun q => posVal (fun n => (Ah g (p + 1) (A.R.1 + (K * β + n : ℕ)) -
          Ah g p (A.R.1 + (K * β + n : ℕ))) (Sa g β (A.R.1 + (K * β + n : ℕ)))) N k q) q‖ ^ 2 ≤
      N * (2 * B + 16 * (P + 2) * (Cj * EW) + 16 * (P + 2) * (N * (Cj * (N * B)))) + EW := by
  have hEWk : ∀ k : Fin (N + 1), ∑ g ∈ Gs, ∑ β ∈ Bs, ‖columnL2Restriction
      (⋃ J ∈ ((U g β).filter fun I => posAct N k (off I)).image
        (fun I => ancAt A.G I (A.R.1 + ((K * β : ℕ) : ℤ))), dyadicGridCell A.G J.1 J.2)
      (Finset.measurableSet_biUnion _ fun J _ => dyadicGridCell_measurable A.G J.1 J.2)
      (W g β)‖ ^ 2 ≤ EW := by
    intro k
    refine le_trans (Finset.sum_le_sum fun g _ => Finset.sum_le_sum fun β _ => ?_) hEW
    refine columnL2Restriction_norm_sq_mono _ _ ?_ _
    exact Set.biUnion_subset_biUnion_left (Finset.coe_subset.mpr
      (Finset.image_subset_image (Finset.filter_subset _ _)))
  rw [Fin.sum_univ_castSucc]
  refine add_le_add ?_ ?_
  · calc ∑ k : Fin N, _ ≤ ∑ _k : Fin N, (2 * B + 16 * (P + 2) * (Cj * EW) +
          16 * (P + 2) * (N * (Cj * (N * B)))) := by
          refine Finset.sum_le_sum fun k _ => ?_
          have hk : ((Fin.castSucc k : Fin (N + 1)) : ℕ) ≠ N := by
            simp only [Fin.val_castSucc]; exact k.2.ne
          exact A.bandStack_energy hanc Gs Z ok hcap hKN (Fin.castSucc k) hk Bs U off hoff hU hok
            Ah hbes hcomm hCj hJ W (hEWk _) Sa hSa
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  · exact A.baseStack_energy Gs hKN Bs U off hU Ah hbes hcomm W hEW Sa
      (fun g β => by rw [hSa]; abel)

open Classical in
/-- Blueprint `eq:stack-energy` for the untouched side over all levels: the position levels by
`posStack_energy` and the base level by the block-start energy. -/
theorem posStack_all (hanc : A.AncClosed) {γ : Type*} {V : Type*} [Fintype V]
    (Gs : Finset γ) (Z : γ → ℤ → ColumnL2 V) (ok : γ → ℤ × ℤ → Prop) {B : ℝ}
    (hcap : A.VarCap Gs Z ok B) {K N : ℕ} (hKN : K ≤ 2 ^ N)
    (Bs : Finset ℕ) (U : γ → ℕ → Finset (ℤ × ℤ)) (off : ℤ × ℤ → ℕ)
    (hU : ∀ g β, ∀ I ∈ U g β, I ∈ A.cells ∧ I.1 = A.R.1 + (K * β + off I : ℕ) ∧ off I < K)
    (hok : ∀ g ∈ Gs, ∀ β, ∀ I ∈ U g β, ∀ J ∈ A.cells,
      dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G J.1 J.2 → ok g J)
    (Sb : γ → ℕ → ℤ → ColumnL2 V)
    (hSb : ∀ g β h h', Sb g β h - Sb g β h' = Z g h - Z g h') {EW : ℝ}
    (hEW : ∑ g ∈ Gs, ∑ β ∈ Bs, ‖columnL2Restriction
      (⋃ J ∈ (U g β).image (fun I => ancAt A.G I (A.R.1 + ((K * β : ℕ) : ℤ))),
        dyadicGridCell A.G J.1 J.2)
      (Finset.measurableSet_biUnion _ fun J _ => dyadicGridCell_measurable A.G J.1 J.2)
      (Sb g β (A.R.1 + ((K * β : ℕ) : ℤ)))‖ ^ 2 ≤ EW) :
    ∑ k : Fin (N + 1), ∑ g ∈ Gs, ∑ β ∈ Bs, ∑ q ∈ ((U g β).filter fun I => posAct N k (off I)).image
        (fun I => off I / 2 ^ ((k : ℕ) + 1)),
      ‖gluedStack A.G ((U g β).filter fun I => posAct N k (off I))
        (fun I => off I / 2 ^ ((k : ℕ) + 1))
        (fun q => posVal (fun n => Sb g β (A.R.1 + (K * β + n : ℕ))) N k q) q‖ ^ 2 ≤
      N * B + EW := by
  rw [Fin.sum_univ_castSucc]
  refine add_le_add ?_ ?_
  · calc ∑ k : Fin N, _ ≤ ∑ _k : Fin N, B := by
          refine Finset.sum_le_sum fun k _ => ?_
          have hk : ((Fin.castSucc k : Fin (N + 1)) : ℕ) ≠ N := by
            simp only [Fin.val_castSucc]; exact k.2.ne
          exact A.posStack_energy hanc Gs Z ok hcap (Fin.castSucc k) hk Bs U off hU hok Sb hSb
      _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  · refine le_trans (Finset.sum_le_sum fun g _ => Finset.sum_le_sum fun β _ => ?_) hEW
    set U' := (U g β).filter fun I => posAct N (Fin.last N) (off I)
    set db : ℤ := A.R.1 + ((K * β : ℕ) : ℤ)
    have hsel0 : ∀ I ∈ U', off I / 2 ^ (N + 1) = 0 := by
      intro I hI
      have h := (hU g β I (Finset.mem_filter.mp hI).1).2.2
      refine Nat.div_eq_of_lt (lt_of_lt_of_le h (hKN.trans ?_))
      exact Nat.pow_le_pow_right (by norm_num) (Nat.le_succ N)
    have himg : U'.image (fun I => off I / 2 ^ (N + 1)) ⊆ {0} := by
      intro q hq
      obtain ⟨I, hI, rfl⟩ := Finset.mem_image.mp hq
      rw [hsel0 I hI]; exact Finset.mem_singleton_self 0
    refine (Finset.sum_le_sum_of_subset_of_nonneg himg fun _ _ _ => by positivity).trans ?_
    rw [Finset.sum_singleton]
    refine (gluedStack_norm_sq_le A.G U' _ _ 0 (Finset.measurableSet_biUnion
      ((U g β).image fun I => ancAt A.G I db) fun J _ =>
        dyadicGridCell_measurable A.G J.1 J.2) ?_).trans (le_of_eq ?_)
    · intro y hy
      simp only [selUnion, Set.mem_iUnion] at hy
      obtain ⟨I, hI, -, hyI⟩ := hy
      obtain ⟨hIc, hIdep, -⟩ := hU g β I (Finset.mem_filter.mp hI).1
      have hd : db ≤ I.1 := by rw [hIdep]; simp only [db]; push_cast; omega
      exact Set.mem_biUnion (Finset.mem_image_of_mem _ (Finset.mem_filter.mp hI).1)
        (subset_ancAt A.G I hd hyI)
    · simp only [posVal, Fin.val_last, ite_true, add_zero]
      rfl

end ActiveSetup

open Classical in
/-- Integrating a pointwise path cap: if the path sums of `f` are at most `T` everywhere, the
length-weighted sum of `f` over cells inside a root is at most `T` times the root length. -/
theorem path_cap_integral (Gd : RealDyadicGrid) (S : Finset (ℤ × ℤ)) (root : ℤ × ℤ)
    (hroot : ∀ I ∈ S, dyadicGridCell Gd I.1 I.2 ⊆ dyadicGridCell Gd root.1 root.2)
    (f : ℤ × ℤ → ℝ) {T : ℝ}
    (hT : ∀ x, ∑ I ∈ S.filter (fun I => x ∈ dyadicGridCell Gd I.1 I.2), f I ≤ T) :
    ∑ I ∈ S, dyadicGridLength Gd I.1 * f I ≤ T * dyadicGridLength Gd root.1 := by
  classical
  set g : ℝ → ℝ := fun x => ∑ I ∈ S, (dyadicGridCell Gd I.1 I.2).indicator (fun _ => f I) x
  rw [dyadicPathIntegral_real Gd S _ (dyadicGridCell Gd root.1 root.2) hroot]
  have hpt : ∀ x, g x ≤ T := by
    intro x
    have hgx : g x = ∑ I ∈ S.filter (fun I => x ∈ dyadicGridCell Gd I.1 I.2), f I := by
      simp only [g, Finset.sum_filter, Set.indicator_apply]
    rw [hgx]
    exact hT x
  have hint : IntegrableOn g (dyadicGridCell Gd root.1 root.2) := by
    refine integrable_finsetSum _ fun I hI => ?_
    apply (integrable_indicator_iff (dyadicGridCell_measurable Gd I.1 I.2)).mpr
    change Integrable _ ((volume.restrict _).restrict (dyadicGridCell Gd I.1 I.2))
    rw [Measure.restrict_restrict_of_subset (hroot I hI)]
    exact integrableOn_const (by rw [dyadicGridCell_volume]; exact ENNReal.ofReal_ne_top)
  calc ∫ x in dyadicGridCell Gd root.1 root.2, g x ≤
      ∫ _x in dyadicGridCell Gd root.1 root.2, T :=
        setIntegral_mono_on hint (integrableOn_const (by
          rw [dyadicGridCell_volume]; exact ENNReal.ofReal_ne_top))
          (dyadicGridCell_measurable Gd root.1 root.2) fun x _ => hpt x
    _ = _ := by
        rw [setIntegral_const, smul_eq_mul, Measure.real, dyadicGridCell_volume,
          ENNReal.toReal_ofReal (dyadicGridLength_pos Gd root.1).le]
        ring

/-- A list sum of a map as a sum over the index range with `getD`. -/
theorem list_map_sum_range {α : Type*} (L : List α) (d : α) (f : α → ℝ) :
    (L.map f).sum = ∑ i ∈ Finset.range L.length, f (L.getD i d) := by
  rw [← Fin.sum_univ_fun_getElem, ← Fin.sum_univ_eq_sum_range (fun i => f (L.getD i d))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [List.getD_eq_getElem _ _ i.2]

/-- Cauchy-Schwarz for a sum over a finset of size at most `n`. -/
theorem sq_sum_le_of_card {ι : Type*} (s : Finset ι) (f : ι → ℝ) {n : ℝ} (hs : (s.card : ℝ) ≤ n) :
    (∑ i ∈ s, f i) ^ 2 ≤ n * ∑ i ∈ s, f i ^ 2 :=
  (sq_sum_le_card_mul_sum_sq (s := s) (f := f)).trans
    (mul_le_mul_of_nonneg_right hs (Finset.sum_nonneg fun _ _ => sq_nonneg _))

/-- `(a + b)² ≤ 2 a² + 2 b²`. -/
theorem add_sq_le_two (a b : ℝ) : (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
  nlinarith only [sq_nonneg (a - b)]

/-- Cauchy-Schwarz for a double sum over ranges of sizes at most `n` and `m`. -/
theorem sq_sum2_le (s : Finset ℕ) (t : ℕ → Finset ℕ) (f : ℕ → ℕ → ℝ) {n m : ℝ}
    (hs : (s.card : ℝ) ≤ n) (ht : ∀ i, ((t i).card : ℝ) ≤ m) (hn : 0 ≤ n) :
    (∑ i ∈ s, ∑ j ∈ t i, f i j) ^ 2 ≤ n * m * ∑ i ∈ s, ∑ j ∈ t i, f i j ^ 2 := by
  calc (∑ i ∈ s, ∑ j ∈ t i, f i j) ^ 2 ≤ n * ∑ i ∈ s, (∑ j ∈ t i, f i j) ^ 2 :=
        sq_sum_le_of_card s _ hs
    _ ≤ n * ∑ i ∈ s, m * ∑ j ∈ t i, f i j ^ 2 :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => sq_sum_le_of_card _ _ (ht i)) hn
    _ = _ := by rw [← Finset.mul_sum]; ring

/-- The per-pair bound of the third strong factor:
`L (a + Σ_{j,o} y)² ≤ 2 (1 + 5 J) (A + D Σ B)`. -/
theorem pair_sq_le {L a Aa D : ℝ} (J O : Finset ℕ) (y Bt : ℕ → ℕ → ℝ) {Jm : ℕ} (hL : 0 < L)
    (hJ : J.card ≤ Jm) (hO : O.card = 5) (ha : L * a ^ 2 ≤ Aa)
    (hy : ∀ j o, L * y j o ^ 2 ≤ D * Bt j o) (hD : 0 ≤ D) (hAa : 0 ≤ Aa)
    (hBt : ∀ j o, 0 ≤ Bt j o) :
    L * (a + ∑ j ∈ J, ∑ o ∈ O, y j o) ^ 2 ≤ 2 * (1 + 5 * Jm) * (Aa + D * ∑ j ∈ J, ∑ o ∈ O, Bt j o)
        := by
  have h1 := add_sq_le_two a (∑ j ∈ J, ∑ o ∈ O, y j o)
  have hJm : (J.card : ℝ) ≤ Jm := by exact_mod_cast hJ
  have h2 := sq_sum2_le J (fun _ => O) y (n := (Jm : ℝ)) (m := 5) hJm
    (fun _ => by rw [hO]; norm_num) (Nat.cast_nonneg Jm)
  have h3 : L * ∑ j ∈ J, ∑ o ∈ O, y j o ^ 2 ≤ D * ∑ j ∈ J, ∑ o ∈ O, Bt j o := by
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_le_sum fun o _ => hy j o
  have hB : 0 ≤ D * ∑ j ∈ J, ∑ o ∈ O, Bt j o :=
    mul_nonneg hD (Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun o _ => hBt j o)
  have hJ0 : (0 : ℝ) ≤ Jm := Nat.cast_nonneg Jm
  calc L * (a + ∑ j ∈ J, ∑ o ∈ O, y j o) ^ 2
      ≤ L * (2 * a ^ 2 + 2 * (Jm * 5 * ∑ j ∈ J, ∑ o ∈ O, y j o ^ 2)) := by
        refine mul_le_mul_of_nonneg_left (h1.trans ?_) hL.le
        nlinarith
    _ = 2 * (L * a ^ 2) + 10 * Jm * (L * ∑ j ∈ J, ∑ o ∈ O, y j o ^ 2) := by ring
    _ ≤ 2 * Aa + 10 * Jm * (D * ∑ j ∈ J, ∑ o ∈ O, Bt j o) := by
        have := mul_le_mul_of_nonneg_left h3 (by positivity : (0 : ℝ) ≤ 10 * Jm)
        linarith
    _ ≤ _ := by nlinarith

/-- Assembling the per-pair bounds over the pairs of positive chains by Cauchy-Schwarz. -/
theorem pairs_sq_le {L Lp K A D : ℝ} (s : Finset ℕ) (t : ℕ → Finset ℕ) (X B : ℕ → ℕ → ℝ)
    (hL : 0 ≤ L) (hK : 0 ≤ K) (hA : 0 ≤ A) (hD : 0 ≤ D) (hLp : 0 ≤ Lp)
    (hs : (s.card : ℝ) ≤ Lp) (ht : ∀ i, ((t i).card : ℝ) ≤ Lp)
    (hX : ∀ i ∈ s, ∀ j ∈ t i, L * X i j ^ 2 ≤ K * (A + D * B i j)) (hB : ∀ i j, 0 ≤ B i j) :
    L * (∑ i ∈ s, ∑ j ∈ t i, X i j) ^ 2 ≤ Lp ^ 2 * K * (Lp ^ 2 * A + D * ∑ i ∈ s, ∑ j ∈ t i, B i j)
        := by
  have h1 := sq_sum2_le s t X hs ht hLp
  have hcnt : ∑ i ∈ s, ((t i).card : ℝ) ≤ Lp ^ 2 := by
    calc ∑ i ∈ s, ((t i).card : ℝ) ≤ ∑ _i ∈ s, Lp := Finset.sum_le_sum fun i _ => ht i
      _ = s.card * Lp := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ Lp * Lp := mul_le_mul_of_nonneg_right hs hLp
      _ = Lp ^ 2 := by ring
  have h2 : L * ∑ i ∈ s, ∑ j ∈ t i, X i j ^ 2 ≤
      K * (∑ i ∈ s, ((t i).card : ℝ) * A + D * ∑ i ∈ s, ∑ j ∈ t i, B i j) := by
    calc L * ∑ i ∈ s, ∑ j ∈ t i, X i j ^ 2 = ∑ i ∈ s, ∑ j ∈ t i, L * X i j ^ 2 := by
          simp only [Finset.mul_sum]
      _ ≤ ∑ i ∈ s, ∑ j ∈ t i, K * (A + D * B i j) :=
          Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => hX i hi j hj
      _ = K * (∑ i ∈ s, ((t i).card : ℝ) * A + D * ∑ i ∈ s, ∑ j ∈ t i, B i j) := by
          simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
  have hB0 : 0 ≤ D * ∑ i ∈ s, ∑ j ∈ t i, B i j :=
    mul_nonneg hD (Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hB i j)
  have hc : ∑ i ∈ s, ((t i).card : ℝ) * A ≤ Lp ^ 2 * A := by
    rw [← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right hcnt hA
  calc L * (∑ i ∈ s, ∑ j ∈ t i, X i j) ^ 2 ≤ L * (Lp * Lp * ∑ i ∈ s, ∑ j ∈ t i, X i j ^ 2) :=
        mul_le_mul_of_nonneg_left h1 hL
    _ = Lp ^ 2 * (L * ∑ i ∈ s, ∑ j ∈ t i, X i j ^ 2) := by ring
    _ ≤ Lp ^ 2 * (K * (∑ i ∈ s, ((t i).card : ℝ) * A + D * ∑ i ∈ s, ∑ j ∈ t i, B i j)) :=
        mul_le_mul_of_nonneg_left h2 (sq_nonneg _)
    _ ≤ Lp ^ 2 * (K * (Lp ^ 2 * A + D * ∑ i ∈ s, ∑ j ∈ t i, B i j)) := by gcongr
    _ = _ := by ring

/-- Cauchy-Schwarz over four slot indices. -/
theorem sq_sum_fin4_4 (f : Fin 4 → Fin 4 → Fin 4 → Fin 4 → ℝ) :
    (∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4, ∑ d : Fin 4, f a b c d) ^ 2 ≤
      256 * ∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4, ∑ d : Fin 4, f a b c d ^ 2 := by
  have h4 : ∀ x : Fin 4 → ℝ, (∑ a, x a) ^ 2 ≤ 4 * ∑ a, x a ^ 2 := fun x =>
    sq_sum_le_of_card Finset.univ x (by simp)
  calc (∑ a : Fin 4, ∑ b : Fin 4, ∑ c : Fin 4, ∑ d : Fin 4, f a b c d) ^ 2
      ≤ 4 * ∑ a : Fin 4, (∑ b : Fin 4, ∑ c : Fin 4, ∑ d : Fin 4, f a b c d) ^ 2 := h4 _
    _ ≤ 4 * ∑ a : Fin 4, 4 * ∑ b : Fin 4, (∑ c : Fin 4, ∑ d : Fin 4, f a b c d) ^ 2 := by
        gcongr with a; exact h4 _
    _ ≤ 4 * ∑ a : Fin 4, 4 * ∑ b : Fin 4, 4 * ∑ c : Fin 4, (∑ d : Fin 4, f a b c d) ^ 2 := by
        gcongr with a _ b; exact h4 _
    _ ≤ 4 * ∑ a : Fin 4, 4 * ∑ b : Fin 4, 4 * ∑ c : Fin 4, 4 * ∑ d : Fin 4, f a b c d ^ 2 := by
        gcongr with a _ b _ c; exact h4 _
    _ = _ := by simp only [Finset.mul_sum]; ring_nf

/-- Pairwise disjoint cells inside a cell have total length at most its length. -/
theorem disjoint_subcells_length_le (Gd : RealDyadicGrid) (C : Finset (ℤ × ℤ)) (J : ℤ × ℤ)
    (hC : Set.PairwiseDisjoint (C : Set (ℤ × ℤ)) (fun c => dyadicGridCell Gd c.1 c.2))
    (hsub : ∀ c ∈ C, dyadicGridCell Gd c.1 c.2 ⊆ dyadicGridCell Gd J.1 J.2) :
    ∑ c ∈ C, dyadicGridLength Gd c.1 ≤ dyadicGridLength Gd J.1 := by
  have h := dyadicRootLength_ofReal_eq_volume Gd C hC
  have hv : volume (⋃ c ∈ C, dyadicGridCell Gd c.1 c.2) ≤ volume (dyadicGridCell Gd J.1 J.2) :=
    measure_mono (Set.iUnion₂_subset fun c hc => hsub c hc)
  rw [← h, dyadicGridCell_volume] at hv
  exact (ENNReal.ofReal_le_ofReal_iff (dyadicGridLength_pos Gd J.1).le).mp hv

open Classical in
/-- Cells of a finite family inside a cell `J`, at depths of a window of `K` depths starting at
`J`, have total length at most `K |J|`. -/
theorem depth_window_length_le (Gd : RealDyadicGrid) (X : Finset (ℤ × ℤ)) (J : ℤ × ℤ) (K : ℕ)
    (hsub : ∀ I ∈ X, dyadicGridCell Gd I.1 I.2 ⊆ dyadicGridCell Gd J.1 J.2)
    (hdep : ∀ I ∈ X, J.1 ≤ I.1 ∧ I.1 < J.1 + K) :
    ∑ I ∈ X, dyadicGridLength Gd I.1 ≤ K * dyadicGridLength Gd J.1 := by
  rw [← Finset.sum_fiberwise_of_maps_to (g := fun I : ℤ × ℤ => (I.1 - J.1).toNat)
    (t := Finset.range K) (fun I hI => by
      have := hdep I hI
      simp only [Finset.mem_range]
      omega)]
  calc ∑ n ∈ Finset.range K, ∑ I ∈ X.filter (fun I => (I.1 - J.1).toNat = n),
        dyadicGridLength Gd I.1
      ≤ ∑ _n ∈ Finset.range K, dyadicGridLength Gd J.1 := by
        refine Finset.sum_le_sum fun n _ => disjoint_subcells_length_le Gd _ J ?_
          fun I hI => hsub I (Finset.mem_filter.mp hI).1
        intro I hI I' hI' hne
        have h1 := Finset.mem_filter.mp hI
        have h2 := Finset.mem_filter.mp hI'
        have hd : I.1 = I'.1 := by
          have := hdep I h1.1; have := hdep I' h2.1; omega
        have hne2 : I.2 ≠ I'.2 := fun h => hne (Prod.ext hd h)
        simp only [Function.onFun]
        rw [hd]
        exact dyadicGridCell_pairwiseDisjoint Gd I'.1 hne2
    _ = K * dyadicGridLength Gd J.1 := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

end TrilinearHT.Auto

end

section

namespace TrilinearHT.Auto
open MeasureTheory Metric
open scoped FourierTransform ComplexConjugate ENNReal

namespace ActiveSetup

namespace AttemptParams

namespace TTData
variable {κ' : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ' c₀} {ap : A.AttemptParams}
  (T : ap.TTData)

/-- Distinct blocks give disjoint depth intervals of a fixed offset `n < K`. -/
theorem block_ioc_disjoint {K n : ℕ} (hn : n < K) {β β' : ℕ} (hne : β ≠ β') :
    Disjoint (Finset.Ioc (K * β) (K * β + n)) (Finset.Ioc (K * β') (K * β' + n)) := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  simp only [Finset.mem_Ioc] at hx hx'
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have : K * (β + 1) ≤ K * β' := Nat.mul_le_mul_left K h
    nlinarith
  · have : K * (β' + 1) ≤ K * β := Nat.mul_le_mul_left K h
    nlinarith

end TTData

end AttemptParams

end ActiveSetup

end TrilinearHT.Auto

end

section

namespace TrilinearHT.Auto
open MeasureTheory Metric
open scoped FourierTransform ComplexConjugate ENNReal

/-! ## Global helper projections in the main column space (blueprint lines 2393-2420) -/

section ConjProj
variable {V W : Type*} [Fintype V] [Fintype W]

open scoped Classical in
/-- Relabeling a physical vector keeps it physical. -/
theorem colRelabel_physEmbed (f : V → W) {U : Type*} [Fintype U] (x : ColumnL2 U) :
    colRelabel f (physEmbed U V x) = physEmbed U W x := by
  refine Lp.ext ?_
  filter_upwards [colRelabel_coeFn f (physEmbed U V x), physEmbed_coeFn (W := V) x,
    physEmbed_coeFn (W := W) x] with y h1 h2 h3
  rw [h1, h2, h3, relabelCLM_apply]
  rw [Finset.sum_eq_single (none : Option V)]
  · simp
  · intro o _ ho
    simp [ho]
  · simp

/-- A conjugated projection by an isometric relabeling is a projection. -/
theorem isStarProjection_conj {f : V → W} (hf : Function.Injective f)
    {T : ColumnL2 V →L[ℂ] ColumnL2 V} (hT : IsStarProjection T) :
    IsStarProjection ((colRelabel f).comp (T.comp
      (ContinuousLinearMap.adjoint (colRelabel f)))) := by
  refine ⟨?_, ?_⟩
  · change _ * _ = _
    rw [ContinuousLinearMap.mul_def]
    refine ContinuousLinearMap.ext fun z => ?_
    simp only [ContinuousLinearMap.comp_apply]
    rw [colRelabel_adjoint_apply_relabel hf]
    have hTT := hT.isIdempotentElem
    change T * T = T at hTT
    rw [ContinuousLinearMap.mul_def] at hTT
    have h := DFunLike.congr_fun hTT (ContinuousLinearMap.adjoint (colRelabel f) z)
    rw [ContinuousLinearMap.comp_apply] at h
    rw [h]
  · have hTs : ContinuousLinearMap.adjoint T = T := hT.isSelfAdjoint
    change ContinuousLinearMap.adjoint _ = _
    rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
      ContinuousLinearMap.adjoint_adjoint, hTs, ContinuousLinearMap.comp_assoc]

end ConjProj

namespace ActiveSetup.BasicFamilies.FamParams
variable {κ : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ c₀} {bf : A.BasicFamilies}
  (fp : bf.FamParams)

/-- A global depth projection of the main base of the catalog `s` with an inherited mask at the
depth `h`, conjugated to the main column space by the relabeling of the relevant labels. -/
noncomputable def gProjC (s : List (CatCol bf.Vtx)) (mb : bf.MainBudget s)
    (M : InheritedColumnMask (bf.mainTree fp.Mc s mb)) (h : ℤ) :
    ColumnL2 (bf.Lab ⊕ Fin fp.Mc) →L[ℂ] ColumnL2 (bf.Lab ⊕ Fin fp.Mc) :=
  (colRelabel (bf.rv fp.Mc s)).comp ((((bf.mainBase fp.Mc s mb).withMask M).proj h).comp
    (ContinuousLinearMap.adjoint (colRelabel (bf.rv fp.Mc s))))

theorem gProjC_isStarProjection (s : List (CatCol bf.Vtx)) (mb : bf.MainBudget s)
    (M : InheritedColumnMask (bf.mainTree fp.Mc s mb)) (h : ℤ) :
    IsStarProjection (fp.gProjC s mb M h) :=
  isStarProjection_conj (bf.rv_injective fp.Mc s)
    (((bf.mainBase fp.Mc s mb).withMask M).isStarProjection_proj h)

/-- Conjugation preserves the composition of global projections. -/
theorem gProjC_comp (s : List (CatCol bf.Vtx)) (mb : bf.MainBudget s)
    (M M' : InheritedColumnMask (bf.mainTree fp.Mc s mb)) (h h' : ℤ) :
    (fp.gProjC s mb M h).comp (fp.gProjC s mb M' h') =
      (colRelabel (bf.rv fp.Mc s)).comp
        (((((bf.mainBase fp.Mc s mb).withMask M).proj h).comp
          (((bf.mainBase fp.Mc s mb).withMask M').proj h')).comp
          (ContinuousLinearMap.adjoint (colRelabel (bf.rv fp.Mc s)))) := by
  refine ContinuousLinearMap.ext fun z => ?_
  unfold gProjC
  simp only [ContinuousLinearMap.comp_apply]
  rw [colRelabel_adjoint_apply_relabel (bf.rv_injective fp.Mc s)]

/-- Global projections with nested masks at one depth are nested. -/
theorem gProjC_mask_nested (s : List (CatCol bf.Vtx)) (mb : bf.MainBudget s)
    {M M' : InheritedColumnMask (bf.mainTree fp.Mc s mb)}
    (hM : ∀ c ∈ (bf.mainTree fp.Mc s mb).cells, M.labels c ⊆ M'.labels c) (h : ℤ) :
    (fp.gProjC s mb M h).comp (fp.gProjC s mb M' h) = fp.gProjC s mb M h := by
  rw [fp.gProjC_comp]
  rw [(bf.mainBase fp.Mc s mb).proj_mask_nested hM h]
  rfl

/-- The global projections commute with the restriction to every cell of depth at most the
clamped depth. -/
theorem gProjC_commute (s : List (CatCol bf.Vtx)) (mb : bf.MainBudget s)
    (M : InheritedColumnMask (bf.mainTree fp.Mc s mb)) (h : ℤ) {Q : ℤ × ℤ}
    (hQ : Q.1 ≤ (bf.mainBase fp.Mc s mb).depth h) :
    (columnL2Restriction (dyadicGridCell A.G Q.1 Q.2)
      (dyadicGridCell_measurable A.G Q.1 Q.2)).comp (fp.gProjC s mb M h) =
    (fp.gProjC s mb M h).comp (columnL2Restriction (dyadicGridCell A.G Q.1 Q.2)
      (dyadicGridCell_measurable A.G Q.1 Q.2)) := by
  have h1 := ((bf.mainBase fp.Mc s mb).withMask M).proj_commute_restrict h (Q := Q) hQ
  refine ContinuousLinearMap.ext fun z => ?_
  have e := DFunLike.congr_fun h1 (ContinuousLinearMap.adjoint (colRelabel (bf.rv fp.Mc s)) z)
  simp only [ContinuousLinearMap.comp_apply] at e
  unfold gProjC
  simp only [ContinuousLinearMap.comp_apply]
  rw [← colRelabel_restrict, colRelabel_adjoint_restrict]
  exact congrArg (colRelabel (bf.rv fp.Mc s)) e

/-- Physical vectors lie in the range of the relabeling. -/
theorem physMain_mem_range (s : List (CatCol bf.Vtx)) {U : Type*} [Fintype U] (x : ColumnL2 U) :
    fp.physMain U x ∈ LinearMap.range (colRelabel (bf.rv fp.Mc s)).toLinearMap :=
  ⟨physEmbed U (bf.RLab fp.Mc s) x, colRelabel_physEmbed _ x⟩

end ActiveSetup.BasicFamilies.FamParams

namespace ActiveSetup.BasicFamilies
variable {κ : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ c₀} (bf : A.BasicFamilies)

open scoped Classical in
/-- The inherited main masks are monotone in the vertex masks. -/
theorem mainMaskT_labels_mono (l : Fin 4) (Mc : ℕ) (s : List (CatCol bf.Vtx))
    (mb : bf.MainBudget s) (r : ℕ) {M M' : ℤ × ℤ → bf.Vtx → Prop}
    (hM : ∀ c ∈ A.cells, ∀ d ∈ A.cells, dyadicGridCell A.G c.1 c.2 ⊆ dyadicGridCell A.G d.1 d.2 →
      ∀ x, M d x → M c x)
    (hM' : ∀ c ∈ A.cells, ∀ d ∈ A.cells, dyadicGridCell A.G c.1 c.2 ⊆ dyadicGridCell A.G d.1 d.2 →
      ∀ x, M' d x → M' c x)
    (hMM : ∀ c x, M c x → M' c x) :
    ∀ c ∈ (bf.mainTree Mc s mb).cells,
      (bf.mainMaskT l Mc s mb r M hM).labels c ⊆ (bf.mainMaskT l Mc s mb r M' hM').labels c := by
  intro c _ v hv
  change v ∈ (match deepAnc (A := A) c with
    | none => ∅
    | some a => Finset.univ.filter fun v : bf.RLab Mc s => bf.mainPred l s a r (M a) v.1) at hv
  change v ∈ (match deepAnc (A := A) c with
    | none => ∅
    | some a => Finset.univ.filter fun v : bf.RLab Mc s => bf.mainPred l s a r (M' a) v.1)
  revert hv
  generalize deepAnc (A := A) c = o
  intro hv
  cases o with
  | none => exact absurd hv (Finset.notMem_empty _)
  | some a =>
    have hv' := (Finset.mem_filter.mp hv).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    obtain ⟨x | n, hrel⟩ := v
    · exact ⟨hv'.1, hMM _ _ hv'.2⟩
    · obtain ⟨hn, hab, hr, hMn⟩ := hv'
      exact ⟨hn, hab, hr, hMM _ _ hMn⟩

end ActiveSetup.BasicFamilies

namespace ActiveSetup.BasicFamilies.FamParams
variable {κ : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ c₀} {bf : A.BasicFamilies}
  (fp : bf.FamParams)

/-- The cell-independent descriptors of the positive filters of a slot along a positive chain:
the ball filter of the level `j`, then the cumulative layers, each with its rank. -/
def slotDescM (j : ℕ) (t : List ℕ) : List (ℕ × Option ℕ) :=
  (fp.brank j, none) :: t.map fun m => (fp.crank m, some m)

open Classical in
/-- The pad mask of a descriptor at a cell: the ball mask of the group or the cumulative mask. -/
def stepMaskM (G : bf.Grp) (j : ℕ) : Option ℕ → Fin fp.P → ℤ × ℤ → bf.Vtx → Prop
  | none, p, I => fp.bmask I G j (p + 1)
  | some m, p, I => fp.cmask I m (p + 1)

open Classical in
theorem stepMaskM_mono (G : bf.Grp) (j : ℕ) (o : Option ℕ) (p : Fin fp.P) :
    ∀ c ∈ A.cells, ∀ d ∈ A.cells, dyadicGridCell A.G c.1 c.2 ⊆ dyadicGridCell A.G d.1 d.2 →
      ∀ x, fp.stepMaskM G j o p d x → fp.stepMaskM G j o p c x := by
  intro c hc d hd hcd x hx
  cases o with
  | none => exact fp.bmask_mono hc hd hcd G j (p + 1) x hx
  | some m => exact fp.cmask_mono hc hd hcd m (p + 1) x hx

open Classical in
theorem stepMaskM_pad_mono (G : bf.Grp) (j : ℕ) (o : Option ℕ) {p p' : Fin fp.P}
    (hpp : p ≤ p') (I : ℤ × ℤ) (x : bf.Vtx) :
    fp.stepMaskM G j o p I x → fp.stepMaskM G j o p' I x := by
  have h : (p : ℕ) + 1 ≤ (p' : ℕ) + 1 := by have : (p : ℕ) ≤ p' := hpp; omega
  cases o with
  | none => exact fp.bmask_pad_mono I G j h x
  | some m => exact fp.cmask_pad_mono I m h x

theorem slotFiltM_eq (G : bf.Grp) (j : ℕ) (I : ℤ × ℤ) (t : List ℕ) :
    fp.slotFiltM G j I t = (fp.slotDescM j t).map fun e =>
      (e.1, fun p : Fin fp.P => fp.stepMaskM G j e.2 p I) := by
  unfold slotFiltM slotDescM
  simp only [List.map_cons, List.map_map]
  rfl

/-- The merged descriptors of a pair of positive chains of the complement slots. -/
def mergeDescM (jc jd : ℕ) (t t' : List ℕ) : List (Bool × ℕ × Option ℕ) :=
  rankMerge Prod.fst (fp.slotDescM jc t) (fp.slotDescM jd t')

/-- The rank merge of the slot filters of a cell is the list of the merged descriptors with their
cell masks. -/
theorem rankMerge_slotFiltM (G : bf.Grp) (jc jd : ℕ) (I : ℤ × ℤ) (t t' : List ℕ) :
    rankMerge Prod.fst (fp.slotFiltM G jc I t) (fp.slotFiltM G jd I t') =
      (fp.mergeDescM jc jd t t').map fun e =>
        (e.1, e.2.1, fun p : Fin fp.P => fp.stepMaskM G (if e.1 then jc else jd) e.2.2 p I) := by
  rw [fp.slotFiltM_eq, fp.slotFiltM_eq, rankMerge_map Prod.fst Prod.fst
    (fun e => (e.1, fun p : Fin fp.P => fp.stepMaskM G jc e.2 p I))
    (fun e => (e.1, fun p : Fin fp.P => fp.stepMaskM G jd e.2 p I)) (fun _ => rfl) (fun _ => rfl)]
  unfold mergeDescM
  refine List.map_congr_left fun e _ => ?_
  obtain ⟨b, x⟩ := e
  cases b <;> rfl

/-- The inherited helper mask (rank `L + 5`) of a descriptor at a pad, on the main tree of the
side slot `a` with its catalog `s_a`. -/
noncomputable def hMaskM (a : Fin 4) (sA : List (CatCol bf.Vtx)) (mbA : bf.MainBudget sA)
    (G : bf.Grp) (jc jd : ℕ) (e : Bool × ℕ × Option ℕ) (p : Fin fp.P) :
    InheritedColumnMask (bf.mainTree fp.Mc sA mbA) :=
  bf.mainMaskT a fp.Mc sA mbA (fp.Lc + 5)
    (fun c => fp.stepMaskM G (if e.1 then jc else jd) e.2.2 p c)
    (fp.stepMaskM_mono G _ e.2.2 p)

/-- The layers `(0, false), …, (n - 1, false)`. -/
def lsOf (n : ℕ) : List (ℕ × Bool) := (List.range n).map fun k => (k, false)

theorem lsOf_length (n : ℕ) : (lsOf n).length = n := by simp [lsOf]

theorem lsOf_succ (n : ℕ) : lsOf (n + 1) = lsOf n ++ [(n, false)] := by
  simp [lsOf, List.range_succ]

/-- The global helper prefix of the descriptors `D` at the depth `h` on the relevant labels of
the side slot: the averaged global helper projections of the steps, in step order. -/
noncomputable def gPreR (a : Fin 4) (sA : List (CatCol bf.Vtx)) (mbA : bf.MainBudget sA)
    (G : bf.Grp) (jc jd : ℕ) (D : List (Bool × ℕ × Option ℕ)) (h : ℤ) :
    ColumnL2 (bf.RLab fp.Mc sA) →L[ℂ] ColumnL2 (bf.RLab fp.Mc sA) :=
  globHist (bf.mainBase fp.Mc sA mbA)
    (fun k p => fp.hMaskM a sA mbA G jc jd (D.getD k (true, 0, none)) p) (lsOf D.length) h

/-- The global band pad family of the step `e` after the prefix `D`, on the relevant labels. -/
noncomputable def gBandR (a : Fin 4) (sA : List (CatCol bf.Vtx)) (mbA : bf.MainBudget sA)
    (G : bf.Grp) (jc jd : ℕ) (e : Bool × ℕ × Option ℕ) (D : List (Bool × ℕ × Option ℕ))
    (n : ℕ) (h : ℤ) : ColumnL2 (bf.RLab fp.Mc sA) →L[ℂ] ColumnL2 (bf.RLab fp.Mc sA) :=
  (padFamC (fun p => ((bf.mainBase fp.Mc sA mbA).withMask
    (fp.hMaskM a sA mbA G jc jd e p)).proj h) n).comp (fp.gPreR a sA mbA G jc jd D h)

/-- The global band pad family of a step after its prefix, conjugated to the main column space
(the operators `A_{p}` of the banded side, blueprint line 2411). -/
noncomputable def gBandC (a : Fin 4) (sA : List (CatCol bf.Vtx)) (mbA : bf.MainBudget sA)
    (G : bf.Grp) (jc jd : ℕ) (e : Bool × ℕ × Option ℕ) (D : List (Bool × ℕ × Option ℕ))
    (n : ℕ) (h : ℤ) : ColumnL2 (bf.Lab ⊕ Fin fp.Mc) →L[ℂ] ColumnL2 (bf.Lab ⊕ Fin fp.Mc) :=
  (colRelabel (bf.rv fp.Mc sA)).comp ((fp.gBandR a sA mbA G jc jd e D n h).comp
    (ContinuousLinearMap.adjoint (colRelabel (bf.rv fp.Mc sA))))

/-- Blueprint lines 2411-2413 ("on the banded side pay at most `P + 1` indices"): the bands of the
global pad family after the prefix are Bessel. -/
theorem gBandC_bessel (a : Fin 4) (sA : List (CatCol bf.Vtx)) (mbA : bf.MainBudget sA)
    (G : bf.Grp) (jc jd : ℕ) (e : Bool × ℕ × Option ℕ) (D : List (Bool × ℕ × Option ℕ))
    (h : ℤ) (y : ColumnL2 (bf.Lab ⊕ Fin fp.Mc)) :
    ∑ p ∈ Finset.range (fp.P + 1), ‖(fp.gBandC a sA mbA G jc jd e D (p + 1) h -
      fp.gBandC a sA mbA G jc jd e D p h) y‖ ^ 2 ≤ ‖y‖ ^ 2 := by
  set! Q := fun p : Fin fp.P => ((bf.mainBase fp.Mc sA mbA).withMask
    (fp.hMaskM a sA mbA G jc jd e p)).proj h
  set! z := fp.gPreR a sA mbA G jc jd D h
    (ContinuousLinearMap.adjoint (colRelabel (bf.rv fp.Mc sA)) y)
  have hb := padFamC_bessel Q (fun p => ((bf.mainBase fp.Mc sA mbA).withMask
      (fp.hMaskM a sA mbA G jc jd e p)).isStarProjection_proj h)
    (fun p p' hpp => (bf.mainBase fp.Mc sA mbA).proj_mask_nested
      (bf.mainMaskT_labels_mono a fp.Mc sA mbA (fp.Lc + 5) _ _
        fun c x hx => fp.stepMaskM_pad_mono G _ e.2.2 hpp c x hx) h) z
  have hz : ‖z‖ ≤ ‖y‖ := (globHist_norm_le _ fp.hP _ _ h _).trans
    (norm_colRelabel_adjoint_le (bf.rv_injective fp.Mc sA) y)
  refine le_trans (le_of_eq ?_) (hb.trans (pow_le_pow_left₀ (norm_nonneg _) hz 2))
  refine Finset.sum_congr rfl fun p _ => ?_
  congr 1
  unfold gBandC gBandR
  simp only [sub_apply, ContinuousLinearMap.comp_apply]
  rw [← map_sub, norm_colRelabel (bf.rv_injective fp.Mc sA)]

/-- The global band pad family commutes with the restriction to every cell of depth at most the
clamped depth. -/
theorem gBandC_commute (a : Fin 4) (sA : List (CatCol bf.Vtx)) (mbA : bf.MainBudget sA)
    (G : bf.Grp) (jc jd : ℕ) (e : Bool × ℕ × Option ℕ) (D : List (Bool × ℕ × Option ℕ))
    (n : ℕ) (h : ℤ) {Q : ℤ × ℤ} (hQ : Q.1 ≤ (bf.mainBase fp.Mc sA mbA).depth h) :
    (columnL2Restriction (dyadicGridCell A.G Q.1 Q.2)
      (dyadicGridCell_measurable A.G Q.1 Q.2)).comp (fp.gBandC a sA mbA G jc jd e D n h) =
    (fp.gBandC a sA mbA G jc jd e D n h).comp (columnL2Restriction (dyadicGridCell A.G Q.1 Q.2)
      (dyadicGridCell_measurable A.G Q.1 Q.2)) := by
  set! rQ := columnL2Restriction (V := bf.RLab fp.Mc sA) (dyadicGridCell A.G Q.1 Q.2)
    (dyadicGridCell_measurable A.G Q.1 Q.2)
  have hproj : ∀ (M : InheritedColumnMask (bf.mainTree fp.Mc sA mbA)),
      (((bf.mainBase fp.Mc sA mbA).withMask M).proj h).comp rQ =
        rQ.comp (((bf.mainBase fp.Mc sA mbA).withMask M).proj h) := fun M =>
    (((bf.mainBase fp.Mc sA mbA).withMask M).proj_commute_restrict h hQ).symm
  have hpre : (fp.gPreR a sA mbA G jc jd D h).comp rQ =
      rQ.comp (fp.gPreR a sA mbA G jc jd D h) := by
    unfold gPreR globHist
    exact layerOp_commute _ rQ (fun m => opAvg_commute _ _ fun p => hproj _) _
  have hpad : (padFamC (fun p => ((bf.mainBase fp.Mc sA mbA).withMask
      (fp.hMaskM a sA mbA G jc jd e p)).proj h) n).comp rQ =
      rQ.comp (padFamC (fun p => ((bf.mainBase fp.Mc sA mbA).withMask
        (fp.hMaskM a sA mbA G jc jd e p)).proj h) n) := by
    unfold padFamC
    split_ifs
    · simp
    · exact hproj _
    · rfl
  have hR : (fp.gBandR a sA mbA G jc jd e D n h).comp rQ =
      rQ.comp (fp.gBandR a sA mbA G jc jd e D n h) := by
    unfold gBandR
    rw [ContinuousLinearMap.comp_assoc, hpre, ← ContinuousLinearMap.comp_assoc, hpad,
      ContinuousLinearMap.comp_assoc]
  refine ContinuousLinearMap.ext fun z => ?_
  have e1 := DFunLike.congr_fun hR (ContinuousLinearMap.adjoint (colRelabel (bf.rv fp.Mc sA)) z)
  simp only [ContinuousLinearMap.comp_apply] at e1
  unfold gBandC
  simp only [ContinuousLinearMap.comp_apply]
  rw [← colRelabel_restrict, colRelabel_adjoint_restrict]
  exact congrArg (colRelabel (bf.rv fp.Mc sA)) e1.symm

end ActiveSetup.BasicFamilies.FamParams

section LayerCongr
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A layer product depends only on the layers used. -/
theorem layerOp_congr {C C' : ℕ → H →L[ℂ] H} :
    ∀ (ls : List (ℕ × Bool)), (∀ x ∈ ls, C x.1 = C' x.1) → layerOp C ls = layerOp C' ls := by
  intro ls
  induction ls using List.reverseRecOn with
  | nil => intro _; rfl
  | append_singleton l x ih =>
    intro h
    rw [layerOp_append, layerOp_append, ih fun y hy => h y (List.mem_append_left _ hy),
      h x (List.mem_append_right _ (List.mem_singleton_self x))]

end LayerCongr

namespace ActiveSetup.BasicFamilies.FamParams
variable {κ : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ c₀} {bf : A.BasicFamilies}
  (fp : bf.FamParams)

theorem mem_lsOf {n : ℕ} {x : ℕ × Bool} (hx : x ∈ lsOf n) : x.1 < n ∧ x.2 = false := by
  simp only [lsOf, List.mem_map, List.mem_range] at hx
  obtain ⟨k, hk, rfl⟩ := hx
  exact ⟨hk, rfl⟩

/-- The jump constant of a helper product with one more layer. -/
noncomputable def bandJumpM (s : List (CatCol bf.Vtx)) (mb : bf.MainBudget s) (n : ℕ) : ℝ :=
  (n + 1) * ∑ m ∈ Finset.range (n + 1), compressionC (bf.mainTree fp.Mc s mb) m ^ 2

theorem bandJumpM_nonneg (s : List (CatCol bf.Vtx)) (mb : bf.MainBudget s) (n : ℕ) :
    0 ≤ fp.bandJumpM s mb n := by
  unfold bandJumpM
  have := Finset.sum_nonneg fun m (_ : m ∈ Finset.range (n + 1)) =>
    sq_nonneg (compressionC (bf.mainTree fp.Mc s mb) m)
  positivity

open Classical in
/-- Blueprint lines 2411-2413 (the outer bands of a fixed input under the subsequent product,
`lem:prefix`): over disjoint depth intervals, the jumps of the global band pad family of a step
after its prefix, on any restrictions, have total square at most `(|D| + 1) Σ_{m ≤ |D|} C_m²`
times the square of the fixed input. -/
theorem gBandC_jump (a : Fin 4) (sA : List (CatCol bf.Vtx)) (mbA : bf.MainBudget sA)
    (G : bf.Grp) (jc jd : ℕ) (e : Bool × ℕ × Option ℕ) (D : List (Bool × ℕ × Option ℕ))
    (n : ℕ) {ι : Type*} [Fintype ι] (r t : ι → ℕ) (hrt : ∀ i, r i ≤ t i)
    (hdis : ∀ i i', i ≠ i' → Disjoint (Finset.Ioc (r i) (t i)) (Finset.Ioc (r i') (t i')))
    (E : ι → Set ℝ) (hE : ∀ i, MeasurableSet (E i)) (x : ColumnL2 (bf.Lab ⊕ Fin fp.Mc)) :
    ∑ i, ‖columnL2Restriction (E i) (hE i)
        ((fp.gBandC a sA mbA G jc jd e D n (A.R.1 + t i) -
          fp.gBandC a sA mbA G jc jd e D n (A.R.1 + r i)) x)‖ ^ 2 ≤
      fp.bandJumpM sA mbA D.length * ‖x‖ ^ 2 := by
  set! Ψ := bf.mainBase fp.Mc sA mbA
  set! Am : ℕ → Fin fp.P → InheritedColumnMask Ψ.D := fun k p =>
    fp.hMaskM a sA mbA G jc jd (D.getD k (true, 0, none)) p
  set! z := ContinuousLinearMap.adjoint (colRelabel (bf.rv fp.Mc sA)) x
  have hz : ‖z‖ ≤ ‖x‖ := norm_colRelabel_adjoint_le (bf.rv_injective fp.Mc sA) x
  have hroot : Ψ.D.root.1 = A.R.1 := rfl
  have hD : Ψ.D = bf.mainTree fp.Mc sA mbA := rfl
  -- reduction to the relevant labels
  have hred : ∀ i, ‖columnL2Restriction (E i) (hE i)
      ((fp.gBandC a sA mbA G jc jd e D n (A.R.1 + t i) -
        fp.gBandC a sA mbA G jc jd e D n (A.R.1 + r i)) x)‖ ≤
      ‖fp.gBandR a sA mbA G jc jd e D n (A.R.1 + t i) z -
        fp.gBandR a sA mbA G jc jd e D n (A.R.1 + r i) z‖ := by
    intro i
    refine (columnL2Indicator_norm_le _ (hE i) _).trans (le_of_eq ?_)
    unfold gBandC
    simp only [sub_apply, ContinuousLinearMap.comp_apply]
    rw [← map_sub, norm_colRelabel (bf.rv_injective fp.Mc sA)]
  have hlen := lsOf_length D.length
  have hbase : ∑ i, ‖fp.gPreR a sA mbA G jc jd D (A.R.1 + t i) z -
      fp.gPreR a sA mbA G jc jd D (A.R.1 + r i) z‖ ^ 2 ≤
      fp.bandJumpM sA mbA D.length * ‖z‖ ^ 2 := by
    have h := globHist_jump Ψ fp.hP Am (lsOf D.length) r t hrt hdis z
    rw [hlen, hroot, hD] at h
    refine le_trans (le_of_eq rfl) (h.trans ?_)
    unfold bandJumpM
    have hS : ∑ m ∈ Finset.range D.length, compressionC (bf.mainTree fp.Mc sA mbA) m ^ 2 ≤
        ∑ m ∈ Finset.range (D.length + 1), compressionC (bf.mainTree fp.Mc sA mbA) m ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.le_succ _))
        fun m _ _ => sq_nonneg _
    have hS0 : 0 ≤ ∑ m ∈ Finset.range D.length, compressionC (bf.mainTree fp.Mc sA mbA) m ^ 2 :=
      Finset.sum_nonneg fun m _ => sq_nonneg _
    have hl : (D.length : ℝ) ≤ D.length + 1 := by linarith
    have hz2 := sq_nonneg ‖z‖
    have h1 := mul_le_mul hl hS hS0 (by positivity)
    nlinarith
  refine le_trans (Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hred i) 2) ?_
  refine le_trans ?_ (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hz 2)
    (fp.bandJumpM_nonneg sA mbA D.length))
  by_cases hn0 : n = 0
  · subst hn0
    have h0 : ∀ h, fp.gBandR a sA mbA G jc jd e D 0 h = 0 := fun h => by
      unfold gBandR padFamC; simp
    simp only [h0, zero_apply, sub_self, norm_zero]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Finset.sum_const_zero]
    exact mul_nonneg (fp.bandJumpM_nonneg sA mbA D.length) (sq_nonneg _)
  by_cases hnP : n - 1 < fp.P
  · -- a single pad on top of the prefix
    set! q : Fin fp.P := ⟨n - 1, hnP⟩
    set! Am' : ℕ → Fin fp.P → InheritedColumnMask Ψ.D := fun k p =>
      if k < D.length then Am k p else fp.hMaskM a sA mbA G jc jd e q
    have hband : ∀ h, fp.gBandR a sA mbA G jc jd e D n h =
        globHist Ψ Am' (lsOf (D.length + 1)) h := by
      intro h
      unfold gBandR gPreR globHist
      rw [lsOf_succ, layerOp_append]
      simp only [Bool.false_eq_true, ite_false]
      have hlay : layerOp (fun m => opAvg fun p : Fin fp.P => (Ψ.withMask (Am' m p)).proj h)
          (lsOf D.length) =
          layerOp (fun m => opAvg fun p : Fin fp.P => (Ψ.withMask (Am m p)).proj h)
            (lsOf D.length) := by
        refine layerOp_congr _ fun y hy => ?_
        have hy1 := (mem_lsOf hy).1
        simp only [Am', hy1, ↓reduceIte]
      rw [hlay]
      congr 1
      have htop : (fun p : Fin fp.P => (Ψ.withMask (Am' D.length p)).proj h) =
          fun _ => (Ψ.withMask (fp.hMaskM a sA mbA G jc jd e q)).proj h := by
        funext p
        simp only [Am', lt_irrefl, ↓reduceIte]
      rw [htop, opAvg_const fp.hP]
      unfold padFamC
      simp only [hn0, hnP, ↓reduceIte, ↓reduceDIte]
      rfl
    have h := globHist_jump Ψ fp.hP Am' (lsOf (D.length + 1)) r t hrt hdis z
    rw [lsOf_length, hroot, hD] at h
    refine le_trans (le_of_eq ?_) (h.trans (le_of_eq ?_))
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [hband, hband]
    · unfold bandJumpM
      push_cast
      ring
  · -- the identity on top of the prefix
    have hband : ∀ h, fp.gBandR a sA mbA G jc jd e D n h = fp.gPreR a sA mbA G jc jd D h := by
      intro h
      unfold gBandR padFamC
      simp only [hn0, hnP, ↓reduceIte, ↓reduceDIte, ContinuousLinearMap.id_comp]
    simp only [hband]
    exact hbase

end ActiveSetup.BasicFamilies.FamParams

namespace ActiveSetup.BasicFamilies.FamParams
variable {κ : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ c₀} {bf : A.BasicFamilies}
  (fp : bf.FamParams)

open Classical in
/-- Blueprint lem:variation as a variation capacity (`VarCap`) of the physical global coarse
outputs of a basic slot for a set of groups of one color: over any disjoint depth intervals and
unions of certified active cells at the right endpoints, the restricted jumps have total square at
most `G₀ · 4 |R|`. -/
theorem varCap_basicOut (l : Fin 4) (s : List (CatCol bf.Vtx))
    (hT : ∀ e ∈ s, ∃ R ∈ residueBox (bf.vtag e.tag).dim 9, ∃ γ : ℝ,
      e = templateCol (bf.vtag e.tag) l R γ e.birth e.rank e.tag)
    (htag : ∀ e ∈ s, bf.occAvail e.tag.2.1 e.tag.1) (d : bf.Vtx) (mb : bf.MainBudget s)
    (hanc : A.AncClosed) (hne : A.cells.Nonempty) (Gs : Finset bf.Grp) (k j : ℕ)
    (hPH : fp.bbase j + fp.P ≤ fp.Hmax) (ls : List (ℕ × Bool))
    {ra rb : ℝ} (hroot : ∀ I ∈ A.cells, dyadicGridCell A.G I.1 I.2 ⊆ Set.Icc ra rb)
    {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hHed : Real.exp (A.Dg * (1 + Real.log A.Hsrc + Real.log τ⁻¹) ^ A.Dg) ≤ fp.Hed)
    {N : ℕ} (hN : ∀ y, ((Finset.univ : Finset ({G // G ∈ Gs} × (bf.Lab ⊕ Fin fp.Mc))).filter
      fun q => ∃ I ∈ A.cells, (∃ k', fp.Cert k' q.1.1 I) ∧
        ∃ p : Fin fp.P, y ∈ dyadicGridCell A.G I.1 I.2 ∧
        q.2 ∈ mainLabelsM A.G fp.Mc (bf.origCols l) s I (fp.brank j)
          (fp.bmask I q.1.1 j (p + 1)) d).card ≤ N)
    (hτN : τ * N * A.colBudget ^ 2 ≤ 1) (c : ℕ) (hc : 1 ≤ c) {kk : ℝ} (hk : 1 ≤ kk)
    (hDm : Real.log (2 * mb.B) ≤ kk ^ c) (hDb : Real.log (2 * A.colBudget) ≤ kk ^ c)
    (hn : (ls.length : ℝ) ≤ c * (Real.log kk + 1)) :
    A.VarCap Gs (fun G h => fp.physMain (bf.Lab ⊕ Fin fp.Mc) (fp.basicOut l s mb G j ls h))
      (fun G J => fp.Cert k G J)
      (Real.exp ((4096 * (c + 1) * (1024 * (c + 1) + c + 7) + c ^ 2 + 3) *
        (1 + Real.log (2 * kk)) ^ 2) * (4 * dyadicGridLength A.G A.R.1)) := by
  intro ι _ r t hrt hdis htd Ec hEc
  have h := fp.basic_variation_G0 l s hT htag d mb hanc hne (ι := {G // G ∈ Gs}) (ι' := ι)
    Subtype.val Subtype.val_injective k j hPH ls r t hrt hdis htd (fun G i => Ec G.1 i)
    (fun G i J hJ => ⟨(hEc G.1 i J hJ).1, (hEc G.1 i J hJ).2.1⟩)
    (fun G i J hJ => (hEc G.1 i J hJ).2.2) hroot hτ hτ1 hHed hN hτN c hc hk hDm hDb hn
  refine le_trans ?_ h
  rw [Fintype.sum_prod_type, ← Finset.sum_coe_sort Gs]
  refine Finset.sum_le_sum fun G _ => Finset.sum_le_sum fun i _ => ?_
  refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
  rw [← map_sub, ← physEmbed_restrict]
  exact norm_physEmbed_apply_le _

end ActiveSetup.BasicFamilies.FamParams

end TrilinearHT.Auto

end

section

namespace TrilinearHT.Auto
open MeasureTheory Metric
open scoped FourierTransform ComplexConjugate ENNReal

/-! ## The number of configurations (blueprint line 2419) -/

end TrilinearHT.Auto

end
