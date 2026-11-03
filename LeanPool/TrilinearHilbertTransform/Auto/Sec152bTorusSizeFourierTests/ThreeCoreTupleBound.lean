/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import LeanPool.TrilinearHilbertTransform.Auto.Sec152bTorusSizeFourierTests.ThreeCoreRefBound

/-!
# Trilinear Hilbert transform: three_core_tuple_bound
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
private def ThreeCoreTupleBoundConclusion11Statement : Prop :=
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
    (_ : (1 : ℕ) ≤ CA)
    (_ : (2 : ℕ) ≤ D.S.dmax)
    (_ : (2 : ℝ) ≤ D.S.Dstar)
    (_ : (2 : ℝ) ≤ D.S.Bstar)
    (_ : (1 : ℕ) ≤ D.S.Q0)
    (I : ℤ × ℤ)
    (_ : I ∈ A.cells)
    (G : bf.Grp)
    (_ : ∀ (j : Fin (4 : ℕ)), (D.Ms j G).zc = (D.Ms (0 : Fin (4 : ℕ)) G).zc)
    (δ : ℝ)
    (_ : (0 : ℝ) < δ)
    (_ : (8 : ℝ) * (↑(D.Ms (0 : Fin (4 : ℕ)) G).zc.dim : ℝ) * δ ≤ (1 : ℝ))
    (_ : δ ≤ (1 / 8 : ℝ))
    (_ : ∀ (j : Fin (4 : ℕ)), (D.Ms j G).δc = δ)
    (_ : ∀ (j : Fin (4 : ℕ)), (D.Ms j G).cl = slotCoeff j)
    (_ : ∀ (j : Fin (4 : ℕ)) (k : Fin (D.Ms j G).zc.dim), (D.Ms j G).ρ k ∈ Set.Icc (0 : ℝ) (1
      : ℝ))
    (_ : ∀ (a b : Fin (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim), ∃ (k : ℤ), (↑D.S.Q0 : ℝ) * (↑((D.Ms
      (0 : Fin (4 : ℕ)) G).zc.C a b) : ℝ) = (↑k : ℝ))
    (Cm : ℝ)
    (_ : (0 : ℝ) ≤ Cm)
    (_ : ∀ (a b : Fin (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim), |(↑((D.Ms (0 : Fin (4 : ℕ)) G).zc.C
      a b) : ℝ)| ≤ Cm)
    (Kt : ℕ)
    (_ : (↑D.S.Q0 : ℝ) * (2 : ℝ) ^ (Kt + (1 : ℕ)) ≤ D.S.Bstar)
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
    (_ : ∀ (j : Fin (4 : ℕ)), j ≠ l → ∀ x ∈ Fsel j, ∀ (i : Fin (D.Ms j G).zc.dim), |(↑(n j x
      i) : ℝ)| ≤ D.S.Dstar * D.S.Eh (h - D.SP.Δ))
    (a : Fin (4 : ℕ) → ℝ)
    (xs : ℝ)
    (_ : xs ∈ dyadicGridCell A.G I.1 I.2)
    (_ : ∀ (j : Fin (4 : ℕ)), j ≠ l → ∀ y ∈ dyadicGridCell A.G I.1 I.2, ‖∑ x ∈ Fsel j, D.c j
      G (A.blkStart D.S.K I.1) (D.preAt I) (↑x : (D.Ms j G).Md) * (D.Ms j G).wave (↑x :
      (D.Ms j G).Md) y - (↑((𝐞 : ℝ → Circle) ((↑(D.Ms j G).cl : ℝ) * centerPhase (D.Ms j
      G).zc (D.Ms j G).ρ y)) : ℂ) * (↑((𝐞 : ℝ → Circle) (a j * (y - xs))) : ℂ) * (D.Ms j
      G).torusG D.S (h - D.SP.Δ) xs (Fsel j) (fun (x : ↥((D.Ms j G).alive (ancAt A.G
      (D.preAt I) (A.blkStart D.S.K I.1 - (4 : ℤ) * (↑D.S.K : ℤ))))) => D.c j G
      (A.blkStart D.S.K I.1) (D.preAt I) (↑x : (D.Ms j G).Md)) (n j) fun (i : Fin (D.Ms
      j G).zc.dim) => (D.Ms j G).torusξ D.S (h - D.SP.Δ) i * (y - xs)‖ ≤ (D.S.Dstar ^
      (150 : ℕ))⁻¹ * ∑ x ∈ Fsel j, ‖D.c j G (A.blkStart D.S.K I.1) (D.preAt I) (↑x :
      (D.Ms j G).Md)‖)
    (X : ↥(ColumnL2 (bf.Lab ⊕ Fin fp.Mc)))
    (Aw : ℕ)
    (Iw : ℕ)
    (_ : (1 : ℕ) ≤ Aw)
    (_ : (0 : ℝ) < dyadicGridLength A.G I.1)
    (_ : (1 : ℝ) ≤ D.S.Dstar)
    (_ : (0 : ℝ) ≤ (D.S.Dstar ^ (100 : ℕ))⁻¹)
    (_ : (D.S.Dstar ^ (100 : ℕ))⁻¹ ≤ (1 : ℝ))
    (_ : ∀ (k : ℕ), (100 : ℕ) ≤ k → (D.S.Dstar ^ k)⁻¹ ≤ (D.S.Dstar ^ (100 : ℕ))⁻¹)
    (_ : (0 : ℝ) ≤ localKernelSupBound κ')
    (_ : (0 : ℝ) ≤ kerC κ' J)
    (_ : (0 : ℝ) ≤ entryCU κ' J Aw)
    (_ : (0 : ℝ) ≤ nearBC κ')
    (_ : (0 : ℝ) < δ / (2 : ℝ))
    (_ : (0 : ℝ) ≤ cutTail (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim δ Kt)
    (_ : (0 : ℝ) ≤ multTail (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim (δ / (2 : ℝ)) D.S.Q0 Cm Kt)
    (_ : (0 : ℝ) ≤ cutNorm (D.Ms (0 : Fin (4 : ℕ)) G).zc.dim δ)
    (_ : (Finset.univ.erase l).card = (3 : ℕ))
    (_ : ∀ j ∈ Finset.univ.erase l, (0 : ℝ) ≤ D.coefSum G I j (Fsel j))
    (_ : (0 : ℝ) ≤ ∏ j ∈ Finset.univ.erase l, D.coefSum G I j (Fsel j))
    (_ : (0 : ℝ) ≤ √((dyadicGridLength A.G I.1)⁻¹ * ∫ (y : ℝ) in dyadicGridLeft A.G I.1
      I.2..dyadicGridLeft A.G I.1 I.2 + dyadicGridLength A.G I.1, ‖augPhys X y‖ ^ (2 :
      ℕ)))
    (_ : (dyadicGridLength A.G I.1)⁻¹ * √(dyadicGridLength A.G I.1 * ∫ (y : ℝ) in
      dyadicGridLeft A.G I.1 I.2..dyadicGridLeft A.G I.1 I.2 + dyadicGridLength A.G I.1,
      ‖augPhys X y‖ ^ (2 : ℕ)) = √((dyadicGridLength A.G I.1)⁻¹ * ∫ (y : ℝ) in
      dyadicGridLeft A.G I.1 I.2..dyadicGridLeft A.G I.1 I.2 + dyadicGridLength A.G I.1,
      ‖augPhys X y‖ ^ (2 : ℕ)))
    (_ : ¬(D.threeRefSet G I xs (h - D.SP.Δ) l a).Nonempty),
  ‖(fp.Λc I : (Fin (4 : ℕ) → ↥(ColumnL2 (bf.Lab ⊕ Fin fp.Mc))) → ℂ)
        (Function.update
          (fun (j : Fin (4 : ℕ)) =>
            D.compSub j G I (Finset.map { toFun := Subtype.val, inj' := Subtype.val_injective }
              (Fsel j)))
          l X)‖ ≤
    (if D.threePasses G I xs (h - D.SP.Δ) l a then D.threePrin G I xs (h - D.SP.Δ) l a Fsel n X
      J Aw Iw else (0 : ℝ)) +
      (((208 : ℝ) * localKernelSupBound κ' + (256 : ℝ) * (2 : ℝ) ^ (Aw + (4 : ℕ)) * entryCU κ' J
        Aw +
                (2 : ℝ) * nearBC κ' +
              (96 : ℝ) * kerC κ' J) *
            (D.S.Dstar ^ (100 : ℕ))⁻¹ *
          ∏ j ∈ Finset.univ.erase l, D.coefSum G I j (Fsel j)) *
        √((dyadicGridLength A.G I.1)⁻¹ *
            ∫ (y : ℝ) in dyadicGridLeft A.G I.1 I.2..dyadicGridLeft A.G I.1 I.2 +
              dyadicGridLength A.G I.1,
              ‖augPhys X y‖ ^ (2 : ℕ))




private theorem three_core_tuple_bound_conclusion_11 : ThreeCoreTupleBoundConclusion11Statement
  := by
  classical
  intro κ' c₀ A bf fp D Cj CA CT CK δs W hV hCA hd2 hD hB hQ I hI G hz δ hδ hdδ hδ8 hδc hcl hρ hQC
    Cm hCm0 hCm Kt hQB hτc hτm hMN hCN J hJ h l Fsel n hn a xs hxs hform X Aw Iw hAw hr hD1 hu0
    hu1 hpow hK hkJ hEC hNB hδ2 hτc0 hτm0 hCN0 hcard hS0 hP0 hσ0 hσ hne
  -- no reference: discarded
  have hnoref : D.threeRefSet G I xs (h - D.SP.Δ) l a = ∅ :=
    Finset.not_nonempty_iff_eq_empty.mp hne
  have hpass : ¬ D.threePasses G I xs (h - D.SP.Δ) l a := fun hp => hne hp.1
  simp only [hpass, ↓reduceIte, zero_add]
  have key := D.three_core_noref_side hV hCA hd2 hD hB hQ hI G hz hδ hdδ hδ8 hδc hcl hρ hQC
    hCm0 hCm hδ2 hQB (J := J) (by omega) h l Fsel n hn a hxs hform hnoref X Aw hAw
  have hL2X : MemLp (augPhys X) 2 (volume.restrict (Set.Ioc (dyadicGridLeft A.G I.1 I.2)
      ((dyadicGridLeft A.G I.1 I.2) + (dyadicGridLength A.G I.1)))) :=
    (memLp_column_coord X none).restrict _
  have hcs := cell_l1_le_size hr hL2X
  have hL1 : 0 ≤ (dyadicGridLength A.G I.1)⁻¹ * ∫ y in Set.Icc (dyadicGridLeft A.G I.1 I.2)
      ((dyadicGridLeft A.G I.1 I.2) + (dyadicGridLength A.G I.1)), ‖augPhys X y‖ :=
    mul_nonneg (inv_nonneg.mpr hr.le) (integral_nonneg fun _ => norm_nonneg _)
  have hL1' : 0 ≤ (dyadicGridLength A.G I.1)⁻¹ * ∫ y in Set.Ico (dyadicGridLeft A.G I.1 I.2)
      ((dyadicGridLeft A.G I.1 I.2) + (dyadicGridLength A.G I.1)), ‖augPhys X y‖ :=
    mul_nonneg (inv_nonneg.mpr hr.le) (integral_nonneg fun _ => norm_nonneg _)
  have hT1 := mul_le_mul (gauge_err_le (K := localKernelSupBound κ') (δ := δ) (P := (∏ j ∈
      Finset.univ.erase l, D.coefSum G I j (Fsel j)))
    (D.Ms 0 G).zc.dim hD1 hK hP0 hτc0 hτm0 hτc hτm) hcs.1 hL1 (by positivity)
  have hU0 : 0 < D.U0 := by unfold U0; positivity
  have hU1 : 1 ≤ D.U0 := by unfold U0; exact one_le_pow₀ hD1
  have hUu : D.U0⁻¹ ≤ (D.S.Dstar ^ 100)⁻¹ := by unfold U0; exact hpow 250 (by norm_num)
  have hUJ : (D.U0 ^ J)⁻¹ ≤ (D.S.Dstar ^ 100)⁻¹ :=
    (inv_anti₀ hU0 (le_self_pow₀ hU1 (by omega))).trans hUu
  have hτc1 : cutTail (D.Ms 0 G).zc.dim δ Kt ≤ 1 := hτc.trans ((hpow 300 (by norm_num)).trans hu1)
  have hτm1 : multTail (D.Ms 0 G).zc.dim (δ / 2) D.S.Q0 Cm Kt ≤ 1 := hτm.trans ((hpow 300 (by
      norm_num)).trans hu1)
  have hWn : (1 + multTail (D.Ms 0 G).zc.dim (δ / 2) D.S.Q0 Cm Kt) * (1 + cutTail (D.Ms 0
      G).zc.dim δ Kt) * ∏ j ∈ Finset.univ.erase l, ((1 + cutTail (D.Ms 0 G).zc.dim δ Kt) *
      D.coefSum G I j (Fsel j)) ≤ 32 * (∏ j ∈ Finset.univ.erase l, D.coefSum G I j (Fsel j)) := by
    rw [Finset.prod_mul_distrib, Finset.prod_const, hcard]
    have h3 : (1 + cutTail (D.Ms 0 G).zc.dim δ Kt) ^ 3 ≤ 8 :=
      calc (1 + cutTail (D.Ms 0 G).zc.dim δ Kt) ^ 3 ≤ 2 ^ 3 := pow_le_pow_left₀ (by linarith) (by
          linarith) 3
        _ = 8 := by norm_num
    have hW4 : (1 + multTail (D.Ms 0 G).zc.dim (δ / 2) D.S.Q0 Cm Kt) * (1 + cutTail (D.Ms 0
        G).zc.dim δ Kt) ≤ 4 :=
      calc (1 + multTail (D.Ms 0 G).zc.dim (δ / 2) D.S.Q0 Cm Kt) * (1 + cutTail (D.Ms 0 G).zc.dim
          δ Kt) ≤ 2 * 2 :=
            mul_le_mul (by linarith only [hτm1]) (by linarith) (by linarith only [hτc0])
              (by norm_num)
        _ = 4 := by norm_num
    calc (1 + multTail (D.Ms 0 G).zc.dim (δ / 2) D.S.Q0 Cm Kt) * (1 + cutTail (D.Ms 0 G).zc.dim δ
        Kt) * ((1 + cutTail (D.Ms 0 G).zc.dim δ Kt) ^ 3 * (∏ j ∈ Finset.univ.erase l, D.coefSum G
            I j (Fsel j))) ≤ 4 * (8 * (∏ j ∈ Finset.univ.erase l, D.coefSum G I j (Fsel j))) :=
          mul_le_mul hW4 (mul_le_mul_of_nonneg_right h3 hP0) (by positivity) (by norm_num)
      _ = 32 * (∏ j ∈ Finset.univ.erase l, D.coefSum G I j (Fsel j)) := by ring
  have hτc1' : 0 ≤ 1 + cutTail (D.Ms 0 G).zc.dim δ Kt := by linarith
  have hτm1' : 0 ≤ 1 + multTail (D.Ms 0 G).zc.dim (δ / 2) D.S.Q0 Cm Kt := by linarith only [hτm0]
  have hWn0 : 0 ≤ (1 + multTail (D.Ms 0 G).zc.dim (δ / 2) D.S.Q0 Cm Kt) * (1 + cutTail (D.Ms 0
      G).zc.dim δ Kt) * ∏ j ∈ Finset.univ.erase l, ((1 + cutTail (D.Ms 0 G).zc.dim δ Kt) *
      D.coefSum G I j (Fsel j)) :=
    mul_nonneg (mul_nonneg hτm1' hτc1') (Finset.prod_nonneg fun j hj =>
      mul_nonneg hτc1' (hS0 j hj))
  have hMid : 4 * ((dyadicGridLength A.G I.1)⁻¹ * (entryCU κ' J Aw * (D.U0 ^ J)⁻¹) * 2 ^ (Aw + 4)
      *
      (((1 + multTail (D.Ms 0 G).zc.dim (δ / 2) D.S.Q0 Cm Kt) * (1 + cutTail (D.Ms 0 G).zc.dim δ
          Kt) * ∏ j ∈ Finset.univ.erase l, ((1 + cutTail (D.Ms 0 G).zc.dim δ Kt) *
        D.coefSum G I j (Fsel j))) * (Real.sqrt (dyadicGridLength A.G I.1 * ∫ y in
            (dyadicGridLeft A.G I.1 I.2)..
    dyadicGridLeft A.G I.1 I.2 + dyadicGridLength A.G I.1, ‖augPhys X y‖ ^ 2)))) ≤
      128 * 2 ^ (Aw + 4) * entryCU κ' J Aw * (D.S.Dstar ^ 100)⁻¹ * (∏ j ∈ Finset.univ.erase l,
          D.coefSum G I j (Fsel j)) * (Real.sqrt ((dyadicGridLength A.G I.1)⁻¹ * ∫ y in
              (dyadicGridLeft A.G I.1 I.2)..
    dyadicGridLeft A.G I.1 I.2 + dyadicGridLength A.G I.1, ‖augPhys X y‖ ^ 2)) := by
    have e : 4 * ((dyadicGridLength A.G I.1)⁻¹ * (entryCU κ' J Aw * (D.U0 ^ J)⁻¹) * 2 ^ (Aw + 4) *
        (((1 + multTail (D.Ms 0 G).zc.dim (δ / 2) D.S.Q0 Cm Kt) * (1 + cutTail (D.Ms 0 G).zc.dim
            δ Kt) * ∏ j ∈ Finset.univ.erase l, ((1 + cutTail (D.Ms 0 G).zc.dim δ Kt) *
          D.coefSum G I j (Fsel j))) * (Real.sqrt (dyadicGridLength A.G I.1 * ∫ y in
              (dyadicGridLeft A.G I.1 I.2)..
    dyadicGridLeft A.G I.1 I.2 + dyadicGridLength A.G I.1, ‖augPhys X y‖ ^ 2)))) =
        4 * 2 ^ (Aw + 4) * entryCU κ' J Aw * (D.U0 ^ J)⁻¹ * ((1 + multTail (D.Ms 0 G).zc.dim (δ /
            2) D.S.Q0 Cm Kt) * (1 + cutTail (D.Ms 0 G).zc.dim δ Kt) *
          ∏ j ∈ Finset.univ.erase l, ((1 + cutTail (D.Ms 0 G).zc.dim δ Kt) * D.coefSum G I j
              (Fsel j))) *
          ((dyadicGridLength A.G I.1)⁻¹ * (Real.sqrt (dyadicGridLength A.G I.1 * ∫ y in
              (dyadicGridLeft A.G I.1 I.2)..
    dyadicGridLeft A.G I.1 I.2 + dyadicGridLength A.G I.1, ‖augPhys X y‖ ^ 2))) := by ring
    rw [e, hσ]
    have hUJ0 : 0 ≤ (D.U0 ^ J)⁻¹ := by positivity
    have hc4 : 0 ≤ 4 * 2 ^ (Aw + 4) * entryCU κ' J Aw := by positivity
    calc 4 * 2 ^ (Aw + 4) * entryCU κ' J Aw * (D.U0 ^ J)⁻¹ * ((1 + multTail (D.Ms 0 G).zc.dim (δ
        / 2) D.S.Q0 Cm Kt) * (1 + cutTail (D.Ms 0 G).zc.dim δ Kt) *
          ∏ j ∈ Finset.univ.erase l, ((1 + cutTail (D.Ms 0 G).zc.dim δ Kt) * D.coefSum G I j
              (Fsel j))) * (Real.sqrt ((dyadicGridLength A.G I.1)⁻¹ * ∫ y in (dyadicGridLeft A.G
                  I.1 I.2)..
    dyadicGridLeft A.G I.1 I.2 + dyadicGridLength A.G I.1, ‖augPhys X y‖ ^ 2)) ≤
          4 * 2 ^ (Aw + 4) * entryCU κ' J Aw * (D.S.Dstar ^ 100)⁻¹ * (32 * (∏ j ∈
              Finset.univ.erase l, D.coefSum G I j (Fsel j))) * (Real.sqrt ((dyadicGridLength A.G
                  I.1)⁻¹ * ∫ y in (dyadicGridLeft A.G I.1 I.2)..
    dyadicGridLeft A.G I.1 I.2 + dyadicGridLength A.G I.1, ‖augPhys X y‖ ^ 2)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul (mul_le_mul_of_nonneg_left hUJ hc4) hWn hWn0
          (mul_nonneg hc4 hu0)) hσ0
      _ = 128 * 2 ^ (Aw + 4) * entryCU κ' J Aw * (D.S.Dstar ^ 100)⁻¹ * (∏ j ∈ Finset.univ.erase
          l, D.coefSum G I j (Fsel j)) * (Real.sqrt ((dyadicGridLength A.G I.1)⁻¹ * ∫ y in
              (dyadicGridLeft A.G I.1 I.2)..
    dyadicGridLeft A.G I.1 I.2 + dyadicGridLength A.G I.1, ‖augPhys X y‖ ^ 2)) := by ring
  have hCo : (multNorm (D.Ms 0 G).zc.dim (δ / 2) D.S.Q0 Cm * (cutNorm (D.Ms 0 G).zc.dim δ *
      ∏ j ∈ Finset.univ.erase l, (cutNorm (D.Ms 0 G).zc.dim δ * D.coefSum G I j (Fsel j)))) *
      ((dyadicGridLength A.G I.1)⁻¹ * (∫ y in Set.Ico (dyadicGridLeft A.G I.1 I.2)
          ((dyadicGridLeft A.G I.1 I.2) + (dyadicGridLength A.G I.1)), ‖augPhys X y‖) *
        (12 * (kerC κ' J * (4 / D.U0) ^ (J - 2)))) ≤ 48 * kerC κ' J * (D.S.Dstar ^ 100)⁻¹ * (∏ j
            ∈ Finset.univ.erase l, D.coefSum G I j (Fsel j)) * (Real.sqrt ((dyadicGridLength A.G
                I.1)⁻¹ * ∫ y in (dyadicGridLeft A.G I.1 I.2)..
    dyadicGridLeft A.G I.1 I.2 + dyadicGridLength A.G I.1, ‖augPhys X y‖ ^ 2)) := by
    have hMNP := norm_prod_le_pow' (Finset.univ.erase l) (S := fun j => D.coefSum G I j (Fsel j))
      hS0 hMN hCN0 hCN
    rw [hcard] at hMNP
    have hq0 : 0 ≤ 4 / D.U0 := by positivity
    have hU4 : 4 ≤ D.U0 := by
      unfold U0
      calc (4 : ℝ) = 2 ^ 2 := by norm_num
        _ ≤ D.S.Dstar ^ 2 := pow_le_pow_left₀ (by norm_num) hD 2
        _ ≤ D.S.Dstar ^ 250 := pow_le_pow_right₀ hD1 (by norm_num)
    have hq1 : 4 / D.U0 ≤ 1 := by rw [div_le_one hU0]; exact hU4
    have hpw : (4 / D.U0) ^ (J - 2) ≤ 4 / D.U0 := pow_le_of_le_one hq0 hq1 (by omega)
    have hfar : 12 * (kerC κ' J * (4 / D.U0) ^ (J - 2)) ≤ 48 * kerC κ' J * D.U0⁻¹ := by
      have h1 := mul_le_mul_of_nonneg_left hpw hkJ
      calc 12 * (kerC κ' J * (4 / D.U0) ^ (J - 2)) ≤ 12 * (kerC κ' J * (4 / D.U0)) := by
            linarith only [h1]
        _ = 48 * kerC κ' J * D.U0⁻¹ := by rw [div_eq_mul_inv]; ring
    have hfar0 : 0 ≤ 12 * (kerC κ' J * (4 / D.U0) ^ (J - 2)) := by positivity
    have h250 := inv_pow_mul_pow5_le hD1 (k := 250) (by norm_num)
    have hU : D.U0⁻¹ = (D.S.Dstar ^ 250)⁻¹ := rfl
    calc _ ≤ (D.S.Dstar ^ (3 + 2) * (∏ j ∈ Finset.univ.erase l, D.coefSum G I j (Fsel j))) *
        ((Real.sqrt ((dyadicGridLength A.G I.1)⁻¹ * ∫ y in (dyadicGridLeft A.G I.1 I.2)..
    dyadicGridLeft A.G I.1 I.2 + dyadicGridLength A.G I.1, ‖augPhys X y‖ ^ 2)) * (48 * kerC κ' J
        * D.U0⁻¹)) :=
          mul_le_mul hMNP (mul_le_mul hcs.2 hfar hfar0 hσ0)
            (mul_nonneg hL1' hfar0) (by positivity)
      _ = 48 * kerC κ' J * (D.U0⁻¹ * D.S.Dstar ^ 5) * (∏ j ∈ Finset.univ.erase l, D.coefSum G I j
          (Fsel j)) * (Real.sqrt ((dyadicGridLength A.G I.1)⁻¹ * ∫ y in (dyadicGridLeft A.G I.1
              I.2)..
    dyadicGridLeft A.G I.1 I.2 + dyadicGridLength A.G I.1, ‖augPhys X y‖ ^ 2)) := by ring
      _ ≤ 48 * kerC κ' J * (D.S.Dstar ^ 100)⁻¹ * (∏ j ∈ Finset.univ.erase l, D.coefSum G I j
          (Fsel j)) * (Real.sqrt ((dyadicGridLength A.G I.1)⁻¹ * ∫ y in (dyadicGridLeft A.G I.1
              I.2)..
    dyadicGridLeft A.G I.1 I.2 + dyadicGridLength A.G I.1, ‖augPhys X y‖ ^ 2)) :=
        by rw [hU]; gcongr
  have hEP' : 0 ≤ kerC κ' J * (D.S.Dstar ^ 100)⁻¹ * (∏ j ∈ Finset.univ.erase l, D.coefSum G I j
      (Fsel j)) * (Real.sqrt ((dyadicGridLength A.G I.1)⁻¹ * ∫ y in (dyadicGridLeft A.G I.1 I.2)..
    dyadicGridLeft A.G I.1 I.2 + dyadicGridLength A.G I.1, ‖augPhys X y‖ ^ 2)) := by positivity
  have hEK : 0 ≤ localKernelSupBound κ' * (D.S.Dstar ^ 100)⁻¹ * (∏ j ∈ Finset.univ.erase l,
      D.coefSum G I j (Fsel j)) * (Real.sqrt ((dyadicGridLength A.G I.1)⁻¹ * ∫ y in
          (dyadicGridLeft A.G I.1 I.2)..
    dyadicGridLeft A.G I.1 I.2 + dyadicGridLength A.G I.1, ‖augPhys X y‖ ^ 2)) := by positivity
  have hEN : 0 ≤ nearBC κ' * (D.S.Dstar ^ 100)⁻¹ * (∏ j ∈ Finset.univ.erase l, D.coefSum G I j
      (Fsel j)) * (Real.sqrt ((dyadicGridLength A.G I.1)⁻¹ * ∫ y in (dyadicGridLeft A.G I.1 I.2)..
    dyadicGridLeft A.G I.1 I.2 + dyadicGridLength A.G I.1, ‖augPhys X y‖ ^ 2)) := by positivity
  linarith only [key, hT1, hMid, hCo, hEN]


open Classical in
/-- Blueprint `eq:core-numerical` (lines 2562-2567) for a three-core tuple on a leaf cell of the
side states, side role `l` and side column `X` (enlarged gauge cutoff `δ/2`, truncation tails at
most `D_*^{-300}`, full Fourier norms at most `D_*`, `J ≥ 3`, windows up to `2^{I_w} ≥ U₀/2`): the
cell form is at most the principal window quantity `threePrin` if the tuple passes the three-core
test, and `0` if it is discarded, plus the absolute error
`C_{J,A} D_*^{-100} Π_{j ≠ l} Σ_{F_j} |α| σ`
with the local side size `σ = (r⁻¹ ∫_I |S_phys|²)^{1/2}` as extra factor. Discarded tuples:
`|β| < U₀⁻¹` gives `C_{J,A} μ ν^{-J} ≤ C_{J,A} U₀⁻¹` (`entryC_le_min`), and no reference gives all
anchored frequencies far (`three_core_noref_side`). -/
theorem three_core_tuple_bound {Cj CA CT CK : ℕ} {δs W : ℝ} (hV : D.S.Valid Cj CA CT CK δs W)
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
    (X : ColumnL2 (bf.Lab ⊕ Fin fp.Mc))
    (Aw Iw : ℕ) (hAw : 1 ≤ Aw) (hIw : D.U0 ≤ 2 ^ (Iw + 1)) :
    ‖fp.Λc I (Function.update (fun j => D.compSub j G I
        ((Fsel j).map ⟨Subtype.val, Subtype.val_injective⟩)) l X)‖ ≤
      (if D.threePasses G I xs (h - D.SP.Δ) l a then
        D.threePrin G I xs (h - D.SP.Δ) l a Fsel n X J Aw Iw else 0) +
      threeErrC κ' J Aw * (D.S.Dstar ^ 100)⁻¹ * (∏ j ∈ Finset.univ.erase l, D.coefSum G I j (Fsel
          j)) * (Real.sqrt ((dyadicGridLength A.G I.1)⁻¹ * ∫ y in (dyadicGridLeft A.G I.1 I.2)..
      dyadicGridLeft A.G I.1 I.2 + dyadicGridLength A.G I.1, ‖augPhys X y‖ ^ 2)) := by
  have hr : 0 < (dyadicGridLength A.G I.1) := dyadicGridLength_pos A.G I.1
  have hw := A.adm I hI
  have hDp : 0 < D.S.Dstar := by linarith
  have hD1 : (1 : ℝ) ≤ D.S.Dstar := by linarith
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
  have hσ0 : 0 ≤ (Real.sqrt ((dyadicGridLength A.G I.1)⁻¹ * ∫ y in (dyadicGridLeft A.G I.1 I.2)..
      dyadicGridLeft A.G I.1 I.2 + dyadicGridLength A.G I.1, ‖augPhys X y‖ ^ 2)) :=
          Real.sqrt_nonneg _
  have hR20 : 0 ≤ (Real.sqrt (dyadicGridLength A.G I.1 * ∫ y in (dyadicGridLeft A.G I.1 I.2)..
      dyadicGridLeft A.G I.1 I.2 + dyadicGridLength A.G I.1, ‖augPhys X y‖ ^ 2)) :=
          Real.sqrt_nonneg _
  have hσ : (dyadicGridLength A.G I.1)⁻¹ * (Real.sqrt (dyadicGridLength A.G I.1 * ∫ y in
      (dyadicGridLeft A.G I.1 I.2)..
      dyadicGridLeft A.G I.1 I.2 + dyadicGridLength A.G I.1, ‖augPhys X y‖ ^ 2)) = (Real.sqrt
          ((dyadicGridLength A.G I.1)⁻¹ * ∫ y in (dyadicGridLeft A.G I.1 I.2)..
      dyadicGridLeft A.G I.1 I.2 + dyadicGridLength A.G I.1, ‖augPhys X y‖ ^ 2)) :=
          inv_mul_sqrt_mul hr
  have hErr : threeErrC κ' J Aw = 208 * localKernelSupBound κ' + 2 ^ (Aw + 12) * entryCU κ' J Aw +
      2 * nearBC κ' + 96 * kerC κ' J := rfl
  have h12 : (2 : ℝ) ^ (Aw + 12) = 256 * 2 ^ (Aw + 4) := by
    rw [show Aw + 12 = (Aw + 4) + 8 by ring, pow_add]; norm_num; ring
  have hEP : 0 ≤ 2 ^ (Aw + 4) * entryCU κ' J Aw * (D.S.Dstar ^ 100)⁻¹ * (∏ j ∈ Finset.univ.erase l,
      D.coefSum G I j (Fsel j)) * (Real.sqrt ((dyadicGridLength A.G I.1)⁻¹ * ∫ y in (dyadicGridLeft
          A.G I.1 I.2)..
      dyadicGridLeft A.G I.1 I.2 + dyadicGridLength A.G I.1, ‖augPhys X y‖ ^ 2)) := by positivity
  rw [hErr, h12]
  by_cases hne : (D.threeRefSet G I xs (h - D.SP.Δ) l a).Nonempty
  · have key := D.three_core_ref_bound hV hCA hCT hd2 hD hB hQ hSP hI G hz hdim hδ hdδ hδ8 hδc
      hcl hρ hQC hCm0 hCm hQB hτc hτm hMN hCN hJ hh j₀ hgood l Fsel n hn a hxs hform hne X Aw Iw
      hAw hIw
    by_cases hpass : D.threePasses G I xs (h - D.SP.Δ) l a
    · simp only [hpass, ↓reduceIte]
      linarith only [hEP, key]
    · simp only [hpass, ↓reduceIte, zero_add]
      -- a discarded tuple with a reference: `|β| < U₀⁻¹`
      have hβ : |D.threeBeta G I xs (h - D.SP.Δ) l a| < D.U0⁻¹ := by
        by_contra hc
        exact hpass ⟨hne, not_lt.mp hc⟩
      have heC : entryC κ' J Aw (D.threeBeta G I xs (h - D.SP.Δ) l a) ≤ entryCU κ' J Aw *
          (D.S.Dstar ^ 100)⁻¹ := by
        refine (entryC_le_min hr hw J Aw _).trans (mul_le_mul_of_nonneg_left ?_ hEC)
        have h3 : D.U0⁻¹ ≤ (D.S.Dstar ^ 100)⁻¹ := by unfold U0; exact hpow 250 (by norm_num)
        exact (min_le_right _ _).trans (hβ.le.trans h3)
      have hPa : ∀ j ∈ Finset.univ.erase l, D.coreSize G I xs (h - D.SP.Δ) j (Fsel j) (n j) ≤
          D.coefSum G I j (Fsel j) := fun j _ =>
        D.coreSize_le G I xs _ j (by rw [hδc j]; exact hδ) (Fsel j) (n j)
      have hPaP : (∏ j ∈ Finset.univ.erase l, D.coreSize G I xs (h - D.SP.Δ) j (Fsel j) (n j)) ≤ (∏
          j ∈ Finset.univ.erase l, D.coefSum G I j (Fsel j)) :=
        Finset.prod_le_prod₀ (fun j _ => D.coreSize_nonneg G I xs _ j _ _) hPa
      have hPa0 : 0 ≤ (∏ j ∈ Finset.univ.erase l, D.coreSize G I xs (h - D.SP.Δ) j (Fsel j) (n
          j)) := Finset.prod_nonneg fun j _ => D.coreSize_nonneg G I xs _ j _ _
      have hprin : D.threePrin G I xs (h - D.SP.Δ) l a Fsel n X J Aw Iw ≤
          4 * 2 ^ (Aw + 4) * entryCU κ' J Aw * (D.S.Dstar ^ 100)⁻¹ * (∏ j ∈ Finset.univ.erase l,
              D.coefSum G I j (Fsel j)) * (Real.sqrt ((dyadicGridLength A.G I.1)⁻¹ * ∫ y in
                  (dyadicGridLeft A.G I.1 I.2)..
      dyadicGridLeft A.G I.1 I.2 + dyadicGridLength A.G I.1, ‖augPhys X y‖ ^ 2)) := by
        unfold threePrin
        have hterm : ∀ i ∈ Finset.range (Iw + 1), ((dyadicGridLength A.G I.1)⁻¹ * entryC κ' J Aw
            (D.threeBeta G I xs (h - D.SP.Δ) l a) * 2 ^ (Aw + 4) *
            ((2 : ℝ) ^ i)⁻¹ ^ (Aw + 1) * (∏ j ∈ Finset.univ.erase l, D.coreSize G I xs (h - D.SP.Δ)
                j (Fsel j) (n j))) * Real.sqrt (∫ ρ', sideWinE (D.Ms 0 G).zc l
              (augPhys X) (dyadicGridLeft A.G I.1 I.2) (dyadicGridLength A.G I.1) (D.threeWin G I
                  xs (h - D.SP.Δ) l a (2 ^ i)) ρ'
              ∂offsetMeasure (D.Ms 0 G).zc.dim) ≤
            ((dyadicGridLength A.G I.1)⁻¹ * (entryCU κ' J Aw * (D.S.Dstar ^ 100)⁻¹) * 2 ^ (Aw + 4)
                * (∏ j ∈ Finset.univ.erase l, D.coefSum G I j (Fsel j)) * (Real.sqrt
                    (dyadicGridLength A.G I.1 * ∫ y in (dyadicGridLeft A.G I.1 I.2)..
      dyadicGridLeft A.G I.1 I.2 + dyadicGridLength A.G I.1, ‖augPhys X y‖ ^ 2))) *
              ((2 : ℝ) ^ i)⁻¹ ^ (Aw + 1) := fun i _ => by
          have hω := window_root_le (D.Ms 0 G).zc l X I (D.threeWin G I xs (h - D.SP.Δ) l a (2 ^ i))
          have hω0 := Real.sqrt_nonneg (∫ ρ', sideWinE (D.Ms 0 G).zc l
              (augPhys X) (dyadicGridLeft A.G I.1 I.2) (dyadicGridLength A.G I.1) (D.threeWin G I
                  xs (h - D.SP.Δ) l a (2 ^ i)) ρ'
              ∂offsetMeasure (D.Ms 0 G).zc.dim)
          have hc0 : 0 ≤ (dyadicGridLength A.G I.1)⁻¹ * entryC κ' J Aw (D.threeBeta G I xs (h -
              D.SP.Δ) l a) * 2 ^ (Aw + 4) * ((2 : ℝ) ^ i)⁻¹ ^ (Aw + 1) := by
            have := entryC_nonneg hr hw J Aw (D.threeBeta G I xs (h - D.SP.Δ) l a)
            have := inv_nonneg.mpr hr.le
            positivity
          have hcu : (dyadicGridLength A.G I.1)⁻¹ * entryC κ' J Aw (D.threeBeta G I xs (h - D.SP.Δ)
              l a) * 2 ^ (Aw + 4) * ((2 : ℝ) ^ i)⁻¹ ^ (Aw + 1) ≤
              (dyadicGridLength A.G I.1)⁻¹ * (entryCU κ' J Aw * (D.S.Dstar ^ 100)⁻¹) * 2 ^ (Aw + 4)
                  * ((2 : ℝ) ^ i)⁻¹ ^ (Aw + 1) := by
            have := inv_nonneg.mpr hr.le
            gcongr
          calc ((dyadicGridLength A.G I.1)⁻¹ * entryC κ' J Aw (D.threeBeta G I xs (h - D.SP.Δ) l a)
              * 2 ^ (Aw + 4) * ((2 : ℝ) ^ i)⁻¹ ^ (Aw + 1) * (∏ j ∈ Finset.univ.erase l, D.coreSize
                  G I xs (h - D.SP.Δ) j (Fsel j) (n j))) *
                Real.sqrt (∫ ρ', sideWinE (D.Ms 0 G).zc l (augPhys X) (dyadicGridLeft A.G I.1 I.2)
                    (dyadicGridLength A.G I.1)
                  (D.threeWin G I xs (h - D.SP.Δ) l a (2 ^ i)) ρ' ∂offsetMeasure (D.Ms 0 G).zc.dim)
              ≤ ((dyadicGridLength A.G I.1)⁻¹ * (entryCU κ' J Aw * (D.S.Dstar ^ 100)⁻¹) * 2 ^ (Aw +
                  4) * ((2 : ℝ) ^ i)⁻¹ ^ (Aw + 1) *
                  (∏ j ∈ Finset.univ.erase l, D.coefSum G I j (Fsel j))) * (Real.sqrt
                      (dyadicGridLength A.G I.1 * ∫ y in (dyadicGridLeft A.G I.1 I.2)..
      dyadicGridLeft A.G I.1 I.2 + dyadicGridLength A.G I.1, ‖augPhys X y‖ ^ 2)) :=
                mul_le_mul (mul_le_mul hcu hPaP hPa0 (hc0.trans hcu)) hω hω0
                  (mul_nonneg (hc0.trans hcu) hP0)
            _ = _ := by ring
        have hsum := Finset.sum_le_sum hterm
        rw [← Finset.mul_sum] at hsum
        have hgeo := sum_range_inv_pow_le Aw Iw
        have hK0 : 0 ≤ (dyadicGridLength A.G I.1)⁻¹ * (entryCU κ' J Aw * (D.S.Dstar ^ 100)⁻¹) * 2 ^
            (Aw + 4) * (∏ j ∈ Finset.univ.erase l, D.coefSum G I j (Fsel j)) * (Real.sqrt
                (dyadicGridLength A.G I.1 * ∫ y in (dyadicGridLeft A.G I.1 I.2)..
      dyadicGridLeft A.G I.1 I.2 + dyadicGridLength A.G I.1, ‖augPhys X y‖ ^ 2)) := by
          have := inv_nonneg.mpr hr.le
          positivity
        have h2 := mul_le_mul_of_nonneg_left hgeo hK0
        calc _ ≤ 2 * ((dyadicGridLength A.G I.1)⁻¹ * (entryCU κ' J Aw * (D.S.Dstar ^ 100)⁻¹) * 2 ^
            (Aw + 4) * (∏ j ∈ Finset.univ.erase l, D.coefSum G I j (Fsel j)) * (Real.sqrt
                (dyadicGridLength A.G I.1 * ∫ y in (dyadicGridLeft A.G I.1 I.2)..
      dyadicGridLeft A.G I.1 I.2 + dyadicGridLength A.G I.1, ‖augPhys X y‖ ^ 2)) * 2) := by
              linarith only [hsum, h2]
          _ = 4 * 2 ^ (Aw + 4) * entryCU κ' J Aw * (D.S.Dstar ^ 100)⁻¹ * (∏ j ∈ Finset.univ.erase
              l, D.coefSum G I j (Fsel j)) * ((dyadicGridLength A.G I.1)⁻¹ * (Real.sqrt
                  (dyadicGridLength A.G I.1 * ∫ y in (dyadicGridLeft A.G I.1 I.2)..
      dyadicGridLeft A.G I.1 I.2 + dyadicGridLength A.G I.1, ‖augPhys X y‖ ^ 2))) := by ring
          _ = _ := by rw [hσ]
      linarith only [key, hprin]
  · expose_names
    exact @three_core_tuple_bound_conclusion_11 κ' c₀ A bf fp D Cj CA CT CK δs W hV hCA hd2 hD hB
      hQ I hI G hz δ hδ hdδ hδ8 hδc hcl hρ hQC Cm hCm0 hCm Kt hQB hτc hτm hMN hCN J hJ h l Fsel n
      hn a xs hxs hform X Aw Iw hAw hr hD1 hu0 hu1 hpow hK hkJ hEC hNB hδ2 hτc0 hτm0 hCN0 hcard
      hS0 hP0 hσ0 hσ hne
end SideInput

end ActiveSetup.BasicFamilies.FamParams

/-! ## Moments of the core torus sizes over the failure histories (blueprint lines 2569-2577) -/

open Classical in
/-- `role_moments` with an arbitrary constant `c`: if for every word `w ∈ H^n` the role size is at
most `c (Σ_K b_K)^{1/2}` over the `K ∈ T` failing at all heights assigned to the role, and every
`K ∈ T` is bad at a proportion at most `ρ` of `H`, then `A(w) ≤ c (Σ_T b)^{1/2}` and the word
average of `A²` is at most `c² ρ^{n_j} Σ_T b`. -/
theorem role_moments_of_le {κ : Type*} {m₀ : ℕ} (H : Finset ℕ) (good : ℕ → κ → Prop)
    (T : Finset κ) (b : κ → ℝ) (hb : ∀ K ∈ T, 0 ≤ b K) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hbad : ∀ K ∈ T, ((H.filter fun h => ¬ good h K).card : ℝ) ≤ ρ * H.card) {n : ℕ}
    (a : Fin n → Fin m₀) (j : Fin m₀) (A : (Fin n → ℕ) → ℝ) (hA0 : ∀ w, 0 ≤ A w) {c : ℝ}
    (hc : 0 ≤ c)
    (hA : ∀ w ∈ Fintype.piFinset (fun _ : Fin n => H), A w ≤
      c * Real.sqrt (∑ K ∈ T.filter (fun K => ∀ i, a i = j → ¬ good (w i) K), b K)) :
    (∀ w ∈ Fintype.piFinset (fun _ : Fin n => H), A w ≤ c * Real.sqrt (∑ K ∈ T, b K)) ∧
      ∑ w ∈ Fintype.piFinset (fun _ : Fin n => H), ((H.card : ℝ) ^ n)⁻¹ * A w ^ 2 ≤
        c ^ 2 * ρ ^ (Finset.univ.filter fun i => a i = j).card * ∑ K ∈ T, b K := by
  set W := Fintype.piFinset (fun _ : Fin n => H)
  have hT0 : 0 ≤ ∑ K ∈ T, b K := Finset.sum_nonneg hb
  have hfilt : ∀ w : Fin n → ℕ, ∑ K ∈ T.filter (fun K => ∀ i, a i = j → ¬ good (w i) K), b K ≤
      ∑ K ∈ T, b K := fun w => Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    fun K hK _ => hb K hK
  have hsq : ∀ w ∈ W, A w ^ 2 ≤
      c ^ 2 * ∑ K ∈ T.filter (fun K => ∀ i, a i = j → ¬ good (w i) K), b K := by
    intro w hw
    have h0 : 0 ≤ ∑ K ∈ T.filter (fun K => ∀ i, a i = j → ¬ good (w i) K), b K :=
      Finset.sum_nonneg fun K hK => hb K (Finset.mem_filter.mp hK).1
    calc A w ^ 2 ≤ (c * Real.sqrt (∑ K ∈ T.filter
          (fun K => ∀ i, a i = j → ¬ good (w i) K), b K)) ^ 2 :=
          pow_le_pow_left₀ (hA0 w) (hA w hw) 2
      _ = _ := by rw [mul_pow, Real.sq_sqrt h0]
  refine ⟨fun w hw => (hA w hw).trans (mul_le_mul_of_nonneg_left
    (Real.sqrt_le_sqrt (hfilt w)) hc), ?_⟩
  have hmom := mask_second_moment (m₀ := m₀) H good T b hb hbad a j
  by_cases hcz : (H.card : ℝ) ^ n = 0
  · rw [hcz, inv_zero]
    simp only [zero_mul, Finset.sum_const_zero]
    exact mul_nonneg (mul_nonneg (sq_nonneg c) (pow_nonneg hρ _)) hT0
  · calc ∑ w ∈ W, ((H.card : ℝ) ^ n)⁻¹ * A w ^ 2 ≤
        ∑ w ∈ W, ((H.card : ℝ) ^ n)⁻¹ * (c ^ 2 * ∑ K ∈ T.filter
          (fun K => ∀ i, a i = j → ¬ good (w i) K), b K) :=
          Finset.sum_le_sum fun w hw => mul_le_mul_of_nonneg_left (hsq w hw) (by positivity)
      _ = c ^ 2 * ((H.card : ℝ) ^ n)⁻¹ * ∑ w ∈ W, ∑ K ∈ T.filter
          (fun K => ∀ i, a i = j → ¬ good (w i) K), b K := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun w _ => by ring
      _ ≤ c ^ 2 * ((H.card : ℝ) ^ n)⁻¹ * (ρ ^ (Finset.univ.filter fun i => a i = j).card *
          (H.card : ℝ) ^ n * ∑ K ∈ T, b K) := by gcongr
      _ = _ := by field_simp

namespace ModeSystem
variable {Gd : RealDyadicGrid} {Mc : ℕ} (Ms : ModeSystem Gd Mc) (S : ModeSchedule)
  (hA : 6 ≤ S.A0) (SP : SideParams)

theorem allComps_of_coreComps {b : ℤ} {J : ℤ × ℤ} {K : Finset Ms.Md}
    (hK : K ∈ Ms.coreComps S hA SP b J) : K ∈ Ms.allComps S hA b J :=
  (Finset.mem_sdiff.mp hK).1

open Classical in
/-- The minimal PRE component of a core mode is a core component. -/
theorem mem_coreComps_of_core {b : ℤ} {J : ℤ × ℤ} {z : Ms.alive (ancAt Gd J (b - 4 * S.K))}
    (hz : (Ms.blockComps S hA b J).Core SP.Δ (Ms.goodP S SP b) SP.Jst SP.δs z) :
    ((Ms.blockComps S hA b J).E 0 z).map ⟨Subtype.val, Subtype.val_injective⟩ ∈
      Ms.coreComps S hA SP b J := by
  set C := Ms.blockComps S hA b J
  refine Finset.mem_sdiff.mpr ⟨Finset.mem_image_of_mem _ (Finset.mem_univ z), fun hs => ?_⟩
  obtain ⟨x, hx, hxz⟩ := Finset.mem_image.mp hs
  have hE : C.E 0 x = C.E 0 z := Finset.map_injective _ hxz
  have hzx : z ∈ C.E 0 x := hE ▸ C.E_self 0 z
  simp only [sideModes, Finset.mem_filter] at hx
  exact hx.2 ((C.core_iff_of_minimal_pre SP.Δ (Ms.goodP S SP b) SP.Jst SP.δs hzx).mpr hz)

open Classical in
/-- The modes of a core component are core. -/
theorem isCoreAt_of_mem_coreComps {b : ℤ} {J : ℤ × ℤ} {K : Finset Ms.Md}
    (hK : K ∈ Ms.coreComps S hA SP b J) {z : Ms.alive (ancAt Gd J (b - 4 * S.K))}
    (hz : z.1 ∈ K) : Ms.IsCoreAt S hA SP b J z.1 := by
  obtain ⟨x, rfl, hx⟩ := Ms.coreComps_rep S hA SP hK
  obtain ⟨y, hy, hyz⟩ := Finset.mem_map.mp hz
  have : y = z := Subtype.val_injective hyz
  subst this
  exact ⟨y.2, ((Ms.blockComps S hA b J).core_iff_of_minimal_pre SP.Δ (Ms.goodP S SP b) SP.Jst
    SP.δs hy).mp hx⟩

open Classical in
/-- A minimal component lies in the minimal CURRENT component of any of its modes. -/
theorem subset_F_zero_of_mem {b : ℤ} {J : ℤ × ℤ} {K : Finset Ms.Md}
    (hK : K ∈ Ms.allComps S hA b J) {y : Ms.alive (ancAt Gd J (b - 4 * S.K))} (hy : y.1 ∈ K) :
    K ⊆ ((Ms.blockComps S hA b J).F 0 y).map ⟨Subtype.val, Subtype.val_injective⟩ := by
  set C := Ms.blockComps S hA b J
  obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hK
  obtain ⟨y', hy', hyy'⟩ := Finset.mem_map.mp hy
  have : y' = y := Subtype.val_injective hyy'
  subst this
  intro m hm
  obtain ⟨z, hz, rfl⟩ := Finset.mem_map.mp hm
  refine Finset.mem_map_of_mem _ (C.E_le_F 0 y' ?_)
  rw [C.E_comp 0 x y' hy']
  exact hz

open Classical in
/-- A minimal component inside a minimal CURRENT component has that component as its class at
height `0`. -/
theorem compClass_zero_of_subset {b : ℤ} {J : ℤ × ℤ} {K : Finset Ms.Md}
    (hK : K ∈ Ms.allComps S hA b J) {y : Ms.alive (ancAt Gd J (b - 4 * S.K))}
    (hKU : K ⊆ ((Ms.blockComps S hA b J).F 0 y).map ⟨Subtype.val, Subtype.val_injective⟩) :
    Ms.compClass S hA b J 0 K =
      ((Ms.blockComps S hA b J).F 0 y).map ⟨Subtype.val, Subtype.val_injective⟩ := by
  set C := Ms.blockComps S hA b J
  obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hK
  have hx : x.1 ∈ (C.E 0 x).map ⟨Subtype.val, Subtype.val_injective⟩ :=
    Finset.mem_map_of_mem _ (C.E_self 0 x)
  obtain ⟨x', hx', hxx'⟩ := Finset.mem_map.mp (hKU hx)
  have : x' = x := Subtype.val_injective hxx'
  subst this
  rw [Ms.compClass_eq S hA b J 0 x', C.F_comp 0 y x' hx']

open Classical in
/-- Blueprint lines 2569-2572 ("apply the probability bound separately to each minimal-component
summand in `eq:torus-size`"): when the selected modes `F` are the core modes of entire minimal
CURRENT components inside `F_h(x)`, each satisfying `P`, the sum of `eq:torus-size` is at most the
sum of the summands of `eq:component-size` over the minimal CURRENT components satisfying `P`. -/
theorem selComps_sum_le_filter {b : ℤ} {J : ℤ × ℤ} (I : ℤ × ℤ) {h : ℕ}
    {x : Ms.alive (ancAt Gd J (b - 4 * S.K))} (F : Finset (Ms.alive (ancAt Gd J (b - 4 * S.K))))
    (P : Finset Ms.Md → Prop) [DecidablePred P] (hFh : ∀ y ∈ F, y ∈ (Ms.blockComps S hA b J).F h x)
    (hunit : ∀ y ∈ F, ∀ z ∈ (Ms.blockComps S hA b J).F 0 y, z ∈ F ↔ Ms.IsCoreAt S hA SP b J z.1)
    (hP : ∀ y ∈ F, P (((Ms.blockComps S hA b J).F 0 y).map ⟨Subtype.val, Subtype.val_injective⟩))
    (c : Ms.Md → ℂ) :
    ∑ E ∈ Ms.selComps S hA b J F,
        (‖∑ m ∈ E, c m • Ms.cellMode I m‖ / Real.sqrt (dyadicGridLength Gd I.1) +
          (S.Dstar ^ 30)⁻¹ * ∑ m ∈ E, ‖c m‖) ^ 2 ≤
      ∑ U ∈ (Ms.minComps S hA b J h x).filter P,
        (‖∑ m ∈ U.filter (Ms.IsCoreAt S hA SP b J), c m • Ms.cellMode I m‖ /
            Real.sqrt (dyadicGridLength Gd I.1) +
          (S.Dstar ^ 30)⁻¹ * ∑ m ∈ U.filter (Ms.IsCoreAt S hA SP b J), ‖c m‖) ^ 2 := by
  set C := Ms.blockComps S hA b J
  set f : Finset Ms.Md → ℝ := fun E =>
    (‖∑ m ∈ E, c m • Ms.cellMode I m‖ / Real.sqrt (dyadicGridLength Gd I.1) +
      (S.Dstar ^ 30)⁻¹ * ∑ m ∈ E, ‖c m‖) ^ 2 with hf
  have hsub : Ms.selComps S hA b J F ⊆
      ((Ms.minComps S hA b J h x).filter P).image
        fun U => U.filter (Ms.IsCoreAt S hA SP b J) := by
    intro E hE
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hE
    refine Finset.mem_image.mpr ⟨(C.F 0 y).map ⟨Subtype.val, Subtype.val_injective⟩,
      Finset.mem_filter.mpr ⟨(Ms.mem_minComps S hA).mpr ⟨y, hFh y hy, rfl⟩, hP y hy⟩, ?_⟩
    ext m
    simp only [Finset.mem_filter, Finset.mem_map, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨⟨z, hz, rfl⟩, hcore⟩
      exact ⟨z, ⟨(hunit y hy z hz).mpr hcore, hz⟩, rfl⟩
    · rintro ⟨z, ⟨hzF, hz⟩, rfl⟩
      exact ⟨⟨z, hz, rfl⟩, (hunit y hy z hz).mp hzF⟩
  calc ∑ E ∈ Ms.selComps S hA b J F, f E ≤
        ∑ E ∈ ((Ms.minComps S hA b J h x).filter P).image
          (fun U => U.filter (Ms.IsCoreAt S hA SP b J)), f E :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => sq_nonneg _
    _ ≤ ∑ U ∈ (Ms.minComps S hA b J h x).filter P, f (U.filter (Ms.IsCoreAt S hA SP b J)) :=
        Finset.sum_image_le_of_nonneg fun _ _ => sq_nonneg _

end ModeSystem

namespace ActiveSetup.BasicFamilies.FamParams
variable {κ' : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ' c₀} {bf : A.BasicFamilies}
  {fp : bf.FamParams}

namespace SideInput
variable (D : fp.SideInput)

open Classical in
/-- The components of a core slot at a cell are the core components of its pre-cell. -/
theorem mem_compsAt {l : Fin 4} {G : bf.Grp} {I : ℤ × ℤ} {K : Finset (D.Ms l G).Md}
    (hK : K ∈ D.compsAt l G I) :
    K ∈ (D.Ms l G).coreComps D.S D.hA D.SP (A.blkStart D.S.K I.1) (D.preAt I) ∧
      D.compsAt l G I =
        (D.Ms l G).coreComps D.S D.hA D.SP (A.blkStart D.S.K I.1) (D.preAt I) := by
  unfold compsAt at hK ⊢
  split_ifs at hK ⊢ with hc
  · exact ⟨hK, rfl⟩
  · simp at hK

/-- The final class `F_h(m)` of a mode of the role `j` (blueprint line 2467), as a set of
modes. -/
noncomputable def finCls (G : bf.Grp) (I : ℤ × ℤ) (j : Fin 4) (h : ℕ)
    (m : (D.Ms j G).alive (ancAt A.G (D.preAt I) (A.blkStart D.S.K I.1 - 4 * D.S.K))) :
    Finset (D.Ms j G).Md :=
  (((D.Ms j G).blockComps D.S D.hA (A.blkStart D.S.K I.1) (D.preAt I)).F h m).map
    ⟨Subtype.val, Subtype.val_injective⟩

open Classical in
/-- The masked components of a core role `j` with final class `F` (blueprint lines 2466-2467 and
2569): the core components of the cell in the role mask of the assignment `asg` of the failed
trials, the failed word `w` and the final height `h`, whose final class at `h` is `F`. -/
noncomputable def maskComps (G : bf.Grp) (I : ℤ × ℤ) (j : Fin 4) {n : ℕ} (asg : Fin n → Fin 4)
    (w : Fin n → ℕ) (h : ℕ) (F : Finset (D.Ms j G).Md) : Finset (Finset (D.Ms j G).Md) :=
  (D.compsAt j G I).filter fun K =>
    roleMask (D.slotGood G I j) j asg w h (some K) ∧ D.coreCls G I h j (some K) = F

open Classical in
/-- The selected modes of a core role with final class `F` (blueprint line 2569): the alive modes
of its masked components. -/
noncomputable def maskSel (G : bf.Grp) (I : ℤ × ℤ) (j : Fin 4) {n : ℕ} (asg : Fin n → Fin 4)
    (w : Fin n → ℕ) (h : ℕ) (F : Finset (D.Ms j G).Md) :
    Finset ((D.Ms j G).alive (ancAt A.G (D.preAt I) (A.blkStart D.S.K I.1 - 4 * D.S.K))) :=
  Finset.univ.filter fun x => ∃ K ∈ D.maskComps G I j asg w h F, x.1 ∈ K

open Classical in
/-- The goodness at a height `t` of a minimal CURRENT component `U` of a core role: every core
component of the cell inside `U` is good at `t`. -/
def unitGood (G : bf.Grp) (I : ℤ × ℤ) (j : Fin 4) (t : ℕ) (U : Finset (D.Ms j G).Md) : Prop :=
  ∀ K ∈ D.compsAt j G I, K ⊆ U → D.slotGood G I j t (some K)

open Classical in
/-- The summand of `eq:component-size` of a minimal CURRENT component `U` of the role `j`:
`(‖A_U‖_{2,I} + D_*^{-30} Σ_{m core in U} |α_m|)²`. -/
noncomputable def unitSizeSq (G : bf.Grp) (I : ℤ × ℤ) (j : Fin 4) (U : Finset (D.Ms j G).Md) :
    ℝ :=
  (‖∑ m ∈ U.filter ((D.Ms j G).IsCoreAt D.S D.hA D.SP (A.blkStart D.S.K I.1) (D.preAt I)),
      D.c j G (A.blkStart D.S.K I.1) (D.preAt I) m • (D.Ms j G).cellMode I m‖ /
      Real.sqrt (dyadicGridLength A.G I.1) +
    (D.S.Dstar ^ 30)⁻¹ * ∑ m ∈ U.filter
      ((D.Ms j G).IsCoreAt D.S D.hA D.SP (A.blkStart D.S.K I.1) (D.preAt I)),
        ‖D.c j G (A.blkStart D.S.K I.1) (D.preAt I) m‖) ^ 2

/-- The torus form `eq:core-torus-form` of selected modes `F` of the role `j` at the torus height
`h'` and the point `x*`, with shifts `n` and anchor mode `a`: shifts at most `D_* E_{h'}` and
error at most `D_*^{-150}` times the absolute coefficient sum. -/
def TorusFormAt (G : bf.Grp) (I : ℤ × ℤ) (j : Fin 4) (h' : ℕ) (xs : ℝ)
    (F : Finset ((D.Ms j G).alive (ancAt A.G (D.preAt I) (A.blkStart D.S.K I.1 - 4 * D.S.K))))
    (n : (D.Ms j G).alive (ancAt A.G (D.preAt I) (A.blkStart D.S.K I.1 - 4 * D.S.K)) →
      Fin (D.Ms j G).zc.dim → ℤ)
    (a : (D.Ms j G).alive (ancAt A.G (D.preAt I) (A.blkStart D.S.K I.1 - 4 * D.S.K))) : Prop :=
  (∀ x ∈ F, ∀ i, |(n x i : ℝ)| ≤ D.S.Dstar * D.S.Eh h') ∧
    ∀ y ∈ dyadicGridCell A.G I.1 I.2,
      ‖∑ x ∈ F, D.c j G (A.blkStart D.S.K I.1) (D.preAt I) x.1 * (D.Ms j G).wave x.1 y -
        (Real.fourierChar (((D.Ms j G).cl : ℝ) * centerPhase (D.Ms j G).zc (D.Ms j G).ρ y) : ℂ) *
          (Real.fourierChar ((D.Ms j G).slope a.1 xs * (y - xs)) : ℂ) *
          (D.Ms j G).torusG D.S h' xs F
            (fun x => D.c j G (A.blkStart D.S.K I.1) (D.preAt I) x.1) n
            (fun i => (D.Ms j G).torusξ D.S h' i * (y - xs))‖ ≤
        (D.S.Dstar ^ 150)⁻¹ * ∑ x ∈ F, ‖D.c j G (A.blkStart D.S.K I.1) (D.preAt I) x.1‖

open Classical in
/-- Blueprint lines 2466-2467 and 2569 for the masked selection: the selected modes of a core role
with the final class `F_h(m)` lie in `F_h(m)`, and they are the core modes of entire minimal
CURRENT components (the masks select whole units, `roleMask_iff_of_same_unit`). -/
theorem maskSel_units (hstab : D.Stab) (G : bf.Grp) (I : ℤ × ℤ) (j : Fin 4)
    (hJ : 2 ≤ D.SP.Jst) (hδ : 0 < D.SP.δs) (hδJ : ⌈4 * D.SP.δs * D.SP.Jst⌉₊ ≤ D.SP.Jst)
    {n : ℕ} (asg : Fin n → Fin 4) {w : Fin n → ℕ}
    (hw : ∀ i, w i ∈ ModeComponents.upperHeights D.SP.Jst D.SP.δs) {h : ℕ}
    (hh : h ∈ ModeComponents.upperHeights D.SP.Jst D.SP.δs)
    (m : (D.Ms j G).alive (ancAt A.G (D.preAt I) (A.blkStart D.S.K I.1 - 4 * D.S.K))) :
    (∀ y ∈ D.maskSel G I j asg w h (D.finCls G I j h m),
      y ∈ ((D.Ms j G).blockComps D.S D.hA (A.blkStart D.S.K I.1) (D.preAt I)).F h m) ∧
    ∀ y ∈ D.maskSel G I j asg w h (D.finCls G I j h m),
      ∀ z ∈ ((D.Ms j G).blockComps D.S D.hA (A.blkStart D.S.K I.1) (D.preAt I)).F 0 y,
        z ∈ D.maskSel G I j asg w h (D.finCls G I j h m) ↔
          (D.Ms j G).IsCoreAt D.S D.hA D.SP (A.blkStart D.S.K I.1) (D.preAt I) z.1 := by
  set C := (D.Ms j G).blockComps D.S D.hA (A.blkStart D.S.K I.1) (D.preAt I) with hC
  have hsel : ∀ y ∈ D.maskSel G I j asg w h (D.finCls G I j h m),
      ∃ K ∈ D.maskComps G I j asg w h (D.finCls G I j h m), y.1 ∈ K :=
    fun y hy => (Finset.mem_filter.mp hy).2
  refine ⟨fun y hy => ?_, fun y hy z hz => ?_⟩
  · obtain ⟨K, hK, hyK⟩ := hsel y hy
    obtain ⟨hKc, -, hcls⟩ := Finset.mem_filter.mp hK
    have hKall := (D.Ms j G).allComps_of_coreComps D.S D.hA D.SP (D.mem_compsAt hKc).1
    have e := (D.Ms j G).compClass_eq_of_mem D.S D.hA _ _ h hKall hyK
    have hF : C.F h y = C.F h m := Finset.map_injective _ (e.symm.trans hcls)
    rw [← hF]
    exact C.mem_F_self h y
  · obtain ⟨K, hK, hyK⟩ := hsel y hy
    obtain ⟨hKc, hmask, hcls⟩ := Finset.mem_filter.mp hK
    obtain ⟨hKcore, hcomps⟩ := D.mem_compsAt hKc
    constructor
    · intro hz'
      obtain ⟨K', hK', hzK'⟩ := hsel z hz'
      exact (D.Ms j G).isCoreAt_of_mem_coreComps D.S D.hA D.SP
        (D.mem_compsAt (Finset.mem_filter.mp hK').1).1 hzK'
    · rintro ⟨hm', hcore⟩
      have hK'core := (D.Ms j G).mem_coreComps_of_core D.S D.hA D.SP hcore
      have hcls0 : (D.Ms j G).compClass D.S D.hA (A.blkStart D.S.K I.1) (D.preAt I) 0 K =
          (D.Ms j G).compClass D.S D.hA (A.blkStart D.S.K I.1) (D.preAt I) 0
            ((C.E 0 z).map ⟨Subtype.val, Subtype.val_injective⟩) := by
        rw [(D.Ms j G).compClass_eq_of_mem D.S D.hA _ _ 0
            ((D.Ms j G).allComps_of_coreComps D.S D.hA D.SP hKcore) hyK,
          (D.Ms j G).compClass_eq D.S D.hA _ _ 0 z, C.F_comp 0 y z hz]
      obtain ⟨hiff, hclsh⟩ := D.roleMask_iff_of_same_unit hstab G I j hJ hδ hδJ hKcore hK'core
        hcls0 asg hw hh
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, (C.E 0 z).map
        ⟨Subtype.val, Subtype.val_injective⟩, ?_, Finset.mem_map_of_mem _ (C.E_self 0 z)⟩
      refine Finset.mem_filter.mpr ⟨?_, hiff.mp hmask, hclsh.symm.trans hcls⟩
      rw [hcomps]
      exact hK'core

open Classical in
/-- Blueprint line 2466 for minimal CURRENT components: on the upper heights a minimal CURRENT
component of a core role is bad at a proportion at most `2δ_*` (its core components share their
good predicates, `compGood_iff_of_same_class_le`, `coreComp_bad_card`). -/
theorem unitGood_bad_card (hstab : D.Stab) (G : bf.Grp) (I : ℤ × ℤ) (j : Fin 4)
    (hJ : 2 ≤ D.SP.Jst) (hδ : 0 < D.SP.δs) (hδ16 : D.SP.δs ≤ 1 / 16)
    (hδJ : ⌈4 * D.SP.δs * D.SP.Jst⌉₊ ≤ D.SP.Jst)
    (y : (D.Ms j G).alive (ancAt A.G (D.preAt I) (A.blkStart D.S.K I.1 - 4 * D.S.K))) :
    (((ModeComponents.upperHeights D.SP.Jst D.SP.δs).filter fun t => ¬ D.unitGood G I j t
      ((((D.Ms j G).blockComps D.S D.hA (A.blkStart D.S.K I.1) (D.preAt I)).F 0 y).map
        ⟨Subtype.val, Subtype.val_injective⟩)).card : ℝ) ≤
      2 * D.SP.δs * (ModeComponents.upperHeights D.SP.Jst D.SP.δs).card := by
  set C := (D.Ms j G).blockComps D.S D.hA (A.blkStart D.S.K I.1) (D.preAt I) with hC
  set H := ModeComponents.upperHeights D.SP.Jst D.SP.δs
  by_cases hex : ∃ K₀ ∈ D.compsAt j G I,
      K₀ ⊆ (C.F 0 y).map ⟨Subtype.val, Subtype.val_injective⟩
  · obtain ⟨K₀, hK₀, hK₀U⟩ := hex
    have hK₀c := (D.mem_compsAt hK₀).1
    refine le_trans ?_ ((D.Ms j G).coreComp_bad_card D.S D.hA D.SP hK₀c hJ hδ hδ16)
    refine Nat.cast_le.mpr (Finset.card_le_card fun t ht => ?_)
    obtain ⟨htH, hng⟩ := Finset.mem_filter.mp ht
    refine Finset.mem_filter.mpr ⟨htH, fun hg0 => hng fun K hK hKU => ?_⟩
    have hKc := (D.mem_compsAt hK).1
    have hcls : (D.Ms j G).compClass D.S D.hA (A.blkStart D.S.K I.1) (D.preAt I) 0 K₀ =
        (D.Ms j G).compClass D.S D.hA (A.blkStart D.S.K I.1) (D.preAt I) 0 K := by
      rw [(D.Ms j G).compClass_zero_of_subset D.S D.hA
          ((D.Ms j G).allComps_of_coreComps D.S D.hA D.SP hK₀c) hK₀U,
        (D.Ms j G).compClass_zero_of_subset D.S D.hA
          ((D.Ms j G).allComps_of_coreComps D.S D.hA D.SP hKc) hKU]
    exact ((D.Ms j G).compGood_iff_of_same_class_le D.S D.hA D.SP (hstab j G I) hJ hδ hδJ hK₀c
      hKc hcls t htH).mp hg0
  · have h0 : H.filter (fun t => ¬ D.unitGood G I j t
        ((C.F 0 y).map ⟨Subtype.val, Subtype.val_injective⟩)) = ∅ :=
      Finset.filter_eq_empty_iff.mpr fun t _ hng =>
        hng fun K hK hKU => absurd ⟨K, hK, hKU⟩ hex
    rw [h0, Finset.card_empty, Nat.cast_zero]
    positivity

end SideInput

end ActiveSetup.BasicFamilies.FamParams

namespace ActiveSetup.BasicFamilies.FamParams
variable {κ' : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ' c₀} {bf : A.BasicFamilies}
  {fp : bf.FamParams}

namespace SideInput
variable (D : fp.SideInput)

open Classical in
/-- Blueprint lines 2569-2572 on a leaf cell of the side states: for a final upper height `h`, the
final class `F_h(m)` of a good mode `m` of a core role `j`, an assignment `asg` of the `n` failed
trials and torus forms of the selected modes for all words `w ∈ H^n` (shifts `ns w`, anchor `a`),
the torus sizes `a'_j(w)` of `eq:torus-size` satisfy `a'_j(w) ≤ 6 σ_F` and
`E_w a'_j(w)² ≤ 36 (2δ_*)^{n_j} σ_F²`, with `n_j` the number of trials assigned to `j` and
`σ_F² = compSizeSq` (`eq:component-size`): each minimal-component summand of `eq:torus-size`
requires its unit to fail at the `n_j` heights assigned to `j`, which has probability at most
`(2δ_*)^{n_j}` (the other success requirements are dropped). -/
theorem role_size_moments {Cj CA CT CK : ℕ} {δs W : ℝ} (hV : D.S.Valid Cj CA CT CK δs W)
    (hCA : 1 ≤ CA) (hCT : 4 ≤ CT) (hd2 : 2 ≤ D.S.dmax) (hD : 2 ≤ D.S.Dstar) (hB : 2 ≤ D.S.Bstar)
    (hQ : 1 ≤ D.S.Q0) (hSP : D.SP = D.S.sideParams δs) (hstab : D.Stab) (I : ℤ × ℤ) (j : Fin 4)
    (G : bf.Grp) (hdim : (D.Ms j G).zc.dim ≤ D.S.dmax) (hδc : 0 < (D.Ms j G).δc)
    (hDg : gaugeSqNorm (D.Ms j G).zc.dim (D.Ms j G).δc ≤ D.S.Dstar) {Kf : ℕ}
    (hKf : 2 * gaugeTail (D.Ms j G).zc.dim (D.Ms j G).δc / 2 ^ Kf * D.S.Dstar ^ 300 ≤ 1)
    (hQB : (D.S.Q0 : ℝ) * 2 ^ (Kf + 1) ≤ D.S.Bstar)
    (hεw : ∀ m, D.S.Dstar⁻¹ ≤ (D.Ms j G).L.εM m)
    (hcard : (((D.Ms j G).alive (ancAt A.G (D.preAt I)
      (A.blkStart D.S.K I.1 - 4 * D.S.K))).card : ℝ) ≤ D.S.Dstar)
    (hΛ : (D.Ms j G).Λ ≤ D.S.Dstar) (hJ : 2 ≤ D.SP.Jst) (hδ : 0 < D.SP.δs)
    (hδ16 : D.SP.δs ≤ 1 / 16) (hδJ : ⌈4 * D.SP.δs * D.SP.Jst⌉₊ ≤ D.SP.Jst) {h : ℕ}
    (hh : h ∈ ModeComponents.upperHeights D.SP.Jst D.SP.δs)
    {m : (D.Ms j G).alive (ancAt A.G (D.preAt I) (A.blkStart D.S.K I.1 - 4 * D.S.K))}
    (hgood : ((D.Ms j G).blockComps D.S D.hA (A.blkStart D.S.K I.1) (D.preAt I)).Good D.SP.Δ
      ((D.Ms j G).goodP D.S D.SP (A.blkStart D.S.K I.1)) h m) {n : ℕ} (asg : Fin n → Fin 4)
    (ns : (Fin n → ℕ) → (D.Ms j G).alive (ancAt A.G (D.preAt I)
      (A.blkStart D.S.K I.1 - 4 * D.S.K)) → Fin (D.Ms j G).zc.dim → ℤ)
    (a : (D.Ms j G).alive (ancAt A.G (D.preAt I) (A.blkStart D.S.K I.1 - 4 * D.S.K)))
    {xs : ℝ} (hxs : xs ∈ dyadicGridCell A.G I.1 I.2)
    (hform : ∀ w ∈ Fintype.piFinset
      (fun _ : Fin n => ModeComponents.upperHeights D.SP.Jst D.SP.δs),
      D.TorusFormAt G I j (h - D.SP.Δ) xs (D.maskSel G I j asg w h (D.finCls G I j h m))
        (ns w) a) :
    (∀ w ∈ Fintype.piFinset (fun _ : Fin n => ModeComponents.upperHeights D.SP.Jst D.SP.δs),
      D.coreSize G I xs (h - D.SP.Δ) j (D.maskSel G I j asg w h (D.finCls G I j h m)) (ns w) ≤
        6 * Real.sqrt ((D.Ms j G).compSizeSq D.S D.hA D.SP I (A.blkStart D.S.K I.1) (D.preAt I) h
          m (D.c j G (A.blkStart D.S.K I.1) (D.preAt I)))) ∧
    ∑ w ∈ Fintype.piFinset (fun _ : Fin n => ModeComponents.upperHeights D.SP.Jst D.SP.δs),
      (((ModeComponents.upperHeights D.SP.Jst D.SP.δs).card : ℝ) ^ n)⁻¹ *
        D.coreSize G I xs (h - D.SP.Δ) j (D.maskSel G I j asg w h (D.finCls G I j h m))
          (ns w) ^ 2 ≤
      36 * (2 * D.SP.δs) ^ (Finset.univ.filter fun i => asg i = j).card *
        (D.Ms j G).compSizeSq D.S D.hA D.SP I (A.blkStart D.S.K I.1) (D.preAt I) h m
          (D.c j G (A.blkStart D.S.K I.1) (D.preAt I)) := by
  have hhJ : h ≤ D.SP.Jst := by
    have := (Finset.mem_filter.mp hh).1
    rw [Finset.mem_range] at this
    omega
  have hbad : ∀ U ∈ (D.Ms j G).minComps D.S D.hA (A.blkStart D.S.K I.1) (D.preAt I) h m,
      (((ModeComponents.upperHeights D.SP.Jst D.SP.δs).filter
        fun t => ¬ D.unitGood G I j t U).card : ℝ) ≤
        2 * D.SP.δs * (ModeComponents.upperHeights D.SP.Jst D.SP.δs).card := by
    intro U hU
    obtain ⟨y, -, rfl⟩ := ((D.Ms j G).mem_minComps D.S D.hA).mp hU
    exact D.unitGood_bad_card hstab G I j hJ hδ hδ16 hδJ y
  have hsize : ∀ w ∈ Fintype.piFinset
      (fun _ : Fin n => ModeComponents.upperHeights D.SP.Jst D.SP.δs),
      D.coreSize G I xs (h - D.SP.Δ) j (D.maskSel G I j asg w h (D.finCls G I j h m)) (ns w) ≤
        6 * Real.sqrt (∑ U ∈ ((D.Ms j G).minComps D.S D.hA (A.blkStart D.S.K I.1)
          (D.preAt I) h m).filter (fun U => ∀ i, asg i = j → ¬ D.unitGood G I j (w i) U),
          D.unitSizeSq G I j U) := by
    intro w hw
    obtain ⟨hFh, hunit⟩ := D.maskSel_units hstab G I j hJ hδ hδJ asg
      (Fintype.mem_piFinset.mp hw) hh m
    refine (D.torus_size hV hCA hCT hd2 hD hB hQ hSP I j G hdim hδc hDg hKf hQB hεw hcard hΛ hhJ
      hgood _ (ns w) (hform w hw).1 a hxs (hform w hw).2).trans
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt ?_) (by norm_num))
    refine (D.Ms j G).selComps_sum_le_filter D.S D.hA D.SP I _
      (fun U => ∀ i, asg i = j → ¬ D.unitGood G I j (w i) U) hFh hunit (fun y hy => ?_)
      (D.c j G (A.blkStart D.S.K I.1) (D.preAt I))
    obtain ⟨K, hK, hyK⟩ := (Finset.mem_filter.mp hy).2
    obtain ⟨hKc, hmask, -⟩ := Finset.mem_filter.mp hK
    intro i hi hg
    exact hmask.2.1 i hi (hg K hKc ((D.Ms j G).subset_F_zero_of_mem D.S D.hA
      ((D.Ms j G).allComps_of_coreComps D.S D.hA D.SP (D.mem_compsAt hKc).1) hyK))
  have hdet : ∀ w ∈ Fintype.piFinset
      (fun _ : Fin n => ModeComponents.upperHeights D.SP.Jst D.SP.δs),
      D.coreSize G I xs (h - D.SP.Δ) j (D.maskSel G I j asg w h (D.finCls G I j h m)) (ns w) ≤
        6 * Real.sqrt ((D.Ms j G).compSizeSq D.S D.hA D.SP I (A.blkStart D.S.K I.1) (D.preAt I)
          h m (D.c j G (A.blkStart D.S.K I.1) (D.preAt I))) := by
    intro w hw
    obtain ⟨hFh, hunit⟩ := D.maskSel_units hstab G I j hJ hδ hδJ asg
      (Fintype.mem_piFinset.mp hw) hh m
    exact D.torus_size_compSize hV hCA hCT hd2 hD hB hQ hSP I j G hdim hδc hDg hKf hQB hεw hcard
      hΛ hhJ hgood _ hFh hunit (ns w) (hform w hw).1 a hxs (hform w hw).2
  obtain ⟨-, hsq⟩ := role_moments_of_le (ModeComponents.upperHeights D.SP.Jst D.SP.δs)
    (D.unitGood G I j) ((D.Ms j G).minComps D.S D.hA (A.blkStart D.S.K I.1) (D.preAt I) h m)
    (D.unitSizeSq G I j) (fun U _ => sq_nonneg _) (by linarith : (0 : ℝ) ≤ 2 * D.SP.δs) hbad asg
    j (fun w => D.coreSize G I xs (h - D.SP.Δ) j (D.maskSel G I j asg w h (D.finCls G I j h m))
      (ns w)) (fun w => D.coreSize_nonneg _ _ _ _ _ _ _) (by norm_num : (0 : ℝ) ≤ 6) hsize
  refine ⟨hdet, hsq.trans (le_of_eq ?_)⟩
  have e : ∑ U ∈ (D.Ms j G).minComps D.S D.hA (A.blkStart D.S.K I.1) (D.preAt I) h m,
      D.unitSizeSq G I j U = (D.Ms j G).compSizeSq D.S D.hA D.SP I (A.blkStart D.S.K I.1)
        (D.preAt I) h m (D.c j G (A.blkStart D.S.K I.1) (D.preAt I)) := rfl
  rw [e]
  norm_num

end SideInput

end ActiveSetup.BasicFamilies.FamParams

/-! ## The principal core contributions (blueprint `eq:principal-core`, lines 2577-2582) -/

namespace ActiveSetup.BasicFamilies.FamParams
variable {κ' : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ' c₀} {bf : A.BasicFamilies}
  {fp : bf.FamParams}

namespace SideInput
variable (D : fp.SideInput)

open Classical in
/-- The minimal CURRENT components inside a final class `F` of the role `j` (the summation units of
`eq:component-size`). -/
noncomputable def clsUnits (G : bf.Grp) (I : ℤ × ℤ) (j : Fin 4) (F : Finset (D.Ms j G).Md) :
    Finset (Finset (D.Ms j G).Md) :=
  (Finset.univ.filter fun y : (D.Ms j G).alive (ancAt A.G (D.preAt I)
      (A.blkStart D.S.K I.1 - 4 * D.S.K)) => y.1 ∈ F).image fun y =>
    (((D.Ms j G).blockComps D.S D.hA (A.blkStart D.S.K I.1) (D.preAt I)).F 0 y).map
      ⟨Subtype.val, Subtype.val_injective⟩

/-- The component size `σ_F` of a final class `F` of the role `j` (blueprint
`eq:component-size`). -/
noncomputable def clsSize (G : bf.Grp) (I : ℤ × ℤ) (j : Fin 4) (F : Finset (D.Ms j G).Md) : ℝ :=
  Real.sqrt (∑ U ∈ D.clsUnits G I j F, D.unitSizeSq G I j U)

theorem clsSize_nonneg (G : bf.Grp) (I : ℤ × ℤ) (j : Fin 4) (F : Finset (D.Ms j G).Md) :
    0 ≤ D.clsSize G I j F :=
  Real.sqrt_nonneg _

open Classical in
/-- The component size of the final class `F_h(m)` is `σ_F = compSizeSq^{1/2}`. -/
theorem clsSize_finCls (G : bf.Grp) (I : ℤ × ℤ) (j : Fin 4) (h : ℕ)
    (m : (D.Ms j G).alive (ancAt A.G (D.preAt I) (A.blkStart D.S.K I.1 - 4 * D.S.K))) :
    D.clsSize G I j (D.finCls G I j h m) = Real.sqrt ((D.Ms j G).compSizeSq D.S D.hA D.SP I
      (A.blkStart D.S.K I.1) (D.preAt I) h m (D.c j G (A.blkStart D.S.K I.1) (D.preAt I))) := by
  have e : D.clsUnits G I j (D.finCls G I j h m) =
      (D.Ms j G).minComps D.S D.hA (A.blkStart D.S.K I.1) (D.preAt I) h m := by
    unfold clsUnits finCls ModeSystem.minComps
    congr 1
    ext y
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨y', hy', hyy'⟩
      rwa [← Subtype.val_injective hyy']
    · intro hy
      exact ⟨y, hy, rfl⟩
  unfold clsSize
  rw [e]
  rfl

open Classical in
/-- A choice of the shifts of the torus form `eq:core-torus-form` of the selected modes of a core
role (any shifts with the torus form, when they exist). -/
noncomputable def maskShift (G : bf.Grp) (I : ℤ × ℤ) (j : Fin 4) {n : ℕ} (asg : Fin n → Fin 4)
    (w : Fin n → ℕ) (h : ℕ) (F : Finset (D.Ms j G).Md) (xs : ℝ)
    (a : (D.Ms j G).alive (ancAt A.G (D.preAt I) (A.blkStart D.S.K I.1 - 4 * D.S.K))) :
    (D.Ms j G).alive (ancAt A.G (D.preAt I) (A.blkStart D.S.K I.1 - 4 * D.S.K)) →
      Fin (D.Ms j G).zc.dim → ℤ :=
  if hx : ∃ ns, D.TorusFormAt G I j (h - D.SP.Δ) xs (D.maskSel G I j asg w h F) ns a then
    hx.choose else fun _ _ => 0

theorem maskShift_spec (G : bf.Grp) (I : ℤ × ℤ) (j : Fin 4) {n : ℕ} (asg : Fin n → Fin 4)
    (w : Fin n → ℕ) (h : ℕ) (F : Finset (D.Ms j G).Md) (xs : ℝ)
    (a : (D.Ms j G).alive (ancAt A.G (D.preAt I) (A.blkStart D.S.K I.1 - 4 * D.S.K)))
    (hx : ∃ ns, D.TorusFormAt G I j (h - D.SP.Δ) xs (D.maskSel G I j asg w h F) ns a) :
    D.TorusFormAt G I j (h - D.SP.Δ) xs (D.maskSel G I j asg w h F)
      (D.maskShift G I j asg w h F xs a) a := by
  unfold maskShift
  simp only [hx, ↓reduceDIte]
  exact hx.choose_spec

/-- The torus size `a'_j` of the selected modes of a core role with the chosen shifts. -/
noncomputable def maskSize (G : bf.Grp) (I : ℤ × ℤ) (j : Fin 4) {n : ℕ} (asg : Fin n → Fin 4)
    (w : Fin n → ℕ) (h : ℕ) (F : Finset (D.Ms j G).Md) (xs : ℝ)
    (a : (D.Ms j G).alive (ancAt A.G (D.preAt I) (A.blkStart D.S.K I.1 - 4 * D.S.K))) : ℝ :=
  D.coreSize G I xs (h - D.SP.Δ) j (D.maskSel G I j asg w h F)
    (D.maskShift G I j asg w h F xs a)

theorem maskSize_nonneg (G : bf.Grp) (I : ℤ × ℤ) (j : Fin 4) {n : ℕ} (asg : Fin n → Fin 4)
    (w : Fin n → ℕ) (h : ℕ) (F : Finset (D.Ms j G).Md) (xs : ℝ)
    (a : (D.Ms j G).alive (ancAt A.G (D.preAt I) (A.blkStart D.S.K I.1 - 4 * D.S.K))) :
    0 ≤ D.maskSize G I j asg w h F xs a :=
  D.coreSize_nonneg _ _ _ _ _ _ _

open Classical in
/-- Blueprint lines 2467-2471 for the masked selection with a given anchor: when every selected
mode lies in the PRE predecessor `E_{h-Δ}(a)` of the anchor, the selected modes have the torus
form `eq:core-torus-form` at `h - Δ` (`cell_torus_form`). -/
theorem maskSel_torus_form_of (G : bf.Grp) (I : ℤ × ℤ) (j : Fin 4) {h : ℕ}
    (hQ : 1 ≤ D.S.Q0) (hD : 2 ≤ D.S.Dstar)
    (hcard : (((D.Ms j G).alive (ancAt A.G (D.preAt I)
      (A.blkStart D.S.K I.1 - 4 * D.S.K))).card : ℝ) ≤ D.S.Dstar)
    (hΛ : (D.Ms j G).Λ ≤ D.S.Dstar) (hK : D.S.Dstar ^ 600 ≤ (2 : ℝ) ^ D.S.K)
    {a : (D.Ms j G).alive (ancAt A.G (D.preAt I) (A.blkStart D.S.K I.1 - 4 * D.S.K))} {n : ℕ}
    (asg : Fin n → Fin 4) (w : Fin n → ℕ) (F : Finset (D.Ms j G).Md) {xs : ℝ}
    (hxs : xs ∈ dyadicGridCell A.G I.1 I.2)
    (hF : ∀ x ∈ D.maskSel G I j asg w h F,
      x ∈ ((D.Ms j G).blockComps D.S D.hA (A.blkStart D.S.K I.1) (D.preAt I)).E
        (h - D.SP.Δ) a) :
    ∃ ns, D.TorusFormAt G I j (h - D.SP.Δ) xs (D.maskSel G I j asg w h F) ns a := by
  have hb := blkStart_bounds D.hK I.1 (A := A)
  obtain ⟨ns, hn, hform⟩ := (D.Ms j G).cell_torus_form D.S D.hA (b := A.blkStart D.S.K I.1)
    (J := D.preAt I) rfl (D.subset_preAt I) hb.1 a (D.maskSel G I j asg w h F)
    (fun x hx => hF x hx) (fun x => D.c j G (A.blkStart D.S.K I.1) (D.preAt I) x.1) hxs hQ hD
    hcard hΛ hK
  refine ⟨ns, fun x hx i => (hn x hx i).trans ?_, hform⟩
  have hE : 0 ≤ D.S.Eh (h - D.SP.Δ) := by
    unfold ModeSchedule.Eh
    exact pow_nonneg (le_trans (by norm_num) D.hA) _
  have hc : (Fintype.card ((D.Ms j G).alive (ancAt A.G (D.preAt I)
      (A.blkStart D.S.K I.1 - 4 * D.S.K))) : ℝ) ≤ D.S.Dstar := by
    rw [Fintype.card_coe]; exact hcard
  exact mul_le_mul_of_nonneg_right hc hE

open Classical in
/-- The subtotals of pairwise disjoint components add up to the subtotal of their union. -/
theorem sum_compSub (l : Fin 4) (G : bf.Grp) (I : ℤ × ℤ) (S : Finset (Finset (D.Ms l G).Md))
    (hS : Set.PairwiseDisjoint (S : Set (Finset (D.Ms l G).Md)) id) :
    ∑ K ∈ S, D.compSub l G I K = D.compSub l G I (S.biUnion id) := by
  unfold compSub
  rw [Finset.sum_biUnion hS, map_sum, map_sum]
  rfl

open Classical in
/-- The selected modes are the union of the masked components. -/
theorem maskSel_map (G : bf.Grp) (I : ℤ × ℤ) (j : Fin 4) {n : ℕ} (asg : Fin n → Fin 4)
    (w : Fin n → ℕ) (h : ℕ) (F : Finset (D.Ms j G).Md) :
    (D.maskSel G I j asg w h F).map ⟨Subtype.val, Subtype.val_injective⟩ =
      (D.maskComps G I j asg w h F).biUnion id := by
  ext m
  simp only [Finset.mem_map, Function.Embedding.coeFn_mk, Finset.mem_biUnion, id]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (Finset.mem_filter.mp hx).2
  · rintro ⟨K, hK, hmK⟩
    have hKall := (D.Ms j G).allComps_of_coreComps D.S D.hA D.SP
      (D.mem_compsAt (Finset.mem_filter.mp hK).1).1
    obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hKall
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hmK
    exact ⟨y, Finset.mem_filter.mpr ⟨Finset.mem_univ _, _, hK, Finset.mem_map_of_mem _ hy⟩, rfl⟩

open Classical in
/-- The masked components of a core slot with final class `F`, as entries of the component
index set: summing any function over them is summing over `maskComps`. -/
theorem masked_filter_sum {M : Type*} [AddCommMonoid M] (G : bf.Grp) (I : ℤ × ℤ)
    (σ : Fin 4 → Fin 3) {l : Fin 4} (hl : σ l = 0) {n : ℕ} (asg : Fin n → Fin 4)
    (w : Fin n → ℕ) (h : ℕ) (F : Finset (D.Ms l G).Md) (f : Option (Finset (D.Ms l G).Md) → M) :
    ∑ o ∈ ((compIdx σ (fun l => D.compsAt l G I) l).filter
        (roleMask (D.slotGood G I l) l asg w h)).filter (fun o => D.coreCls G I h l o = F), f o =
      ∑ K ∈ D.maskComps G I l asg w h F, f (some K) := by
  unfold compIdx maskComps
  simp only [hl, ↓reduceIte]
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_map, Finset.sum_filter]
  refine Finset.sum_congr rfl fun K _ => ?_
  simp only [Function.Embedding.some_apply]
  by_cases h1 : roleMask (D.slotGood G I l) l asg w h (some K)
  · by_cases h2 : D.coreCls G I h l (some K) = F
    · simp [h1, h2]
    · simp [h1, h2]
  · simp [h1]

open Classical in
/-- The masked components of a core slot are pairwise disjoint. -/
theorem maskComps_disjoint (G : bf.Grp) (I : ℤ × ℤ) (j : Fin 4) {n : ℕ} (asg : Fin n → Fin 4)
    (w : Fin n → ℕ) (h : ℕ) (F : Finset (D.Ms j G).Md) :
    Set.PairwiseDisjoint (D.maskComps G I j asg w h F : Set (Finset (D.Ms j G).Md)) id := by
  refine ((D.Ms j G).coreComps_pairwiseDisjoint D.S D.hA D.SP (A.blkStart D.S.K I.1)
    (D.preAt I)).subset fun K hK => ?_
  exact (D.mem_compsAt (Finset.mem_filter.mp (Finset.mem_coe.mp hK)).1).1

open Classical in
/-- Blueprint lines 2466-2467 (grouping at the final classes): the masked subtotals of a core slot
with final class `F` add up to the subtotal of the selected modes. -/
theorem masked_group_sum (G : bf.Grp) (I : ℤ × ℤ) (σ : Fin 4 → Fin 3) {l : Fin 4} (hl : σ l = 0)
    {n : ℕ} (asg : Fin n → Fin 4) (w : Fin n → ℕ) (h : ℕ) (F : Finset (D.Ms l G).Md)
    (s e : Fin 4 → ColumnL2 (bf.Lab ⊕ Fin fp.Mc)) :
    ∑ o ∈ ((compIdx σ (fun l => D.compsAt l G I) l).filter
        (roleMask (D.slotGood G I l) l asg w h)).filter (fun o => D.coreCls G I h l o = F),
      slotVal σ (fun l K => D.compSub l G I K) s e l o =
    D.compSub l G I ((D.maskSel G I l asg w h F).map ⟨Subtype.val, Subtype.val_injective⟩) := by
  rw [D.masked_filter_sum G I σ hl asg w h F, D.maskSel_map,
    ← D.sum_compSub l G I _ (D.maskComps_disjoint G I l asg w h F)]
  refine Finset.sum_congr rfl fun K _ => ?_
  simp only [slotVal, hl, ↓reduceIte]

open Classical in
/-- Blueprint lines 2565-2566 for a group of masked tuples: the absolute coefficient sum of the
selected modes of a core slot is the sum over the masked components of their coefficient
sums. -/
theorem masked_group_coef (G : bf.Grp) (I : ℤ × ℤ) (σ : Fin 4 → Fin 3) {l : Fin 4}
    (hl : σ l = 0) {n : ℕ} (asg : Fin n → Fin 4) (w : Fin n → ℕ) (h : ℕ)
    (F : Finset (D.Ms l G).Md) (s : ℝ) :
    ∑ o ∈ ((compIdx σ (fun l => D.compsAt l G I) l).filter
        (roleMask (D.slotGood G I l) l asg w h)).filter (fun o => D.coreCls G I h l o = F),
      o.elim s (fun K => ∑ m ∈ K, ‖D.c l G (A.blkStart D.S.K I.1) (D.preAt I) m‖) =
    D.coefSum G I l (D.maskSel G I l asg w h F) := by
  rw [D.masked_filter_sum G I σ hl asg w h F]
  have e : D.coefSum G I l (D.maskSel G I l asg w h F) =
      ∑ m ∈ (D.maskSel G I l asg w h F).map ⟨Subtype.val, Subtype.val_injective⟩,
        ‖D.c l G (A.blkStart D.S.K I.1) (D.preAt I) m‖ := by
    unfold coefSum
    rw [Finset.sum_map]
    rfl
  rw [e, D.maskSel_map, Finset.sum_biUnion (D.maskComps_disjoint G I l asg w h F)]
  rfl

open Classical in
/-- The final classes at `h` of the core components of a role good at `h`. -/
noncomputable def goodCls (G : bf.Grp) (I : ℤ × ℤ) (j : Fin 4) (h : ℕ) :
    Finset (Finset (D.Ms j G).Md) :=
  ((D.compsAt j G I).filter fun K =>
    (D.Ms j G).compGood D.S D.hA D.SP (A.blkStart D.S.K I.1) (D.preAt I) h K).image
    fun K => (D.Ms j G).compClass D.S D.hA (A.blkStart D.S.K I.1) (D.preAt I) h K

open Classical in
/-- A final class of a good core component is the final class of a mode good at `h`. -/
theorem mem_goodCls {G : bf.Grp} {I : ℤ × ℤ} {j : Fin 4} {h : ℕ} {F : Finset (D.Ms j G).Md}
    (hF : F ∈ D.goodCls G I j h) :
    ∃ m : (D.Ms j G).alive (ancAt A.G (D.preAt I) (A.blkStart D.S.K I.1 - 4 * D.S.K)),
      ((D.Ms j G).blockComps D.S D.hA (A.blkStart D.S.K I.1) (D.preAt I)).Good D.SP.Δ
        ((D.Ms j G).goodP D.S D.SP (A.blkStart D.S.K I.1)) h m ∧ D.finCls G I j h m = F := by
  obtain ⟨K, hK, rfl⟩ := Finset.mem_image.mp hF
  obtain ⟨-, x, hKx, hgx⟩ := Finset.mem_filter.mp hK
  refine ⟨x, hgx, ?_⟩
  rw [hKx, (D.Ms j G).compClass_eq D.S D.hA _ _ h x]
  rfl

end SideInput

end ActiveSetup.BasicFamilies.FamParams

namespace ActiveSetup.BasicFamilies.FamParams
variable {κ' : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ' c₀} {bf : A.BasicFamilies}
  {fp : bf.FamParams}

namespace SideInput
variable (D : fp.SideInput)

open Classical in
/-- Anchors of the final classes (blueprint line 2467, "they lie in the unique good predecessor of
each `F_j`; let `a_j` be its representative"): at every upper height `h` and in every role, every
mode of a core component good at `h` lies in the PRE predecessor `E_{h-Δ}` of the anchor of its
final class (for instance the hereditary representatives, `selected_in_pred_of_rep`). -/
def AnchorOK (G : bf.Grp) (I : ℤ × ℤ)
    (anc : ℕ → ∀ j, Finset (D.Ms j G).Md →
      (D.Ms j G).alive (ancAt A.G (D.preAt I) (A.blkStart D.S.K I.1 - 4 * D.S.K))) : Prop :=
  ∀ h ∈ ModeComponents.upperHeights D.SP.Jst D.SP.δs, ∀ j, ∀ K ∈ D.compsAt j G I,
    (D.Ms j G).compGood D.S D.hA D.SP (A.blkStart D.S.K I.1) (D.preAt I) h K →
    ∀ x : (D.Ms j G).alive (ancAt A.G (D.preAt I) (A.blkStart D.S.K I.1 - 4 * D.S.K)), x.1 ∈ K →
      x ∈ ((D.Ms j G).blockComps D.S D.hA (A.blkStart D.S.K I.1) (D.preAt I)).E (h - D.SP.Δ)
        (anc h j ((D.Ms j G).compClass D.S D.hA (A.blkStart D.S.K I.1) (D.preAt I) h K))

open Classical in
/-- The selected modes of a final class lie in the PRE predecessor of its anchor. -/
theorem maskSel_anchor {G : bf.Grp} {I : ℤ × ℤ}
    {anc : ℕ → ∀ j, Finset (D.Ms j G).Md →
      (D.Ms j G).alive (ancAt A.G (D.preAt I) (A.blkStart D.S.K I.1 - 4 * D.S.K))}
    (hanc : D.AnchorOK G I anc) {h : ℕ} (hh : h ∈ ModeComponents.upperHeights D.SP.Jst D.SP.δs)
    (j : Fin 4) {n : ℕ} (asg : Fin n → Fin 4) (w : Fin n → ℕ) (F : Finset (D.Ms j G).Md) :
    ∀ x ∈ D.maskSel G I j asg w h F,
      x ∈ ((D.Ms j G).blockComps D.S D.hA (A.blkStart D.S.K I.1) (D.preAt I)).E (h - D.SP.Δ)
        (anc h j F) := by
  intro x hx
  obtain ⟨K, hK, hxK⟩ := (Finset.mem_filter.mp hx).2
  obtain ⟨hKc, hmask, hcls⟩ := Finset.mem_filter.mp hK
  have hx' := hanc h hh j K hKc hmask.1 x hxK
  have e : (D.Ms j G).compClass D.S D.hA (A.blkStart D.S.K I.1) (D.preAt I) h K = F := hcls
  rwa [e] at hx'

open Classical in
/-- `role_size_moments` for a final class `F = F_h(m)`, in terms of `σ_F = clsSize F`. -/
theorem role_size_moments_cls {Cj CA CT CK : ℕ} {δs W : ℝ} (hV : D.S.Valid Cj CA CT CK δs W)
    (hCA : 1 ≤ CA) (hCT : 4 ≤ CT) (hd2 : 2 ≤ D.S.dmax) (hD : 2 ≤ D.S.Dstar) (hB : 2 ≤ D.S.Bstar)
    (hQ : 1 ≤ D.S.Q0) (hSP : D.SP = D.S.sideParams δs) (hstab : D.Stab) (I : ℤ × ℤ) (j : Fin 4)
    (G : bf.Grp) (hdim : (D.Ms j G).zc.dim ≤ D.S.dmax) (hδc : 0 < (D.Ms j G).δc)
    (hDg : gaugeSqNorm (D.Ms j G).zc.dim (D.Ms j G).δc ≤ D.S.Dstar) {Kf : ℕ}
    (hKf : 2 * gaugeTail (D.Ms j G).zc.dim (D.Ms j G).δc / 2 ^ Kf * D.S.Dstar ^ 300 ≤ 1)
    (hQB : (D.S.Q0 : ℝ) * 2 ^ (Kf + 1) ≤ D.S.Bstar)
    (hεw : ∀ m, D.S.Dstar⁻¹ ≤ (D.Ms j G).L.εM m)
    (hcard : (((D.Ms j G).alive (ancAt A.G (D.preAt I)
      (A.blkStart D.S.K I.1 - 4 * D.S.K))).card : ℝ) ≤ D.S.Dstar)
    (hΛ : (D.Ms j G).Λ ≤ D.S.Dstar) (hJ : 2 ≤ D.SP.Jst) (hδ : 0 < D.SP.δs)
    (hδ16 : D.SP.δs ≤ 1 / 16) (hδJ : ⌈4 * D.SP.δs * D.SP.Jst⌉₊ ≤ D.SP.Jst) {h : ℕ}
    (hh : h ∈ ModeComponents.upperHeights D.SP.Jst D.SP.δs)
    {m : (D.Ms j G).alive (ancAt A.G (D.preAt I) (A.blkStart D.S.K I.1 - 4 * D.S.K))}
    (hgood : ((D.Ms j G).blockComps D.S D.hA (A.blkStart D.S.K I.1) (D.preAt I)).Good D.SP.Δ
      ((D.Ms j G).goodP D.S D.SP (A.blkStart D.S.K I.1)) h m) {F : Finset (D.Ms j G).Md}
    (hF : D.finCls G I j h m = F) {n : ℕ} (asg : Fin n → Fin 4)
    (ns : (Fin n → ℕ) → (D.Ms j G).alive (ancAt A.G (D.preAt I)
      (A.blkStart D.S.K I.1 - 4 * D.S.K)) → Fin (D.Ms j G).zc.dim → ℤ)
    (a : (D.Ms j G).alive (ancAt A.G (D.preAt I) (A.blkStart D.S.K I.1 - 4 * D.S.K)))
    {xs : ℝ} (hxs : xs ∈ dyadicGridCell A.G I.1 I.2)
    (hform : ∀ w ∈ Fintype.piFinset
      (fun _ : Fin n => ModeComponents.upperHeights D.SP.Jst D.SP.δs),
      D.TorusFormAt G I j (h - D.SP.Δ) xs (D.maskSel G I j asg w h F) (ns w) a) :
    (∀ w ∈ Fintype.piFinset (fun _ : Fin n => ModeComponents.upperHeights D.SP.Jst D.SP.δs),
      D.coreSize G I xs (h - D.SP.Δ) j (D.maskSel G I j asg w h F) (ns w) ≤
        6 * D.clsSize G I j F) ∧
    ∑ w ∈ Fintype.piFinset (fun _ : Fin n => ModeComponents.upperHeights D.SP.Jst D.SP.δs),
      (((ModeComponents.upperHeights D.SP.Jst D.SP.δs).card : ℝ) ^ n)⁻¹ *
        D.coreSize G I xs (h - D.SP.Δ) j (D.maskSel G I j asg w h F) (ns w) ^ 2 ≤
      36 * (2 * D.SP.δs) ^ (Finset.univ.filter fun i => asg i = j).card *
        D.clsSize G I j F ^ 2 := by
  subst hF
  obtain ⟨h1, h2⟩ := D.role_size_moments hV hCA hCT hd2 hD hB hQ hSP hstab I j G hdim hδc hDg hKf
    hQB hεw hcard hΛ hJ hδ hδ16 hδJ hh hgood asg ns a hxs hform
  have h0 : 0 ≤ (D.Ms j G).compSizeSq D.S D.hA D.SP I (A.blkStart D.S.K I.1) (D.preAt I) h m
      (D.c j G (A.blkStart D.S.K I.1) (D.preAt I)) := Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [D.clsSize_finCls, Real.sq_sqrt h0]
  exact ⟨h1, h2⟩

open Classical in
/-- The principal coefficient of a four-core tuple with representatives `a`: `|WFourier_s(r q',
  r t')|`
when it passes the four-core test, `0` when it is discarded (blueprint lines 2519-2530). -/
noncomputable def fourCoef (G : bf.Grp) (I : ℤ × ℤ) (xs : ℝ) (h' : ℕ)
    (a : ∀ j, (D.Ms j G).alive (ancAt A.G (D.preAt I) (A.blkStart D.S.K I.1 - 4 * D.S.K))) :
    ℝ :=
  if D.fourPasses G I xs h' a then
    ‖fourK (dyadicGridLeft A.G I.1 I.2) (dyadicGridLength A.G I.1) (A.w I) xs
      (D.fourQ' G I xs h' a) (D.fourT' G I xs h' a)‖ else 0

theorem fourCoef_nonneg (G : bf.Grp) (I : ℤ × ℤ) (xs : ℝ) (h' : ℕ)
    (a : ∀ j, (D.Ms j G).alive (ancAt A.G (D.preAt I) (A.blkStart D.S.K I.1 - 4 * D.S.K))) :
    0 ≤ D.fourCoef G I xs h' a := by
  unfold fourCoef
  split_ifs
  · exact norm_nonneg _
  · exact le_rfl

open Classical in
/-- The tuple errors of a group of masked tuples with final classes `p`: the sum over the group of
`Π_l Σ_{m ∈ r_l} |α_m|` is the product of the coefficient sums of the selected modes. -/
theorem masked_group_err (G : bf.Grp) (I : ℤ × ℤ) (σ : Fin 4 → Fin 3) (hσ : ∀ l, σ l = 0)
    {n : ℕ} (asg : Fin n → Fin 4) (w : Fin n → ℕ) (h : ℕ) (p : ∀ l, Finset (D.Ms l G).Md) :
    ∑ r ∈ (Fintype.piFinset fun l => (compIdx σ (fun l => D.compsAt l G I) l).filter
        (roleMask (D.slotGood G I l) l asg w h)).filter
          (fun r => ∀ l, D.coreCls G I h l (r l) = p l),
      ∏ l, (r l).elim 1 (fun K => ∑ m ∈ K, ‖D.c l G (A.blkStart D.S.K I.1) (D.preAt I) m‖) =
    ∏ l, D.coefSum G I l (D.maskSel G I l asg w h (p l)) := by
  have hpf : (Fintype.piFinset fun l => (compIdx σ (fun l => D.compsAt l G I) l).filter
        (roleMask (D.slotGood G I l) l asg w h)).filter
          (fun r => ∀ l, D.coreCls G I h l (r l) = p l) =
      Fintype.piFinset fun l => ((compIdx σ (fun l => D.compsAt l G I) l).filter
        (roleMask (D.slotGood G I l) l asg w h)).filter (fun o => D.coreCls G I h l o = p l) := by
    ext r
    simp only [Finset.mem_filter, Fintype.mem_piFinset]
    constructor
    · rintro ⟨h1, h2⟩ l; exact ⟨h1 l, h2 l⟩
    · intro h; exact ⟨fun l => (h l).1, fun l => (h l).2⟩
  rw [hpf]
  refine (Finset.prod_univ_sum _ (fun l (o : Option (Finset (D.Ms l G).Md)) => o.elim (1 : ℝ)
    (fun K => ∑ m ∈ K, ‖D.c l G (A.blkStart D.S.K I.1) (D.preAt I) m‖))).symm.trans ?_
  exact Finset.prod_congr rfl fun l _ => D.masked_group_coef G I σ (hσ l) asg w h (p l) 1

end SideInput

end ActiveSetup.BasicFamilies.FamParams

namespace ActiveSetup.BasicFamilies.FamParams
variable {κ' : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ' c₀} {bf : A.BasicFamilies}
  {fp : bf.FamParams}

namespace SideInput
variable (D : fp.SideInput)

open Classical in
/-- Blueprint lines 2463-2582 for the four-core pattern on a leaf cell of the side states
(`eq:principal-core` before binning, with `eq:core-numerical`): with anchors of the final classes
(`AnchorOK`), the form of the four core slots is at most `2⁴ Z / (1 - 4 (2δ_*)^{1/4})` plus the
absolute tuple errors `C_J D_*^{-100} Π_l Σ_{m ∈ r_l} |α_m|`, where
`Z = Σ_{h ∈ H} |H|⁻¹ Σ_p c_p Π_j 6 σ_{p_j}` sums over the final heights and the tuples `p` of final
classes of good core components the principal coefficients `c_p = |WFourier_s(r q', r t')|` of the
passing tuples (`0` for discarded ones) times the class sizes (exact common-height selection
`pattern_first_success`, first success `pattern_leaf_bound`, grouping `masked_group_sum`, tuple
bounds `four_core_tuple_bound`, moments `role_size_moments_cls` and `principal_word_average`). -/
theorem four_core_principal {Cj CA CT CK : ℕ} {δs W : ℝ} (hV : D.S.Valid Cj CA CT CK δs W)
    (hCA : 1 ≤ CA) (hCT : 4 ≤ CT) (hd2 : 2 ≤ D.S.dmax) (hD : 2 ≤ D.S.Dstar)
    (hB : 2 ≤ D.S.Bstar) (hQ : 1 ≤ D.S.Q0) (hSP : D.SP = D.S.sideParams δs) (hstab : D.Stab)
    (hK : D.S.Dstar ^ 600 ≤ (2 : ℝ) ^ D.S.K) {I : ℤ × ℤ} (hI : I ∈ A.cells) (G : bf.Grp)
    (hz : ∀ j, (D.Ms j G).zc = (D.Ms 0 G).zc) (hdim : (D.Ms 0 G).zc.dim ≤ D.S.dmax) {δ : ℝ}
    (hδ : 0 < δ) (hδc : ∀ j, (D.Ms j G).δc = δ) (hcl : ∀ j, (D.Ms j G).cl = slotCoeff j)
    (hρ : ∀ j k, (D.Ms j G).ρ k ∈ Set.Icc (0 : ℝ) 1)
    (hQC : ∀ a b, ∃ k : ℤ, (D.S.Q0 : ℝ) * ((D.Ms 0 G).zc.C a b : ℝ) = k) {Cm : ℝ}
    (hCm0 : 0 ≤ Cm) (hCm : ∀ a b, |((D.Ms 0 G).zc.C a b : ℝ)| ≤ Cm)
    {Kt : ℕ} (hQB : (D.S.Q0 : ℝ) * 2 ^ (Kt + 1) ≤ D.S.Bstar)
    (hτc : cutTail (D.Ms 0 G).zc.dim δ Kt ≤ (D.S.Dstar ^ 300)⁻¹)
    (hτm : multTail (D.Ms 0 G).zc.dim (δ / 2) D.S.Q0 Cm Kt ≤ (D.S.Dstar ^ 300)⁻¹)
    (hMN : multNorm (D.Ms 0 G).zc.dim (δ / 2) D.S.Q0 Cm ≤ D.S.Dstar)
    (hCN : cutNorm (D.Ms 0 G).zc.dim δ ≤ D.S.Dstar) {J : ℕ} (hJ1 : 1 ≤ J)
    (hDg : ∀ j, gaugeSqNorm (D.Ms j G).zc.dim (D.Ms j G).δc ≤ D.S.Dstar) {Kf : ℕ}
    (hKf : ∀ j, 2 * gaugeTail (D.Ms j G).zc.dim (D.Ms j G).δc / 2 ^ Kf * D.S.Dstar ^ 300 ≤ 1)
    (hQBf : (D.S.Q0 : ℝ) * 2 ^ (Kf + 1) ≤ D.S.Bstar)
    (hεw : ∀ j m, D.S.Dstar⁻¹ ≤ (D.Ms j G).L.εM m)
    (hcard : ∀ j, (((D.Ms j G).alive (ancAt A.G (D.preAt I)
      (A.blkStart D.S.K I.1 - 4 * D.S.K))).card : ℝ) ≤ D.S.Dstar)
    (hΛ : ∀ j, (D.Ms j G).Λ ≤ D.S.Dstar) (hJ : 2 ≤ D.SP.Jst) (hδs : 0 < D.SP.δs)
    (hδ16 : D.SP.δs ≤ 1 / 16) (hδJ : ⌈4 * D.SP.δs * D.SP.Jst⌉₊ ≤ D.SP.Jst)
    (hq : 4 * (2 * D.SP.δs) ^ (1 / (4 : ℝ)) < 1)
    (anc : ℕ → ∀ j, Finset (D.Ms j G).Md →
      (D.Ms j G).alive (ancAt A.G (D.preAt I) (A.blkStart D.S.K I.1 - 4 * D.S.K)))
    (hanc : D.AnchorOK G I anc) {xs : ℝ} (hxs : xs ∈ dyadicGridCell A.G I.1 I.2)
    (L : ∀ l G, LiftData (bf.Lab ⊕ Fin fp.Mc) (D.Ms l G).Md) :
    ‖fp.Λc I (patternPiece (fun l => D.coreAt l G I) (fun l => D.toLeaf.sv l G I)
        (fun l => D.errAt L l G I) (fun _ => 0))‖ ≤
      2 ^ 4 * (∑ h ∈ ModeComponents.upperHeights D.SP.Jst D.SP.δs,
        ((ModeComponents.upperHeights D.SP.Jst D.SP.δs).card : ℝ)⁻¹ *
          ∑ p ∈ Fintype.piFinset (fun j => D.goodCls G I j h),
            D.fourCoef G I xs (h - D.SP.Δ) (fun j => anc h j (p j)) *
              ∏ j, (6 * D.clsSize G I j (p j))) / (1 - 4 * (2 * D.SP.δs) ^ (1 / (4 : ℝ))) +
      ∑ r ∈ Fintype.piFinset (compIdx (fun _ => 0) (fun l => D.compsAt l G I)),
        fourErrC κ' J * (D.S.Dstar ^ 100)⁻¹ *
          ∏ l, (r l).elim 1 (fun K => ∑ m ∈ K, ‖D.c l G (A.blkStart D.S.K I.1) (D.preAt I) m‖) := by
  set H := ModeComponents.upperHeights D.SP.Jst D.SP.δs with hH
  have hHJ : ∀ h ∈ H, h ≤ D.SP.Jst := fun h hh => by
    have := (Finset.mem_filter.mp hh).1
    rw [Finset.mem_range] at this
    omega
  have hρ0 : (0 : ℝ) ≤ 2 * D.SP.δs := by linarith only [hδs]
  have hdimj : ∀ j, (D.Ms j G).zc.dim ≤ D.S.dmax := fun j => by rw [hz j]; exact hdim
  have hδcj : ∀ j, 0 < (D.Ms j G).δc := fun j => by rw [hδc j]; exact hδ
  have htor : ∀ h ∈ H, ∀ j {n : ℕ} (asg : Fin n → Fin 4) (w : Fin n → ℕ)
      (F : Finset (D.Ms j G).Md), D.TorusFormAt G I j (h - D.SP.Δ) xs
        (D.maskSel G I j asg w h F) (D.maskShift G I j asg w h F xs (anc h j F)) (anc h j F) :=
    fun h hh j _ asg w F => D.maskShift_spec G I j asg w h F xs (anc h j F)
      (D.maskSel_torus_form_of G I j hQ hD (hcard j) (hΛ j) hK asg w F hxs
        (D.maskSel_anchor hanc hh j asg w F))
  rw [(D.pattern_first_success L I G (fun _ => 0) hJ hδs hδ16).1]
  refine pattern_leaf_bound (fp.Λc I) (fun _ => 0) (fun l => D.compsAt l G I)
    (fun l K => D.compSub l G I K) (fun l => D.toLeaf.sv l G I) (fun l => D.errAt L l G I) H
    (fun l => D.slotGood G I l) (D.tuple_success G I (fun _ => 0) hJ hδs hδ16)
    (fun h l => D.coreCls G I h l)
    (fun n a w h p => D.fourCoef G I xs (h - D.SP.Δ) (fun j => anc h j (p j)) *
      ∏ j, D.maskSize G I j a w h (p j) xs (anc h j (p j)))
    (fun r => fourErrC κ' J * (D.S.Dstar ^ 100)⁻¹ *
      ∏ l, (r l).elim 1 (fun K => ∑ m ∈ K, ‖D.c l G (A.blkStart D.S.K I.1) (D.preAt I) m‖))
    (fun n a w hw h hh p hp => ?_) hρ0 hq (fun n a => ?_)
  · -- the grouped tuples of one history: the four-core tuple bound
    have hpk := Fintype.mem_piFinset.mp hp
    obtain ⟨o, ho, -⟩ := Finset.mem_image.mp (hpk 0)
    obtain ⟨ho1, ho2⟩ := Finset.mem_filter.mp ho
    simp only [compIdx, ↓reduceIte, Finset.mem_map, Function.Embedding.some_apply] at ho1
    obtain ⟨K₀, -, rfl⟩ := ho1
    obtain ⟨m₀, -, hm₀⟩ := ho2.1
    have hgs : (fun l => ∑ o ∈ ((compIdx (fun _ => 0) (fun l => D.compsAt l G I) l).filter
        (roleMask (D.slotGood G I l) l a w h)).filter (fun o => D.coreCls G I h l o = p l),
        slotVal (fun _ => 0) (fun l K => D.compSub l G I K) (fun l => D.toLeaf.sv l G I)
          (fun l => D.errAt L l G I) l o) =
        fun l => D.compSub l G I
          ((D.maskSel G I l a w h (p l)).map ⟨Subtype.val, Subtype.val_injective⟩) :=
      funext fun l => D.masked_group_sum G I (fun _ => 0) rfl a w h (p l) _ _
    rw [hgs, ← Finset.mul_sum, D.masked_group_err G I (fun _ => 0) (fun _ => rfl) a w h p]
    have hb := D.four_core_tuple_bound hV hCA hCT hd2 hD hB hQ hSP hI G hz hdim hδ hδc hcl hρ
      hQC hCm0 hCm hQB hτc hτm hMN hCN hJ1 (hHJ h hh) hm₀
      (fun j => D.maskSel G I j a w h (p j))
      (fun j => D.maskShift G I j a w h (p j) xs (anc h j (p j)))
      (fun j => (htor h hh j a w (p j)).1) (fun j => anc h j (p j)) hxs
      (fun j => (htor h hh j a w (p j)).2)
    refine hb.trans (le_of_eq ?_)
    unfold fourCoef maskSize
    split_ifs <;> ring
  · -- the moments over the words and final heights
    have hImg : ∀ w h, Fintype.piFinset (fun l => ((compIdx (fun _ => 0)
        (fun l => D.compsAt l G I) l).filter (roleMask (D.slotGood G I l) l a w h)).image
          (D.coreCls G I h l)) ⊆ Fintype.piFinset (fun j => D.goodCls G I j h) := by
      intro w h p hp
      rw [Fintype.mem_piFinset] at hp ⊢
      intro l
      obtain ⟨o, ho, hop⟩ := Finset.mem_image.mp (hp l)
      rw [← hop]
      obtain ⟨ho1, ho2⟩ := Finset.mem_filter.mp ho
      simp only [compIdx, ↓reduceIte, Finset.mem_map, Function.Embedding.some_apply] at ho1
      obtain ⟨K, hK, rfl⟩ := ho1
      exact Finset.mem_image.mpr ⟨K, Finset.mem_filter.mpr ⟨hK, ho2.1⟩, rfl⟩
    have hpw := principal_word_average H (m₀ := 4) (by norm_num) a
      (π := fun _ => ∀ l, Finset (D.Ms l G).Md)
      (fun h => Fintype.piFinset (fun j => D.goodCls G I j h))
      (fun h p => D.fourCoef G I xs (h - D.SP.Δ) (fun j => anc h j (p j)))
      (fun h p _ => D.fourCoef_nonneg G I xs (h - D.SP.Δ) _)
      (fun h p j w => D.maskSize G I j a w h (p j) xs (anc h j (p j)))
      (fun h p j w => D.maskSize_nonneg G I j a w h (p j) xs (anc h j (p j)))
      (fun h p j => 6 * D.clsSize G I j (p j))
      (fun h p j => mul_nonneg (by norm_num) (D.clsSize_nonneg G I j (p j))) hρ0
      (fun h hh p hp j w hw => ?_) (fun h hh p hp j => ?_)
    · have h4 : ((4 : ℕ) : ℝ) = 4 := by norm_num
      rw [h4] at hpw
      refine le_trans ?_ hpw
      refine Finset.sum_le_sum fun w _ => Finset.sum_le_sum fun h _ => ?_
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact Finset.sum_le_sum_of_subset_of_nonneg (hImg w h) fun p _ _ =>
        mul_nonneg (D.fourCoef_nonneg G I xs (h - D.SP.Δ) _)
          (Finset.prod_nonneg fun j _ => D.maskSize_nonneg G I j a w h (p j) xs (anc h j (p j)))
    · obtain ⟨m, hm, hmF⟩ := D.mem_goodCls (Fintype.mem_piFinset.mp hp j)
      have hr := D.role_size_moments_cls hV hCA hCT hd2 hD hB hQ hSP hstab I j G (hdimj j)
        (hδcj j) (hDg j) (hKf j) hQBf (hεw j) (hcard j) (hΛ j) hJ hδs hδ16 hδJ hh hm hmF a
        (fun w => D.maskShift G I j a w h (p j) xs (anc h j (p j))) (anc h j (p j)) hxs
        (fun w _ => htor h hh j a w (p j))
      have h1 := hr.1 w hw
      have h0 := D.clsSize_nonneg G I j (p j)
      change D.maskSize G I j a w h (p j) xs (anc h j (p j)) ≤ 6 * D.clsSize G I j (p j) at h1
      linarith
    · obtain ⟨m, hm, hmF⟩ := D.mem_goodCls (Fintype.mem_piFinset.mp hp j)
      have hr := D.role_size_moments_cls hV hCA hCT hd2 hD hB hQ hSP hstab I j G (hdimj j)
        (hδcj j) (hDg j) (hKf j) hQBf (hεw j) (hcard j) (hΛ j) hJ hδs hδ16 hδJ hh hm hmF a
        (fun w => D.maskShift G I j a w h (p j) xs (anc h j (p j))) (anc h j (p j)) hxs
        (fun w _ => htor h hh j a w (p j))
      have h2 := hr.2
      have h0 : 0 ≤ (2 * D.SP.δs) ^ (Finset.univ.filter fun i => a i = j).card *
          D.clsSize G I j (p j) ^ 2 := mul_nonneg (pow_nonneg hρ0 _) (sq_nonneg _)
      refine h2.trans ?_
      nlinarith only [h0]

end SideInput

end ActiveSetup.BasicFamilies.FamParams

/-- The value `C_J 2μ ν^{-J} Π_j 6 (2 σ_j)` of a four-core dyadic bin `(μ, ν, σ)` (blueprint
`eq:principal-core`, `Λ = 1`). -/
noncomputable def fourBinVal (κ : LocalKernelClass) (J : ℕ) (c : ℝ × ℝ × (Fin 4 → ℝ)) : ℝ :=
  fourKC κ J * (2 * c.1) * (c.2.1 ^ J)⁻¹ * ∏ j, (6 * (2 * c.2.2 j))

theorem fourKC_nonneg (κ : LocalKernelClass) (J : ℕ) : 0 ≤ fourKC κ J := by
  have := kernelDerivBound_nonneg κ 0
  have := kernelDerivBound_nonneg κ J
  unfold fourKC
  positivity

namespace ActiveSetup.BasicFamilies.FamParams
variable {κ' : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ' c₀} {bf : A.BasicFamilies}
  {fp : bf.FamParams}

namespace SideInput
variable (D : fp.SideInput)

/-- The dyadic bin `(μ, ν, (σ_j)_j)` of a four-core tuple with representatives `a` and sizes `σ`
(the bands of `eq:four-tests` and the dyadic bands of the sizes). -/
noncomputable def fourBin (G : bf.Grp) (I : ℤ × ℤ) (xs : ℝ) (h' : ℕ)
    (a : ∀ j, (D.Ms j G).alive (ancAt A.G (D.preAt I) (A.blkStart D.S.K I.1 - 4 * D.S.K)))
    (σv : Fin 4 → ℝ) : ℝ × ℝ × (Fin 4 → ℝ) :=
  (D.fourMuBand G I xs h' a, D.fourNuBand G I xs h' a, fun j => dyadicBand (σv j))

open Classical in
/-- The tested four-core tuples of a family: those passing the four-core test with all sizes
positive. -/
noncomputable def fourTestedOf (G : bf.Grp) (I : ℤ × ℤ) (xs : ℝ) (h' : ℕ) {ι : Type*}
    (T : Finset ι)
    (a : ι → ∀ j, (D.Ms j G).alive (ancAt A.G (D.preAt I) (A.blkStart D.S.K I.1 - 4 * D.S.K)))
    (σv : ι → Fin 4 → ℝ) : Finset ι :=
  T.filter fun p => D.fourPasses G I xs h' (a p) ∧ ∀ j, 0 < σv p j

theorem one_le_U0 (hD : 2 ≤ D.S.Dstar) : 1 ≤ D.U0 := by
  unfold U0
  exact one_le_pow₀ (by linarith)

open Classical in
/-- Blueprint `eq:principal-core` (lines 2577-2582) for four cores (`Λ = 1`), at one final height:
the principal quantity `Σ_p c_p Π_j 6 σ_{p,j}` (`c_p = |WFourier_s(r q', r t')|` for passing
  tuples, `0`
for discarded ones) is at most the sum over the occupied dyadic bins `(μ, ν, σ)` of the bin values
`C_J 2μ ν^{-J} Π_j 6 (2σ_j)` times the number `N` of tuples in the bin that pass the four-core
test and have all `σ_j > 0` (zero factors contribute nothing; `four_core_kernel_sample`,
`fourBands_spec`, `sum_by_bins`). -/
theorem four_core_binned (hD : 2 ≤ D.S.Dstar) {I : ℤ × ℤ} (hI : I ∈ A.cells) (G : bf.Grp)
    (xs : ℝ) (h' J : ℕ) {ι : Type*} (T : Finset ι)
    (a : ι → ∀ j, (D.Ms j G).alive (ancAt A.G (D.preAt I) (A.blkStart D.S.K I.1 - 4 * D.S.K)))
    (σv : ι → Fin 4 → ℝ) (hσ : ∀ p ∈ T, ∀ j, 0 ≤ σv p j) :
    ∑ p ∈ T, D.fourCoef G I xs h' (a p) * ∏ j, (6 * σv p j) ≤
      ∑ c ∈ (D.fourTestedOf G I xs h' T a σv).image (fun p => D.fourBin G I xs h' (a p) (σv p)),
        fourBinVal κ' J c * (((D.fourTestedOf G I xs h' T a σv).filter
          fun p => D.fourBin G I xs h' (a p) (σv p) = c).card : ℝ) := by
  unfold fourTestedOf
  have hD0 : (0 : ℝ) ≤ D.S.Dstar := by linarith
  have hU := D.one_le_U0 hD
  rw [← Finset.sum_filter_of_ne (p := fun p => D.fourPasses G I xs h' (a p) ∧ ∀ j, 0 < σv p j)
    fun p hp hne => ?_]
  · refine sum_by_bins _ (fun p => D.fourBin G I xs h' (a p) (σv p)) (fourBinVal κ' J)
      (fun p => D.fourCoef G I xs h' (a p) * ∏ j, (6 * σv p j)) fun p hp => ?_
    obtain ⟨hpT, hpass, hpos⟩ := Finset.mem_filter.mp hp
    obtain ⟨hμ1, hμ2, hμ3, -, hν1, hν2, hν3, -⟩ := D.fourBands_spec hD0 hU hpass
    have hK := D.four_core_kernel_sample hI G xs h' (a p) J
    have hKC := fourKC_nonneg κ' J
    set μ := fourMu (dyadicGridLength A.G I.1) (D.fourQ' G I xs h' (a p)) (D.fourT' G I xs h' (a p))
    set ν := fourNu (dyadicGridLength A.G I.1) (D.fourQ' G I xs h' (a p)) (D.fourT' G I xs h' (a p))
    set μb := D.fourMuBand G I xs h' (a p)
    set νb := D.fourNuBand G I xs h' (a p)
    have hνb0 : 0 < νb := by linarith
    have hν0 : 0 < ν := by linarith
    have hU0i : 0 < D.U0⁻¹ := inv_pos.mpr (by linarith)
    have hμb0 : 0 < μb := by linarith
    have hcoef : D.fourCoef G I xs h' (a p) ≤ fourKC κ' J * (2 * μb) * (νb ^ J)⁻¹ := by
      unfold fourCoef
      simp only [hpass, ↓reduceIte]
      have h1 : ‖fourK (dyadicGridLeft A.G I.1 I.2) (dyadicGridLength A.G I.1) (A.w I) xs
          (D.fourQ' G I xs h' (a p)) (D.fourT' G I xs h' (a p))‖ ≤ fourKC κ' J * μ * (ν ^ J)⁻¹ := by
        rw [← div_eq_mul_inv, le_div_iff₀ (pow_pos hν0 J)]
        exact hK
      have h2 : (ν ^ J)⁻¹ ≤ (νb ^ J)⁻¹ :=
        inv_anti₀ (pow_pos hνb0 J) (pow_le_pow_left₀ hνb0.le hν1 J)
      exact h1.trans (mul_le_mul (mul_le_mul_of_nonneg_left hμ2.le hKC) h2
        (inv_nonneg.mpr (pow_nonneg hν0.le J)) (mul_nonneg hKC (by linarith)))
    have hprod : ∏ j, (6 * σv p j) ≤ ∏ j, (6 * (2 * dyadicBand (σv p j))) :=
      Finset.prod_le_prod₀ (fun j _ => mul_nonneg (by norm_num) (hσ p hpT j))
        fun j _ => mul_le_mul_of_nonneg_left (lt_two_mul_dyadicBand _).le (by norm_num)
    have hP0 : 0 ≤ ∏ j, (6 * σv p j) :=
      Finset.prod_nonneg fun j _ => mul_nonneg (by norm_num) (hσ p hpT j)
    have hB0 : 0 ≤ fourKC κ' J * (2 * μb) * (νb ^ J)⁻¹ := by positivity
    unfold fourBinVal fourBin
    exact mul_le_mul hcoef hprod hP0 hB0
  · by_contra hQ
    apply hne
    by_cases hpass : D.fourPasses G I xs h' (a p)
    · have hz : ∃ j, σv p j = 0 := by
        by_contra hz
        push Not at hz
        exact hQ ⟨hpass, fun j => lt_of_le_of_ne (hσ p hp j) (Ne.symm (hz j))⟩
      obtain ⟨j, hj⟩ := hz
      rw [Finset.prod_eq_zero (Finset.mem_univ j) (by rw [hj, mul_zero]), mul_zero]
    · unfold fourCoef
      simp only [hpass, ↓reduceIte, zero_mul]

end SideInput

end ActiveSetup.BasicFamilies.FamParams

namespace ActiveSetup.BasicFamilies.FamParams
variable {κ' : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ' c₀} {bf : A.BasicFamilies}
  {fp : bf.FamParams}

namespace SideInput
variable (D : fp.SideInput)

open Classical in
/-- The tested four-core tuples at a final height `h`: tuples of final classes of good core
components passing the four-core test with their anchors and with all class sizes positive. -/
noncomputable def fourTested (G : bf.Grp) (I : ℤ × ℤ) (xs : ℝ)
    (anc : ℕ → ∀ j, Finset (D.Ms j G).Md →
      (D.Ms j G).alive (ancAt A.G (D.preAt I) (A.blkStart D.S.K I.1 - 4 * D.S.K))) (h : ℕ) :
    Finset (∀ j, Finset (D.Ms j G).Md) :=
  D.fourTestedOf G I xs (h - D.SP.Δ) (Fintype.piFinset (fun j => D.goodCls G I j h))
    (fun p j => anc h j (p j)) (fun p j => D.clsSize G I j (p j))

/-- The dyadic bin of a four-core tuple of final classes at the final height `h`. -/
noncomputable def fourBinOf (G : bf.Grp) (I : ℤ × ℤ) (xs : ℝ)
    (anc : ℕ → ∀ j, Finset (D.Ms j G).Md →
      (D.Ms j G).alive (ancAt A.G (D.preAt I) (A.blkStart D.S.K I.1 - 4 * D.S.K))) (h : ℕ)
    (p : ∀ j, Finset (D.Ms j G).Md) : ℝ × ℝ × (Fin 4 → ℝ) :=
  D.fourBin G I xs (h - D.SP.Δ) (fun j => anc h j (p j)) (fun j => D.clsSize G I j (p j))

open Classical in
/-- Blueprint `eq:principal-core` (lines 2577-2582) for the four-core pattern on a leaf cell of
the side states (`Λ = 1`): the form of the four core slots is at most
`2⁴/(1 - 4(2δ_*)^{1/4}) Σ_{h ∈ H} |H|⁻¹ Σ_{bins} C_J 2μ ν^{-J} Π_j 6(2σ_j) N_{h,bin}`, plus the
absolute tuple errors of `eq:core-numerical`. Here `N_{h,bin}` is the number of tested tuples of
final classes at the final height `h` in the bin. These tuples pass the four-core test and have
nonzero class sizes, and they are counted once each: distinct classes have distinct anchors,
`anchor_injective`. The bin consists of the dyadic bands of `μ`, `ν` and of the component sizes
`σ_j` of `eq:component-size`. -/
theorem four_core_principal_bins {Cj CA CT CK : ℕ} {δs W : ℝ}
    (hV : D.S.Valid Cj CA CT CK δs W) (hCA : 1 ≤ CA) (hCT : 4 ≤ CT) (hd2 : 2 ≤ D.S.dmax)
    (hD : 2 ≤ D.S.Dstar) (hB : 2 ≤ D.S.Bstar) (hQ : 1 ≤ D.S.Q0) (hSP : D.SP = D.S.sideParams δs)
    (hstab : D.Stab) (hK : D.S.Dstar ^ 600 ≤ (2 : ℝ) ^ D.S.K) {I : ℤ × ℤ} (hI : I ∈ A.cells)
    (G : bf.Grp) (hz : ∀ j, (D.Ms j G).zc = (D.Ms 0 G).zc) (hdim : (D.Ms 0 G).zc.dim ≤ D.S.dmax)
    {δ : ℝ} (hδ : 0 < δ) (hδc : ∀ j, (D.Ms j G).δc = δ) (hcl : ∀ j, (D.Ms j G).cl = slotCoeff j)
    (hρ : ∀ j k, (D.Ms j G).ρ k ∈ Set.Icc (0 : ℝ) 1)
    (hQC : ∀ a b, ∃ k : ℤ, (D.S.Q0 : ℝ) * ((D.Ms 0 G).zc.C a b : ℝ) = k) {Cm : ℝ}
    (hCm0 : 0 ≤ Cm) (hCm : ∀ a b, |((D.Ms 0 G).zc.C a b : ℝ)| ≤ Cm)
    {Kt : ℕ} (hQB : (D.S.Q0 : ℝ) * 2 ^ (Kt + 1) ≤ D.S.Bstar)
    (hτc : cutTail (D.Ms 0 G).zc.dim δ Kt ≤ (D.S.Dstar ^ 300)⁻¹)
    (hτm : multTail (D.Ms 0 G).zc.dim (δ / 2) D.S.Q0 Cm Kt ≤ (D.S.Dstar ^ 300)⁻¹)
    (hMN : multNorm (D.Ms 0 G).zc.dim (δ / 2) D.S.Q0 Cm ≤ D.S.Dstar)
    (hCN : cutNorm (D.Ms 0 G).zc.dim δ ≤ D.S.Dstar) {J : ℕ} (hJ1 : 1 ≤ J)
    (hDg : ∀ j, gaugeSqNorm (D.Ms j G).zc.dim (D.Ms j G).δc ≤ D.S.Dstar) {Kf : ℕ}
    (hKf : ∀ j, 2 * gaugeTail (D.Ms j G).zc.dim (D.Ms j G).δc / 2 ^ Kf * D.S.Dstar ^ 300 ≤ 1)
    (hQBf : (D.S.Q0 : ℝ) * 2 ^ (Kf + 1) ≤ D.S.Bstar)
    (hεw : ∀ j m, D.S.Dstar⁻¹ ≤ (D.Ms j G).L.εM m)
    (hcard : ∀ j, (((D.Ms j G).alive (ancAt A.G (D.preAt I)
      (A.blkStart D.S.K I.1 - 4 * D.S.K))).card : ℝ) ≤ D.S.Dstar)
    (hΛ : ∀ j, (D.Ms j G).Λ ≤ D.S.Dstar) (hJ : 2 ≤ D.SP.Jst) (hδs : 0 < D.SP.δs)
    (hδ16 : D.SP.δs ≤ 1 / 16) (hδJ : ⌈4 * D.SP.δs * D.SP.Jst⌉₊ ≤ D.SP.Jst)
    (hq : 4 * (2 * D.SP.δs) ^ (1 / (4 : ℝ)) < 1)
    (anc : ℕ → ∀ j, Finset (D.Ms j G).Md →
      (D.Ms j G).alive (ancAt A.G (D.preAt I) (A.blkStart D.S.K I.1 - 4 * D.S.K)))
    (hanc : D.AnchorOK G I anc) {xs : ℝ} (hxs : xs ∈ dyadicGridCell A.G I.1 I.2)
    (L : ∀ l G, LiftData (bf.Lab ⊕ Fin fp.Mc) (D.Ms l G).Md) :
    ‖fp.Λc I (patternPiece (fun l => D.coreAt l G I) (fun l => D.toLeaf.sv l G I)
        (fun l => D.errAt L l G I) (fun _ => 0))‖ ≤
      2 ^ 4 * (∑ h ∈ ModeComponents.upperHeights D.SP.Jst D.SP.δs,
        ((ModeComponents.upperHeights D.SP.Jst D.SP.δs).card : ℝ)⁻¹ *
          ∑ c ∈ (D.fourTested G I xs anc h).image (D.fourBinOf G I xs anc h),
            fourBinVal κ' J c * (((D.fourTested G I xs anc h).filter
              fun p => D.fourBinOf G I xs anc h p = c).card : ℝ)) /
        (1 - 4 * (2 * D.SP.δs) ^ (1 / (4 : ℝ))) +
      ∑ r ∈ Fintype.piFinset (compIdx (fun _ => 0) (fun l => D.compsAt l G I)),
        fourErrC κ' J * (D.S.Dstar ^ 100)⁻¹ *
          ∏ l, (r l).elim 1 (fun K => ∑ m ∈ K, ‖D.c l G (A.blkStart D.S.K I.1) (D.preAt I) m‖) := by
  refine (D.four_core_principal hV hCA hCT hd2 hD hB hQ hSP hstab hK hI G hz hdim hδ hδc hcl hρ
    hQC hCm0 hCm hQB hτc hτm hMN hCN hJ1 hDg hKf hQBf hεw hcard hΛ hJ hδs hδ16 hδJ hq anc hanc hxs
    L).trans (add_le_add ?_ le_rfl)
  have hden : 0 < 1 - 4 * (2 * D.SP.δs) ^ (1 / (4 : ℝ)) := by linarith only [hq]
  refine div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun h _ =>
    mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (Nat.cast_nonneg _))) (by norm_num)) hden.le
  have hb := D.four_core_binned hD hI G xs (h - D.SP.Δ) J
    (Fintype.piFinset (fun j => D.goodCls G I j h)) (fun p j => anc h j (p j))
    (fun p j => D.clsSize G I j (p j)) fun p _ j => D.clsSize_nonneg G I j (p j)
  refine le_trans hb (le_of_eq ?_)
  rfl

end SideInput

end ActiveSetup.BasicFamilies.FamParams

/-- A product with the factor `1` at one index is the product over the other indices. -/
theorem prod_ite_one {M : Type*} [CommMonoid M] (l : Fin 4) (f : Fin 4 → M) :
    ∏ j, (if j = l then 1 else f j) = ∏ j ∈ Finset.univ.erase l, f j := by
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ l), ite_eq_left rfl, one_mul]
  exact Finset.prod_congr rfl fun j hj => ite_eq_right (Finset.ne_of_mem_erase hj)

namespace ActiveSetup.BasicFamilies.FamParams
variable {κ' : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ' c₀} {bf : A.BasicFamilies}
  {fp : bf.FamParams}

namespace SideInput
variable (D : fp.SideInput)

/-- The principal window coefficient of a three-core tuple with side role `l` (blueprint
`eq:side-windows`): `2 Σ_{Λ = 2^i ≤ 2^{I_w}} r⁻¹ C_{J,A} μ ν^{-J} 2^{A+4} Λ^{-(A+1)} b_Λ r` with the
offset-averaged window energies of the side `X`, so that `threePrin = threeC Π_{j ≠ l} a'_j`. -/
noncomputable def threeC (G : bf.Grp) (I : ℤ × ℤ) (xs : ℝ) (h' : ℕ) (l : Fin 4)
    (a : Fin 4 → ℝ)
    (X : ColumnL2 (bf.Lab ⊕ Fin fp.Mc)) (J Aw Iw : ℕ) : ℝ :=
  2 * ∑ i ∈ Finset.range (Iw + 1), ((dyadicGridLength A.G I.1)⁻¹ *
      entryC κ' J Aw (D.threeBeta G I xs h' l a) * 2 ^ (Aw + 4) * ((2 : ℝ) ^ i)⁻¹ ^ (Aw + 1)) *
    Real.sqrt (∫ ρ', sideWinE (D.Ms 0 G).zc l (augPhys X) (dyadicGridLeft A.G I.1 I.2)
      (dyadicGridLength A.G I.1) (D.threeWin G I xs h' l a (2 ^ i)) ρ'
      ∂offsetMeasure (D.Ms 0 G).zc.dim)

theorem threePrin_eq (G : bf.Grp) (I : ℤ × ℤ) (xs : ℝ) (h' : ℕ) (l : Fin 4)
    (a : Fin 4 → ℝ)
    (Fsel : ∀ j, Finset ((D.Ms j G).alive (ancAt A.G (D.preAt I)
      (A.blkStart D.S.K I.1 - 4 * D.S.K))))
    (n : ∀ j, (D.Ms j G).alive (ancAt A.G (D.preAt I) (A.blkStart D.S.K I.1 - 4 * D.S.K)) →
      Fin (D.Ms j G).zc.dim → ℤ)
    (X : ColumnL2 (bf.Lab ⊕ Fin fp.Mc)) (J Aw Iw : ℕ) :
    D.threePrin G I xs h' l a Fsel n X J Aw Iw =
      D.threeC G I xs h' l a X J Aw Iw *
        ∏ j ∈ Finset.univ.erase l, D.coreSize G I xs h' j (Fsel j) (n j) := by
  unfold threePrin threeC
  simp only [Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem threeC_nonneg {I : ℤ × ℤ} (hI : I ∈ A.cells) (G : bf.Grp) (xs : ℝ) (h' : ℕ) (l : Fin 4)
    (a : Fin 4 → ℝ)
    (X : ColumnL2 (bf.Lab ⊕ Fin fp.Mc)) (J Aw Iw : ℕ) : 0 ≤ D.threeC G I xs h' l a X J Aw Iw := by
  have hr := dyadicGridLength_pos A.G I.1
  have hw := A.adm I hI
  unfold threeC
  refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun i _ => mul_nonneg ?_ (Real.sqrt_nonneg _))
  have := entryC_nonneg hr hw J Aw (D.threeBeta G I xs h' l a)
  positivity

open Classical in
/-- The principal coefficient of a three-core tuple: `threeC` if it passes the three-core test,
`0` if it is discarded. -/
noncomputable def threeCoef (G : bf.Grp) (I : ℤ × ℤ) (xs : ℝ) (h' : ℕ) (l : Fin 4)
    (a : Fin 4 → ℝ)
    (X : ColumnL2 (bf.Lab ⊕ Fin fp.Mc)) (J Aw Iw : ℕ) : ℝ :=
  if D.threePasses G I xs h' l a then D.threeC G I xs h' l a X J Aw Iw else 0

theorem threeCoef_nonneg {I : ℤ × ℤ} (hI : I ∈ A.cells) (G : bf.Grp) (xs : ℝ) (h' : ℕ)
    (l : Fin 4)
    (a : Fin 4 → ℝ)
    (X : ColumnL2 (bf.Lab ⊕ Fin fp.Mc)) (J Aw Iw : ℕ) :
    0 ≤ D.threeCoef G I xs h' l a X J Aw Iw := by
  unfold threeCoef
  split_ifs
  · exact D.threeC_nonneg hI G xs h' l a X J Aw Iw
  · exact le_rfl

open Classical in
/-- In a non-core slot occurring in a group of masked tuples, the group consists of the single
dummy entry. -/
theorem masked_group_none (G : bf.Grp) (I : ℤ × ℤ) (σ : Fin 4 → Fin 3) {l : Fin 4}
    (hl : σ l ≠ 0) {n : ℕ} (asg : Fin n → Fin 4) (w : Fin n → ℕ) (h : ℕ)
    {F : Finset (D.Ms l G).Md}
    (hF : F ∈ ((compIdx σ (fun l => D.compsAt l G I) l).filter
      (roleMask (D.slotGood G I l) l asg w h)).image (D.coreCls G I h l)) :
    ((compIdx σ (fun l => D.compsAt l G I) l).filter
      (roleMask (D.slotGood G I l) l asg w h)).filter (fun o => D.coreCls G I h l o = F) =
      {none} := by
  obtain ⟨o, ho, hoF⟩ := Finset.mem_image.mp hF
  have hci : compIdx σ (fun l => D.compsAt l G I) l = {none} := by
    unfold compIdx
    simp only [hl, ↓reduceIte]
  rw [hci] at ho ⊢
  obtain ⟨ho1, ho2⟩ := Finset.mem_filter.mp ho
  rw [Finset.mem_singleton.mp ho1] at ho2 hoF
  rw [Finset.filter_singleton, ite_eq_left ho2, Finset.filter_singleton, ite_eq_left hoF]

open Classical in
/-- Blueprint lines 2549-2560 for a group of masked tuples of a three-core pattern: the side slot
of the grouped form is the side itself. -/
theorem masked_group_side (G : bf.Grp) (I : ℤ × ℤ) (σ : Fin 4 → Fin 3) {l : Fin 4}
    (hl : σ l = 1) {n : ℕ} (asg : Fin n → Fin 4) (w : Fin n → ℕ) (h : ℕ)
    {F : Finset (D.Ms l G).Md}
    (hF : F ∈ ((compIdx σ (fun l => D.compsAt l G I) l).filter
      (roleMask (D.slotGood G I l) l asg w h)).image (D.coreCls G I h l))
    (s e : Fin 4 → ColumnL2 (bf.Lab ⊕ Fin fp.Mc)) :
    ∑ o ∈ ((compIdx σ (fun l => D.compsAt l G I) l).filter
        (roleMask (D.slotGood G I l) l asg w h)).filter (fun o => D.coreCls G I h l o = F),
      slotVal σ (fun l K => D.compSub l G I K) s e l o = s l := by
  rw [D.masked_group_none G I σ (by rw [hl]; decide) asg w h hF, Finset.sum_singleton]
  simp only [slotVal, hl]
  rfl

open Classical in
/-- The tuple errors of a group of masked tuples of a three-core pattern (side slot `l`): the sum
over the group of `Π_k Σ_{m ∈ r_k} |α_m|` (the side slot contributing `1`) is the product over the
core slots of the coefficient sums of the selected modes. -/
theorem masked_group_err3 (G : bf.Grp) (I : ℤ × ℤ) (l : Fin 4) {n : ℕ} (asg : Fin n → Fin 4)
    (w : Fin n → ℕ) (h : ℕ) (p : ∀ l, Finset (D.Ms l G).Md)
    (hp : p l ∈ ((compIdx (fun k => if k = l then 1 else 0) (fun l => D.compsAt l G I) l).filter
      (roleMask (D.slotGood G I l) l asg w h)).image (D.coreCls G I h l)) :
    ∑ r ∈ (Fintype.piFinset fun k => (compIdx (fun k => if k = l then 1 else 0)
        (fun l => D.compsAt l G I) k).filter (roleMask (D.slotGood G I k) k asg w h)).filter
          (fun r => ∀ k, D.coreCls G I h k (r k) = p k),
      ∏ k, (r k).elim 1 (fun K => ∑ m ∈ K, ‖D.c k G (A.blkStart D.S.K I.1) (D.preAt I) m‖) =
    ∏ j ∈ Finset.univ.erase l, D.coefSum G I j (D.maskSel G I j asg w h (p j)) := by
  set σ : Fin 4 → Fin 3 := fun k => if k = l then 1 else 0 with hσ
  have hpf : (Fintype.piFinset fun k => (compIdx σ (fun l => D.compsAt l G I) k).filter
        (roleMask (D.slotGood G I k) k asg w h)).filter
          (fun r => ∀ k, D.coreCls G I h k (r k) = p k) =
      Fintype.piFinset fun k => ((compIdx σ (fun l => D.compsAt l G I) k).filter
        (roleMask (D.slotGood G I k) k asg w h)).filter (fun o => D.coreCls G I h k o = p k) := by
    ext r
    simp only [Finset.mem_filter, Fintype.mem_piFinset]
    constructor
    · rintro ⟨h1, h2⟩ k; exact ⟨h1 k, h2 k⟩
    · intro h; exact ⟨fun k => (h k).1, fun k => (h k).2⟩
  rw [hpf]
  refine (Finset.prod_univ_sum _ (fun k (o : Option (Finset (D.Ms k G).Md)) => o.elim (1 : ℝ)
    (fun K => ∑ m ∈ K, ‖D.c k G (A.blkStart D.S.K I.1) (D.preAt I) m‖))).symm.trans ?_
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ l),
    D.masked_group_none G I σ (by simp [hσ]) asg w h hp, Finset.sum_singleton]
  simp only [Option.elim, one_mul]
  exact Finset.prod_congr rfl fun j hj => D.masked_group_coef G I σ
    (by simp [hσ, Finset.ne_of_mem_erase hj]) asg w h (p j) 1

end SideInput

end ActiveSetup.BasicFamilies.FamParams

open Classical in
theorem compIdx_of_core (σ : Fin 4 → Fin 3) {κ : Fin 4 → Type*} (Ks : ∀ l, Finset (κ l))
    {l : Fin 4} (hl : σ l = 0) : compIdx σ Ks l = (Ks l).map Function.Embedding.some := by
  unfold compIdx
  simp only [hl, ↓reduceIte]

open Classical in
theorem compIdx_of_side (σ : Fin 4 → Fin 3) {κ : Fin 4 → Type*} (Ks : ∀ l, Finset (κ l))
    {l : Fin 4} (hl : σ l ≠ 0) : compIdx σ Ks l = {none} := by
  unfold compIdx
  simp only [hl, ↓reduceIte]

namespace ActiveSetup.BasicFamilies.FamParams
variable {κ' : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ' c₀} {bf : A.BasicFamilies}
  {fp : bf.FamParams}

namespace SideInput
variable (D : fp.SideInput)

open Classical in
/-- Anchors of the final classes in one role `j` (the property `AnchorOK` for this role): every
mode of a core component good at an upper height `h` lies in `E_{h-Δ}` of the anchor of its
class. -/
def AnchorOKAt (G : bf.Grp) (I : ℤ × ℤ) (j : Fin 4)
    (anc : ℕ → Finset (D.Ms j G).Md →
      (D.Ms j G).alive (ancAt A.G (D.preAt I) (A.blkStart D.S.K I.1 - 4 * D.S.K))) : Prop :=
  ∀ h ∈ ModeComponents.upperHeights D.SP.Jst D.SP.δs, ∀ K ∈ D.compsAt j G I,
    (D.Ms j G).compGood D.S D.hA D.SP (A.blkStart D.S.K I.1) (D.preAt I) h K →
    ∀ x : (D.Ms j G).alive (ancAt A.G (D.preAt I) (A.blkStart D.S.K I.1 - 4 * D.S.K)), x.1 ∈ K →
      x ∈ ((D.Ms j G).blockComps D.S D.hA (A.blkStart D.S.K I.1) (D.preAt I)).E (h - D.SP.Δ)
        (anc h ((D.Ms j G).compClass D.S D.hA (A.blkStart D.S.K I.1) (D.preAt I) h K))

open Classical in
/-- The selected modes of a final class lie in the PRE predecessor of its anchor (one role). -/
theorem maskSel_anchorAt {G : bf.Grp} {I : ℤ × ℤ} {j : Fin 4}
    {anc : ℕ → Finset (D.Ms j G).Md →
      (D.Ms j G).alive (ancAt A.G (D.preAt I) (A.blkStart D.S.K I.1 - 4 * D.S.K))}
    (hanc : D.AnchorOKAt G I j anc) {h : ℕ}
    (hh : h ∈ ModeComponents.upperHeights D.SP.Jst D.SP.δs) {n : ℕ} (asg : Fin n → Fin 4)
    (w : Fin n → ℕ) (F : Finset (D.Ms j G).Md) :
    ∀ x ∈ D.maskSel G I j asg w h F,
      x ∈ ((D.Ms j G).blockComps D.S D.hA (A.blkStart D.S.K I.1) (D.preAt I)).E (h - D.SP.Δ)
        (anc h F) := by
  intro x hx
  obtain ⟨K, hK, hxK⟩ := (Finset.mem_filter.mp hx).2
  obtain ⟨hKc, hmask, hcls⟩ := Finset.mem_filter.mp hK
  have hx' := hanc h hh K hKc hmask.1 x hxK
  have e : (D.Ms j G).compClass D.S D.hA (A.blkStart D.S.K I.1) (D.preAt I) h K = F := hcls
  rwa [e] at hx'

/-- The slopes `γ_j^* = ω_{a_j}(x_*)` of the anchors of a three-core tuple `p` of final classes at
the height `h` (side role `l`, whose entry is `0`). -/
noncomputable def slopes3 (G : bf.Grp) (I : ℤ × ℤ) (xs : ℝ) (l : Fin 4)
    (anc : ℕ → ∀ j, j ≠ l → Finset (D.Ms j G).Md →
      (D.Ms j G).alive (ancAt A.G (D.preAt I) (A.blkStart D.S.K I.1 - 4 * D.S.K))) (h : ℕ)
    (p : ∀ j, Finset (D.Ms j G).Md) : Fin 4 → ℝ :=
  fun j => if hj : j = l then 0 else (D.Ms j G).slope (anc h j hj (p j)).1 xs



end SideInput
end ActiveSetup.BasicFamilies.FamParams
end TrilinearHT.Auto
end
