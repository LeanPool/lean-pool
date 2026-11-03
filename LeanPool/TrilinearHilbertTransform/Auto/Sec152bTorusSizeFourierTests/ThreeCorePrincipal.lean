/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

/- Adapted for Lean Pool from roos-j/lean-trilinearht at
7b4209609e6a7fb9d9935973ee8541495f943660. Imports, names, proof organization and
Mathlib interfaces have been updated; original authorship is retained above. -/

public import LeanPool.TrilinearHilbertTransform.Auto.Sec152bTorusSizeFourierTests.ThreeCoreTupleBound

/-!
# Trilinear Hilbert transform: three_core_principal
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
private def ThreeCorePrincipalConclusion4Statement : Prop :=
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
    (_ : (4 : ℕ) ≤ CT)
    (_ : (2 : ℕ) ≤ D.S.dmax)
    (_ : (2 : ℝ) ≤ D.S.Dstar)
    (_ : (2 : ℝ) ≤ D.S.Bstar)
    (_ : (1 : ℕ) ≤ D.S.Q0)
    (_ : D.SP = D.S.sideParams δs)
    (_ : D.Stab)
    (I : ℤ × ℤ)
    (_ : I ∈ A.cells)
    (G : bf.Grp)
    (J : ℕ)
    (_ : ∀ (j : Fin (4 : ℕ)), gaugeSqNorm (D.Ms j G).zc.dim (D.Ms j G).δc ≤ D.S.Dstar)
    (Kf : ℕ)
    (_ : ∀ (j : Fin (4 : ℕ)), (2 : ℝ) * gaugeTail (D.Ms j G).zc.dim (D.Ms j G).δc / (2 : ℝ) ^
      Kf * D.S.Dstar ^ (300 : ℕ) ≤ (1 : ℝ))
    (_ : (↑D.S.Q0 : ℝ) * (2 : ℝ) ^ (Kf + (1 : ℕ)) ≤ D.S.Bstar)
    (_ : ∀ (j : Fin (4 : ℕ)) (m : (D.Ms j G).Md), D.S.Dstar⁻¹ ≤ (D.Ms j G).L.εM m)
    (_ : ∀ (j : Fin (4 : ℕ)), (↑((D.Ms j G).alive (ancAt A.G (D.preAt I) (A.blkStart D.S.K
      I.1 - (4 : ℤ) * (↑D.S.K : ℤ)))).card : ℝ) ≤ D.S.Dstar)
    (_ : ∀ (j : Fin (4 : ℕ)), (D.Ms j G).Λ ≤ D.S.Dstar)
    (_ : (2 : ℕ) ≤ D.SP.Jst)
    (_ : (0 : ℝ) < D.SP.δs)
    (_ : D.SP.δs ≤ (1 / 16 : ℝ))
    (_ : ⌈(4 : ℝ) * D.SP.δs * (↑D.SP.Jst : ℝ)⌉₊ ≤ D.SP.Jst)
    (l : Fin (4 : ℕ))
    (anc : ℕ → (j : Fin (4 : ℕ)) → j ≠ l → Finset (D.Ms j G).Md → ↥((D.Ms j G).alive (ancAt A.G
      (D.preAt I) (A.blkStart D.S.K I.1 - (4 : ℤ) * (↑D.S.K : ℤ)))))
    (_ : ∀ (j : Fin (4 : ℕ)) (hj : j ≠ l), D.AnchorOKAt G I j fun (h : ℕ) => anc h j hj)
    (xs : ℝ)
    (_ : xs ∈ dyadicGridCell A.G I.1 I.2)
    (Aw : ℕ)
    (Iw : ℕ),
  let H : Finset ℕ :=
    ModeComponents.upperHeights D.SP.Jst D.SP.δs
  ∀ (_ : (0 : ℝ) ≤ (2 : ℝ) * D.SP.δs)
    (_ : ∀ (j : Fin (4 : ℕ)), (D.Ms j G).zc.dim ≤ D.S.dmax)
    (_ : ∀ (j : Fin (4 : ℕ)), (0 : ℝ) < (D.Ms j G).δc)
    (_ : (fun (k : Fin (4 : ℕ)) => if k = l then (1 : Fin (3 : ℕ)) else (0 : Fin (3 : ℕ))) l
      = (1 : Fin (3 : ℕ)))
    (_ : ∀ (k : Fin (4 : ℕ)), k ≠ l → (fun (k : Fin (4 : ℕ)) => if k = l then (1 : Fin (3 :
      ℕ)) else (0 : Fin (3 : ℕ))) k = (0 : Fin (3 : ℕ)))
    (_ : ∀ h ∈ H, ∀ (j : Fin (4 : ℕ)) (hj : j ≠ l) {n : ℕ} (asg : Fin n → Fin (4 : ℕ)) (w :
      Fin n → ℕ) (F : Finset (D.Ms j G).Md), D.TorusFormAt G I j (h - D.SP.Δ) xs
      (D.maskSel G I j asg w h F) (D.maskShift G I j asg w h F xs (anc h j hj F)) (anc h
      j hj F))
    (n : ℕ)
    (a : Fin n → Fin (4 : ℕ)),
  (∑ w ∈ Fintype.piFinset fun (_ : Fin n) => H, ∑ h ∈ H, ((↑H.card : ℝ) ^ (n + (1 :
    ℕ)))⁻¹ * ∑ p ∈ Fintype.piFinset fun (l_1 : Fin (4 : ℕ)) => Finset.image (D.coreCls
    G I h l_1) (Finset.filter (roleMask (D.slotGood G I l_1) l_1 a w h) (compIdx (fun
    (k : Fin (4 : ℕ)) => if k = l then (1 : Fin (3 : ℕ)) else (0 : Fin (3 : ℕ))) (fun
    (l : Fin (4 : ℕ)) => D.compsAt l G I) l_1)), D.threeCoef G I xs (h - D.SP.Δ) l
    (D.slopes3 G I xs l anc h p) (D.toLeaf.sv l G I) J Aw Iw * ∏ j : Fin (4 : ℕ), if
    hj : j = l then (1 : ℝ) else D.maskSize G I j a w h (p j) xs (anc h j hj (p j))) ≤
    (2 : ℝ) ^ (4 : ℕ) * (((2 : ℝ) * D.SP.δs) ^ n) ^ (1 / 4 : ℝ) * ∑ h ∈ H, (↑H.card :
    ℝ)⁻¹ * ∑ p ∈ Fintype.piFinset fun (j : Fin (4 : ℕ)) => if j = l then {∅} else
    D.goodCls G I j h, D.threeCoef G I xs (h - D.SP.Δ) l (D.slopes3 G I xs l anc h p)
    (D.toLeaf.sv l G I) J Aw Iw * ∏ j : Fin (4 : ℕ), if j = l then (1 : ℝ) else (6 :
    ℝ) * D.clsSize G I j (p j)

private theorem three_core_principal_conclusion_4 : ThreeCorePrincipalConclusion4Statement := by
  classical
  intro κ' c₀ A bf fp D Cj CA CT CK δs W hV hCA hCT hd2 hD hB hQ hSP hstab I hI G J hDg Kf hKf
    hQBf hεw hcard hΛ hJ hδs hδ16 hδJ l anc hanc xs hxs Aw Iw H hρ0 hdimj hδcj hσl hσk htor n a
  -- the moments over the words and final heights
  have hZ : 0 ≤ ∑ h ∈ H, (H.card : ℝ)⁻¹ *
      ∑ p ∈ Fintype.piFinset (fun j => if j = l then {∅} else D.goodCls G I j h),
        D.threeCoef G I xs (h - D.SP.Δ) l (D.slopes3 G I xs l anc h p) (D.toLeaf.sv l G I) J
            Aw Iw * ∏ j, (if j = l then 1 else 6 * D.clsSize G I j (p j)) := by
    refine Finset.sum_nonneg fun h _ => mul_nonneg (by positivity) (Finset.sum_nonneg
      fun p _ => mul_nonneg (D.threeCoef_nonneg hI G xs _ l _ _ J Aw Iw)
        (Finset.prod_nonneg fun j _ => ?_))
    split_ifs
    · exact zero_le_one
    · exact mul_nonneg (by norm_num) (D.clsSize_nonneg G I j (p j))
  by_cases hal : ∃ i, a i = l
  · obtain ⟨i, hi⟩ := hal
    have hE : ∀ w h, Fintype.piFinset (fun k => ((compIdx (fun k' => if k' = l then (1 : Fin 3)
        else 0) (fun l' => D.compsAt l' G I) k).filter
          (roleMask (D.slotGood G I k) k a w h)).image (D.coreCls G I h k)) = ∅ := by
      intro w h
      rw [Fintype.piFinset_eq_empty]
      refine ⟨l, ?_⟩
      rw [Finset.image_eq_empty, Finset.filter_eq_empty_iff]
      intro o ho hmask
      rw [compIdx_of_side _ _ (by simp), Finset.mem_singleton] at ho
      subst ho
      exact (hmask.2.1 i hi) trivial
    simp only [hE, Finset.sum_empty, mul_zero, Finset.sum_const_zero]
    exact mul_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg (pow_nonneg hρ0 _) _)) hZ
  · push Not at hal
    have hImg : ∀ w h, Fintype.piFinset (fun k => ((compIdx (fun k' => if k' = l then (1 : Fin 3)
        else 0) (fun l' => D.compsAt l' G I) k).filter
          (roleMask (D.slotGood G I k) k a w h)).image (D.coreCls G I h k)) ⊆
        Fintype.piFinset (fun j => if j = l then {∅} else D.goodCls G I j h) := by
      intro w h p hp
      rw [Fintype.mem_piFinset] at hp ⊢
      intro k
      obtain ⟨o, ho, hop⟩ := Finset.mem_image.mp (hp k)
      rw [← hop]
      obtain ⟨ho1, ho2⟩ := Finset.mem_filter.mp ho
      by_cases hk : k = l
      · subst hk
        rw [compIdx_of_side _ _ (by simp), Finset.mem_singleton] at ho1
        subst ho1
        simp [coreCls]
      · rw [ite_eq_right hk]
        rw [compIdx_of_core _ _ (hσk k hk), Finset.mem_map] at ho1
        obtain ⟨K, hK, rfl⟩ := ho1
        exact Finset.mem_image.mpr ⟨K, Finset.mem_filter.mpr ⟨hK, ho2.1⟩, rfl⟩
    have hpw := principal_word_average H (m₀ := 4) (by norm_num) a
      (π := fun _ => ∀ l, Finset (D.Ms l G).Md)
      (fun h => Fintype.piFinset (fun j => if j = l then {∅} else D.goodCls G I j h))
      (fun h p => D.threeCoef G I xs (h - D.SP.Δ) l (D.slopes3 G I xs l anc h p)
        (D.toLeaf.sv l G I) J Aw Iw)
      (fun h p _ => D.threeCoef_nonneg hI G xs _ l _ _ J Aw Iw)
      (fun h p j w => if hj : j = l then 1 else
        D.maskSize G I j a w h (p j) xs (anc h j hj (p j)))
      (fun h p j w => by
        split_ifs with hj
        · exact zero_le_one
        · exact D.maskSize_nonneg G I j a w h (p j) xs (anc h j hj (p j)))
      (fun h p j => if j = l then 1 else 6 * D.clsSize G I j (p j))
      (fun h p j => by
        split_ifs
        · exact zero_le_one
        · exact mul_nonneg (by norm_num) (D.clsSize_nonneg G I j (p j))) hρ0
      (fun h hh p hp j w hw => ?_) (fun h hh p hp j => ?_)
    · have h4 : ((4 : ℕ) : ℝ) = 4 := by norm_num
      rw [h4] at hpw
      refine le_trans ?_ hpw
      refine Finset.sum_le_sum fun w _ => Finset.sum_le_sum fun h _ => ?_
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact Finset.sum_le_sum_of_subset_of_nonneg (hImg w h) fun p _ _ =>
        mul_nonneg (D.threeCoef_nonneg hI G xs _ l _ _ J Aw Iw)
          (Finset.prod_nonneg fun j _ => by
            split_ifs with hj
            · exact zero_le_one
            · exact D.maskSize_nonneg G I j a w h (p j) xs (anc h j hj (p j)))
    · by_cases hj : j = l
      · rw [dite_eq_left hj, ite_eq_left hj]; norm_num
      · rw [dite_eq_right hj, ite_eq_right hj]
        have hpj := Fintype.mem_piFinset.mp hp j
        rw [ite_eq_right hj] at hpj
        obtain ⟨m, hm, hmF⟩ := D.mem_goodCls hpj
        have hr := D.role_size_moments_cls hV hCA hCT hd2 hD hB hQ hSP hstab I j G (hdimj j)
          (hδcj j) (hDg j) (hKf j) hQBf (hεw j) (hcard j) (hΛ j) hJ hδs hδ16 hδJ hh hm hmF a
          (fun w => D.maskShift G I j a w h (p j) xs (anc h j hj (p j))) (anc h j hj (p j)) hxs
          (fun w _ => htor h hh j hj a w (p j))
        have h1 := hr.1 w hw
        have h0 := D.clsSize_nonneg G I j (p j)
        change D.maskSize G I j a w h (p j) xs (anc h j hj (p j)) ≤ 6 * D.clsSize G I j (p j)
          at h1
        linarith
    · by_cases hj : j = l
      · simp only [dite_eq_left hj, ite_eq_left hj]
        have hcnt : (Finset.univ.filter fun i => a i = j).card = 0 := by
          rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
          intro i _ hi
          exact hal i (hi.trans hj)
        rw [hcnt, pow_zero]
        simp only [one_pow, mul_one, Finset.sum_const, Fintype.card_piFinset, Finset.prod_const,
          Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        by_cases hc : ((H.card : ℕ) : ℝ) ^ n = 0
        · rw [hc]; norm_num
        · rw [mul_inv_cancel₀ hc]; norm_num
      · simp only [dite_eq_right hj, ite_eq_right hj]
        have hpj := Fintype.mem_piFinset.mp hp j
        rw [ite_eq_right hj] at hpj
        obtain ⟨m, hm, hmF⟩ := D.mem_goodCls hpj
        have hr := D.role_size_moments_cls hV hCA hCT hd2 hD hB hQ hSP hstab I j G (hdimj j)
          (hδcj j) (hDg j) (hKf j) hQBf (hεw j) (hcard j) (hΛ j) hJ hδs hδ16 hδJ hh hm hmF a
          (fun w => D.maskShift G I j a w h (p j) xs (anc h j hj (p j))) (anc h j hj (p j)) hxs
          (fun w _ => htor h hh j hj a w (p j))
        have h2 := hr.2
        have h0 : 0 ≤ (2 * D.SP.δs) ^ (Finset.univ.filter fun i => a i = j).card *
            D.clsSize G I j (p j) ^ 2 := mul_nonneg (pow_nonneg hρ0 _) (sq_nonneg _)
        refine h2.trans ?_
        nlinarith only [h0]

open Classical in
/-- Blueprint lines 2463-2582 for the three-core pattern with side role `l` on a leaf cell of the
side states (`eq:principal-core` before binning, with `eq:core-numerical`): with anchors of the
final classes in the core roles (`AnchorOKAt`), the pattern form is at most
`2⁴ Z / (1 - 4 (2δ_*)^{1/4})` plus the
absolute tuple errors `C_{J,A} D_*^{-100} σ Π_{j ≠ l} Σ_{m ∈ r_j} |α_m|` (`σ` the local side size),
where `Z = Σ_{h ∈ H} |H|⁻¹ Σ_p c_p Π_{j ≠ l} 6 σ_{p_j}` with the principal window coefficients
`c_p` (`threeCoef`, `0` for discarded tuples) of the side `S` (`pattern_leaf_bound`,
`masked_group_side`, `three_core_tuple_bound`, `role_size_moments_cls`, `principal_word_average`;
assignments of a failure to the side slot leave no masked tuples). -/
theorem three_core_principal {Cj CA CT CK : ℕ} {δs W : ℝ} (hV : D.S.Valid Cj CA CT CK δs W)
    (hCA : 1 ≤ CA) (hCT : 4 ≤ CT) (hd2 : 2 ≤ D.S.dmax) (hD : 2 ≤ D.S.Dstar)
    (hB : 2 ≤ D.S.Bstar) (hQ : 1 ≤ D.S.Q0) (hSP : D.SP = D.S.sideParams δs) (hstab : D.Stab)
    (hK : D.S.Dstar ^ 600 ≤ (2 : ℝ) ^ D.S.K) {I : ℤ × ℤ} (hI : I ∈ A.cells) (G : bf.Grp)
    (hz : ∀ j, (D.Ms j G).zc = (D.Ms 0 G).zc) (hdim : (D.Ms 0 G).zc.dim ≤ D.S.dmax) {δ : ℝ}
    (hδ : 0 < δ) (hdδ : 8 * (D.Ms 0 G).zc.dim * δ ≤ 1) (hδ8 : δ ≤ 1 / 8)
    (hδc : ∀ j, (D.Ms j G).δc = δ) (hcl : ∀ j, (D.Ms j G).cl = slotCoeff j)
    (hρ : ∀ j k, (D.Ms j G).ρ k ∈ Set.Icc (0 : ℝ) 1)
    (hQC : ∀ a b, ∃ k : ℤ, (D.S.Q0 : ℝ) * ((D.Ms 0 G).zc.C a b : ℝ) = k) {Cm : ℝ}
    (hCm0 : 0 ≤ Cm) (hCm : ∀ a b, |((D.Ms 0 G).zc.C a b : ℝ)| ≤ Cm)
    {Kt : ℕ} (hQB : (D.S.Q0 : ℝ) * 2 ^ (Kt + 1) ≤ D.S.Bstar)
    (hτc : cutTail (D.Ms 0 G).zc.dim δ Kt ≤ (D.S.Dstar ^ 300)⁻¹)
    (hτm : multTail (D.Ms 0 G).zc.dim (δ / 2) D.S.Q0 Cm Kt ≤ (D.S.Dstar ^ 300)⁻¹)
    (hMN : multNorm (D.Ms 0 G).zc.dim (δ / 2) D.S.Q0 Cm ≤ D.S.Dstar)
    (hCN : cutNorm (D.Ms 0 G).zc.dim δ ≤ D.S.Dstar) {J : ℕ} (hJ3 : 3 ≤ J)
    (hDg : ∀ j, gaugeSqNorm (D.Ms j G).zc.dim (D.Ms j G).δc ≤ D.S.Dstar) {Kf : ℕ}
    (hKf : ∀ j, 2 * gaugeTail (D.Ms j G).zc.dim (D.Ms j G).δc / 2 ^ Kf * D.S.Dstar ^ 300 ≤ 1)
    (hQBf : (D.S.Q0 : ℝ) * 2 ^ (Kf + 1) ≤ D.S.Bstar)
    (hεw : ∀ j m, D.S.Dstar⁻¹ ≤ (D.Ms j G).L.εM m)
    (hcard : ∀ j, (((D.Ms j G).alive (ancAt A.G (D.preAt I)
      (A.blkStart D.S.K I.1 - 4 * D.S.K))).card : ℝ) ≤ D.S.Dstar)
    (hΛ : ∀ j, (D.Ms j G).Λ ≤ D.S.Dstar) (hJ : 2 ≤ D.SP.Jst) (hδs : 0 < D.SP.δs)
    (hδ16 : D.SP.δs ≤ 1 / 16) (hδJ : ⌈4 * D.SP.δs * D.SP.Jst⌉₊ ≤ D.SP.Jst)
    (hq : 4 * (2 * D.SP.δs) ^ (1 / (4 : ℝ)) < 1)
    (l : Fin 4) (anc : ℕ → ∀ j, j ≠ l → Finset (D.Ms j G).Md →
      (D.Ms j G).alive (ancAt A.G (D.preAt I) (A.blkStart D.S.K I.1 - 4 * D.S.K)))
    (hanc : ∀ j (hj : j ≠ l), D.AnchorOKAt G I j (fun h => anc h j hj)) {xs : ℝ}
    (hxs : xs ∈ dyadicGridCell A.G I.1 I.2)
    (L : ∀ l G, LiftData (bf.Lab ⊕ Fin fp.Mc) (D.Ms l G).Md) (Aw Iw : ℕ)
    (hAw : 1 ≤ Aw) (hIw : D.U0 ≤ 2 ^ (Iw + 1)) :
    ‖fp.Λc I (patternPiece (fun l => D.coreAt l G I) (fun l => D.toLeaf.sv l G I)
        (fun l => D.errAt L l G I) (fun k => if k = l then 1 else 0))‖ ≤
      2 ^ 4 * (∑ h ∈ ModeComponents.upperHeights D.SP.Jst D.SP.δs,
        ((ModeComponents.upperHeights D.SP.Jst D.SP.δs).card : ℝ)⁻¹ *
          ∑ p ∈ Fintype.piFinset (fun j => if j = l then {∅} else D.goodCls G I j h),
            D.threeCoef G I xs (h - D.SP.Δ) l (D.slopes3 G I xs l anc h p) (D.toLeaf.sv l G I) J
                Aw Iw *
              ∏ j, (if j = l then 1 else 6 * D.clsSize G I j (p j))) /
          (1 - 4 * (2 * D.SP.δs) ^ (1 / (4 : ℝ))) +
      ∑ r ∈ Fintype.piFinset (compIdx (fun k => if k = l then 1 else 0)
          (fun l => D.compsAt l G I)),
        threeErrC κ' J Aw * (D.S.Dstar ^ 100)⁻¹ *
          Real.sqrt ((dyadicGridLength A.G I.1)⁻¹ * ∫ y in (dyadicGridLeft A.G I.1 I.2)..
            dyadicGridLeft A.G I.1 I.2 + dyadicGridLength A.G I.1,
              ‖augPhys (D.toLeaf.sv l G I) y‖ ^ 2) *
          ∏ k, (r k).elim 1
            (fun K => ∑ m ∈ K, ‖D.c k G (A.blkStart D.S.K I.1) (D.preAt I) m‖) := by
  set H := ModeComponents.upperHeights D.SP.Jst D.SP.δs with hH
  have hHJ : ∀ h ∈ H, h ≤ D.SP.Jst := fun h hh => by
    have := (Finset.mem_filter.mp hh).1
    rw [Finset.mem_range] at this
    omega
  have hρ0 : (0 : ℝ) ≤ 2 * D.SP.δs := by linarith
  have hdimj : ∀ j, (D.Ms j G).zc.dim ≤ D.S.dmax := fun j => by rw [hz j]; exact hdim
  have hδcj : ∀ j, 0 < (D.Ms j G).δc := fun j => by rw [hδc j]; exact hδ
  have hσl : (fun k => if k = l then (1 : Fin 3) else 0) l = 1 := by simp
  have hσk : ∀ k, k ≠ l → (fun k => if k = l then (1 : Fin 3) else 0) k = 0 := fun k hk => by
    simp [hk]
  have htor : ∀ h ∈ H, ∀ j (hj : j ≠ l) {n : ℕ} (asg : Fin n → Fin 4) (w : Fin n → ℕ)
      (F : Finset (D.Ms j G).Md), D.TorusFormAt G I j (h - D.SP.Δ) xs
        (D.maskSel G I j asg w h F) (D.maskShift G I j asg w h F xs (anc h j hj F))
          (anc h j hj F) :=
    fun h hh j hj _ asg w F => D.maskShift_spec G I j asg w h F xs (anc h j hj F)
      (D.maskSel_torus_form_of G I j hQ hD (hcard j) (hΛ j) hK asg w F hxs
        (D.maskSel_anchorAt (hanc j hj) hh asg w F))
  rw [(D.pattern_first_success L I G (fun k => if k = l then 1 else 0) hJ hδs hδ16).1]
  refine pattern_leaf_bound (fp.Λc I) (fun k => if k = l then 1 else 0) (fun l => D.compsAt l G I)
    (fun l K => D.compSub l G I K) (fun l => D.toLeaf.sv l G I) (fun l => D.errAt L l G I) H
    (fun l => D.slotGood G I l) (D.tuple_success G I _ hJ hδs hδ16)
    (fun h l => D.coreCls G I h l)
    (fun n a w h p => D.threeCoef G I xs (h - D.SP.Δ) l (D.slopes3 G I xs l anc h p)
      (D.toLeaf.sv l G I) J Aw Iw *
      ∏ j, (if hj : j = l then 1 else D.maskSize G I j a w h (p j) xs (anc h j hj (p j))))
    (fun r => threeErrC κ' J Aw * (D.S.Dstar ^ 100)⁻¹ *
      Real.sqrt ((dyadicGridLength A.G I.1)⁻¹ * ∫ y in (dyadicGridLeft A.G I.1 I.2)..
        dyadicGridLeft A.G I.1 I.2 + dyadicGridLength A.G I.1,
          ‖augPhys (D.toLeaf.sv l G I) y‖ ^ 2) *
      ∏ k, (r k).elim 1 (fun K => ∑ m ∈ K, ‖D.c k G (A.blkStart D.S.K I.1) (D.preAt I) m‖))
    (fun n a w hw h hh p hp => ?_) hρ0 hq (fun n a => ?_)
  · -- the grouped tuples of one history: the three-core tuple bound
    have hpk := Fintype.mem_piFinset.mp hp
    obtain ⟨j₀, hj₀l⟩ : ∃ j₀ : Fin 4, j₀ ≠ l := by
      by_cases h0 : l = 0
      · exact ⟨1, by rw [h0]; decide⟩
      · exact ⟨0, fun e => h0 e.symm⟩
    obtain ⟨o, ho, -⟩ := Finset.mem_image.mp (hpk j₀)
    obtain ⟨ho1, ho2⟩ := Finset.mem_filter.mp ho
    rw [compIdx_of_core _ _ (hσk j₀ hj₀l), Finset.mem_map] at ho1
    obtain ⟨K₀, -, rfl⟩ := ho1
    obtain ⟨m₀, -, hm₀⟩ := ho2.1
    have hgs : (fun k => ∑ o ∈ ((compIdx (fun k' => if k' = l then (1 : Fin 3) else 0)
        (fun l' => D.compsAt l' G I) k).filter (roleMask (D.slotGood G I k) k a w h)).filter
          (fun o => D.coreCls G I h k o = p k),
        slotVal (fun k' => if k' = l then (1 : Fin 3) else 0) (fun l' K => D.compSub l' G I K)
          (fun l' => D.toLeaf.sv l' G I) (fun l' => D.errAt L l' G I) k o) =
        Function.update (fun j => D.compSub j G I
          ((D.maskSel G I j a w h (p j)).map ⟨Subtype.val, Subtype.val_injective⟩)) l
          (D.toLeaf.sv l G I) := by
      funext k
      by_cases hk : k = l
      · rw [hk, Function.update_self]
        exact D.masked_group_side G I _ hσl a w h (hpk l) _ _
      · rw [Function.update_of_ne hk]
        exact D.masked_group_sum G I _ (hσk k hk) a w h (p k) _ _
    rw [hgs, ← Finset.mul_sum, D.masked_group_err3 G I l a w h p (hpk l)]
    have hb := D.three_core_tuple_bound hV hCA hCT hd2 hD hB hQ hSP hI G hz hdim hδ hdδ hδ8 hδc
      hcl hρ hQC hCm0 hCm hQB hτc hτm hMN hCN hJ3 (hHJ h hh) j₀ hm₀ l
      (fun j => D.maskSel G I j a w h (p j))
      (fun j => if hj : j = l then fun _ _ => 0 else
        D.maskShift G I j a w h (p j) xs (anc h j hj (p j)))
      (fun j hj => by simp only [hj, ↓reduceDIte]; exact (htor h hh j hj a w (p j)).1)
      (D.slopes3 G I xs l anc h p) hxs
      (fun j hj => by
        simp only [slopes3, hj, ↓reduceDIte]
        exact (htor h hh j hj a w (p j)).2) (D.toLeaf.sv l G I) Aw Iw hAw hIw
    refine hb.trans (le_of_eq ?_)
    rw [D.threePrin_eq]
    have hprod : ∏ j ∈ Finset.univ.erase l, D.coreSize G I xs (h - D.SP.Δ) j
        (D.maskSel G I j a w h (p j)) (if hj : j = l then fun _ _ => 0 else
          D.maskShift G I j a w h (p j) xs (anc h j hj (p j))) =
        ∏ j, (if hj : j = l then 1 else D.maskSize G I j a w h (p j) xs (anc h j hj (p j))) := by
      rw [← prod_ite_one l]
      refine Finset.prod_congr rfl fun j _ => ?_
      by_cases hj : j = l
      · rw [ite_eq_left hj, dite_eq_left hj]
      · rw [ite_eq_right hj, dite_eq_right hj, dite_eq_right hj]
        rfl
    rw [hprod]
    unfold threeCoef
    split_ifs <;> ring
  · expose_names
    exact @three_core_principal_conclusion_4 κ' c₀ A bf fp D Cj CA CT CK δs W hV hCA hCT hd2 hD hB
      hQ hSP hstab I hI G J hDg Kf hKf hQBf hεw hcard hΛ hJ hδs hδ16 hδJ l anc hanc xs
      hxs Aw Iw hρ0 hdimj hδcj hσl hσk htor n a
end SideInput

end ActiveSetup.BasicFamilies.FamParams

/-- The value `2 C_{J,A} 2^{A+4} (2μ) ν^{-J} Λ^{-(A+1)} (2 b) Π_{j ≠ l} 6 (2σ_j)` of a three-core
dyadic bin `(μ, ν, i, b, σ)` with `Λ = 2^i` (blueprint `eq:principal-core`; the side role `l` bins
the window size `b_Λ`). -/
noncomputable def threeBinVal (κ : LocalKernelClass) (J Aw : ℕ) (l : Fin 4)
    (c : ℝ × ℝ × ℕ × ℝ × (Fin 4 → ℝ)) : ℝ :=
  2 * entryCU κ J Aw * 2 ^ (Aw + 4) * (2 * c.1) * (c.2.1 ^ J)⁻¹ *
    ((2 : ℝ) ^ c.2.2.1)⁻¹ ^ (Aw + 1) * (2 * c.2.2.2.1) *
    ∏ j ∈ Finset.univ.erase l, (6 * (2 * c.2.2.2.2 j))

theorem entryC_eq_mu_nu (κ : LocalKernelClass) (J A : ℕ) (b : ℝ) :
    entryC κ J A b = entryCU κ J A * (min 1 |b| * (max 1 |b| ^ J)⁻¹) := by
  unfold entryC entryCU
  ring

namespace ActiveSetup.BasicFamilies.FamParams
variable {κ' : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ' c₀} {bf : A.BasicFamilies}
  {fp : bf.FamParams}

namespace SideInput
variable (D : fp.SideInput)

/-- The window size `b_Λ` of the side `X` at the shell `Λ = 2^i` (blueprint `eq:side-windows`): the
offset-averaged `ℓ²` norm of the normalized Fourier coefficients of the side in the window. -/
noncomputable def winB (G : bf.Grp) (I : ℤ × ℤ) (xs : ℝ) (h' : ℕ) (l : Fin 4)
    (a : Fin 4 → ℝ)
    (X : ColumnL2 (bf.Lab ⊕ Fin fp.Mc)) (i : ℕ) : ℝ :=
  (dyadicGridLength A.G I.1)⁻¹ *
    Real.sqrt (∫ ρ', sideWinE (D.Ms 0 G).zc l (augPhys X) (dyadicGridLeft A.G I.1 I.2)
      (dyadicGridLength A.G I.1) (D.threeWin G I xs h' l a (2 ^ i)) ρ'
      ∂offsetMeasure (D.Ms 0 G).zc.dim)

/-- The dyadic bin `(μ, ν, i, b_Λ, (σ_j)_j)` of a three-core tuple at the shell `Λ = 2^i`. -/
noncomputable def threeBin (G : bf.Grp) (I : ℤ × ℤ) (xs : ℝ) (h' : ℕ) (l : Fin 4)
    (a : Fin 4 → ℝ)
    (X : ColumnL2 (bf.Lab ⊕ Fin fp.Mc)) (σv : Fin 4 → ℝ) (i : ℕ) :
    ℝ × ℝ × ℕ × ℝ × (Fin 4 → ℝ) :=
  (D.threeMuBand G I xs h' l a, D.threeNuBand G I xs h' l a, i,
    dyadicBand (D.winB G I xs h' l a X i), fun j => dyadicBand (σv j))

open Classical in
/-- The tested three-core tuples and shells of a family: the pairs `(p, i)` passing the three-core
test with positive window size `b_Λ` and positive core sizes. -/
noncomputable def threeTestedOf (G : bf.Grp) (I : ℤ × ℤ) (xs : ℝ) (h' : ℕ) (l : Fin 4)
    {ι : Type*} (T : Finset ι)
    (a : ι → Fin 4 → ℝ)
    (X : ColumnL2 (bf.Lab ⊕ Fin fp.Mc)) (σv : ι → Fin 4 → ℝ) (Iw : ℕ) : Finset (ι × ℕ) :=
  (T ×ˢ Finset.range (Iw + 1)).filter fun q => D.threePasses G I xs h' l (a q.1) ∧
    0 < D.winB G I xs h' l (a q.1) X q.2 ∧ ∀ j, j ≠ l → 0 < σv q.1 j

open Classical in
/-- Blueprint `eq:principal-core` (lines 2577-2582) for three cores (side role `l`), at one final
height: the principal quantity `Σ_p c_p Π_{j ≠ l} 6 σ_{p,j}` (`c_p` the window coefficient of a
passing tuple, `0` for discarded ones) is at most the sum over the occupied dyadic bins
`(μ, ν, Λ, b_Λ, σ)` of `C_{J,A} μ ν^{-J} Λ^{-(A+1)} b_Λ Π_{j ≠ l} σ_j` (with the factors `2` of the
bands) times the number `N` of tested tuples and shells in the bin (zero factors contribute
nothing; `threeBands_spec`, `sum_by_bins`). -/
theorem three_core_binned (hD : 2 ≤ D.S.Dstar) {I : ℤ × ℤ} (hI : I ∈ A.cells) (G : bf.Grp)
    (xs : ℝ) (h' : ℕ) (l : Fin 4) (J Aw Iw : ℕ) {ι : Type*} (T : Finset ι)
    (a : ι → Fin 4 → ℝ)
    (X : ColumnL2 (bf.Lab ⊕ Fin fp.Mc)) (σv : ι → Fin 4 → ℝ) (hσ : ∀ p ∈ T, ∀ j, 0 ≤ σv p j) :
    ∑ p ∈ T, D.threeCoef G I xs h' l (a p) X J Aw Iw *
        ∏ j, (if j = l then 1 else 6 * σv p j) ≤
      ∑ c ∈ (D.threeTestedOf G I xs h' l T a X σv Iw).image
          (fun q => D.threeBin G I xs h' l (a q.1) X (σv q.1) q.2),
        threeBinVal κ' J Aw l c * (((D.threeTestedOf G I xs h' l T a X σv Iw).filter
          fun q => D.threeBin G I xs h' l (a q.1) X (σv q.1) q.2 = c).card : ℝ) := by
  have hr := dyadicGridLength_pos A.G I.1
  have hw := A.adm I hI
  have hD0 : (0 : ℝ) ≤ D.S.Dstar := by linarith
  have hU := D.one_le_U0 hD
  have hEU := entryCU_nonneg hr hw J Aw
  unfold threeTestedOf
  set! term : ι × ℕ → ℝ := fun q => (if D.threePasses G I xs h' l (a q.1) then
      2 * (entryC κ' J Aw (D.threeBeta G I xs h' l (a q.1)) * 2 ^ (Aw + 4) *
        ((2 : ℝ) ^ q.2)⁻¹ ^ (Aw + 1) * D.winB G I xs h' l (a q.1) X q.2) else 0) *
      ∏ j ∈ Finset.univ.erase l, (6 * σv q.1 j) with hterm
  have hexp : ∑ p ∈ T, D.threeCoef G I xs h' l (a p) X J Aw Iw *
      ∏ j, (if j = l then 1 else 6 * σv p j) = ∑ q ∈ T ×ˢ Finset.range (Iw + 1), term q := by
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [prod_ite_one l (fun j => 6 * σv p j)]
    unfold threeCoef threeC
    simp only [hterm]
    split_ifs
    · rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      unfold winB
      ring
    · simp
  rw [hexp, ← Finset.sum_filter_of_ne (p := fun q => D.threePasses G I xs h' l (a q.1) ∧
    0 < D.winB G I xs h' l (a q.1) X q.2 ∧ ∀ j, j ≠ l → 0 < σv q.1 j) fun q hq hne => ?_]
  · have hsb := sum_by_bins ((T ×ˢ Finset.range (Iw + 1)).filter fun q =>
      D.threePasses G I xs h' l (a q.1) ∧ 0 < D.winB G I xs h' l (a q.1) X q.2 ∧
        ∀ j, j ≠ l → 0 < σv q.1 j)
      (fun q => D.threeBin G I xs h' l (a q.1) X (σv q.1) q.2) (threeBinVal κ' J Aw l) term
    refine hsb fun q hq => ?_
    obtain ⟨hqT, hpass, hb, hpos⟩ := Finset.mem_filter.mp hq
    have hpT := (Finset.mem_product.mp hqT).1
    obtain ⟨hμ1, hμ2, hμ3, -, hν1, -, hν3, -⟩ := D.threeBands_spec hD0 hU hpass
    set β := D.threeBeta G I xs h' l (a q.1)
    set μb := D.threeMuBand G I xs h' l (a q.1)
    set νb := D.threeNuBand G I xs h' l (a q.1)
    have hνb0 : 0 < νb := by linarith
    have hν0 : 0 < max 1 |β| := lt_of_lt_of_le one_pos (le_max_left _ _)
    have hU0i : 0 < D.U0⁻¹ := inv_pos.mpr (by linarith)
    have hμb0 : 0 < μb := by linarith
    have hentry : entryC κ' J Aw β ≤ entryCU κ' J Aw * (2 * μb) * (νb ^ J)⁻¹ := by
      rw [entryC_eq_mu_nu, mul_assoc]
      refine mul_le_mul_of_nonneg_left (mul_le_mul hμ2.le (inv_anti₀ (pow_pos hνb0 J)
        (pow_le_pow_left₀ hνb0.le hν1 J)) (inv_nonneg.mpr (pow_nonneg hν0.le J)) (by linarith)) hEU
    have hprod : ∏ j ∈ Finset.univ.erase l, (6 * σv q.1 j) ≤
        ∏ j ∈ Finset.univ.erase l, (6 * (2 * dyadicBand (σv q.1 j))) :=
      Finset.prod_le_prod₀ (fun j _ => mul_nonneg (by norm_num) (hσ q.1 hpT j))
        fun j _ => mul_le_mul_of_nonneg_left (lt_two_mul_dyadicBand _).le (by norm_num)
    have hP0 : 0 ≤ ∏ j ∈ Finset.univ.erase l, (6 * σv q.1 j) :=
      Finset.prod_nonneg fun j _ => mul_nonneg (by norm_num) (hσ q.1 hpT j)
    have hbb := (lt_two_mul_dyadicBand (D.winB G I xs h' l (a q.1) X q.2)).le
    have hΛ0 : 0 ≤ ((2 : ℝ) ^ q.2)⁻¹ ^ (Aw + 1) := by positivity
    have hent0 : 0 ≤ entryC κ' J Aw β := entryC_nonneg hr hw J Aw β
    have hb0 : 0 ≤ D.winB G I xs h' l (a q.1) X q.2 :=
      mul_nonneg (inv_nonneg.mpr hr.le) (Real.sqrt_nonneg _)
    have hbb0 : 0 < dyadicBand (D.winB G I xs h' l (a q.1) X q.2) := dyadicBand_pos _
    have hP'0 : 0 ≤ ∏ j ∈ Finset.univ.erase l, (6 * (2 * dyadicBand (σv q.1 j))) :=
      Finset.prod_nonneg fun j _ => by have := dyadicBand_pos (σv q.1 j); positivity
    have h1 : entryC κ' J Aw β * 2 ^ (Aw + 4) * ((2 : ℝ) ^ q.2)⁻¹ ^ (Aw + 1) *
        D.winB G I xs h' l (a q.1) X q.2 ≤
        entryCU κ' J Aw * (2 * μb) * (νb ^ J)⁻¹ * 2 ^ (Aw + 4) * ((2 : ℝ) ^ q.2)⁻¹ ^ (Aw + 1) *
          (2 * dyadicBand (D.winB G I xs h' l (a q.1) X q.2)) :=
      mul_le_mul (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hentry (by positivity))
        hΛ0) hbb hb0 (by positivity)
    simp only [hterm, hpass, ↓reduceIte]
    unfold threeBinVal threeBin
    simp only
    calc 2 * (entryC κ' J Aw β * 2 ^ (Aw + 4) * ((2 : ℝ) ^ q.2)⁻¹ ^ (Aw + 1) *
          D.winB G I xs h' l (a q.1) X q.2) * ∏ j ∈ Finset.univ.erase l, (6 * σv q.1 j)
        ≤ 2 * (entryCU κ' J Aw * (2 * μb) * (νb ^ J)⁻¹ * 2 ^ (Aw + 4) *
          ((2 : ℝ) ^ q.2)⁻¹ ^ (Aw + 1) *
          (2 * dyadicBand (D.winB G I xs h' l (a q.1) X q.2))) *
          ∏ j ∈ Finset.univ.erase l, (6 * (2 * dyadicBand (σv q.1 j))) :=
          mul_le_mul (mul_le_mul_of_nonneg_left h1 (by norm_num)) hprod hP0 (by positivity)
      _ = _ := by ring
  · by_contra hQ
    apply hne
    simp only [hterm]
    by_cases hpass : D.threePasses G I xs h' l (a q.1)
    · simp only [hpass, ↓reduceIte]
      by_cases hb : D.winB G I xs h' l (a q.1) X q.2 = 0
      · rw [hb]; ring
      · have hz : ∃ j, j ≠ l ∧ σv q.1 j = 0 := by
          by_contra hz
          push Not at hz
          have hpT := (Finset.mem_product.mp hq).1
          have hb0 : 0 < D.winB G I xs h' l (a q.1) X q.2 := by
            refine lt_of_le_of_ne ?_ (Ne.symm hb)
            unfold winB
            exact mul_nonneg (inv_nonneg.mpr hr.le) (Real.sqrt_nonneg _)
          exact hQ ⟨hpass, hb0, fun j hj => lt_of_le_of_ne (hσ q.1 hpT j) (Ne.symm (hz j hj))⟩
        obtain ⟨j, hj, hj0⟩ := hz
        rw [Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩)
          (by rw [hj0, mul_zero]), mul_zero]
    · simp only [hpass, ↓reduceIte, zero_mul]

end SideInput

end ActiveSetup.BasicFamilies.FamParams

namespace ActiveSetup.BasicFamilies.FamParams
variable {κ' : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ' c₀} {bf : A.BasicFamilies}
  {fp : bf.FamParams}

namespace SideInput
variable (D : fp.SideInput)

/-- The tested three-core tuples and shells at a final height `h` (side role `l`, side `X`):
tuples of final classes of good core components in the core roles passing the three-core test
with the slopes of their anchors, together with the shells `Λ = 2^i ≤ 2^{I_w}` of positive window
size, all core class sizes positive. -/
noncomputable def threeTested (G : bf.Grp) (I : ℤ × ℤ) (xs : ℝ) (l : Fin 4)
    (anc : ℕ → ∀ j, j ≠ l → Finset (D.Ms j G).Md →
      (D.Ms j G).alive (ancAt A.G (D.preAt I) (A.blkStart D.S.K I.1 - 4 * D.S.K)))
    (X : ColumnL2 (bf.Lab ⊕ Fin fp.Mc)) (Iw h : ℕ) :
    Finset ((∀ j, Finset (D.Ms j G).Md) × ℕ) :=
  D.threeTestedOf G I xs (h - D.SP.Δ) l
    (Fintype.piFinset (fun j => if j = l then {∅} else D.goodCls G I j h))
    (fun p => D.slopes3 G I xs l anc h p) X (fun p j => D.clsSize G I j (p j)) Iw

/-- The dyadic bin of a three-core tuple of final classes and a shell at the final height `h`. -/
noncomputable def threeBinOf (G : bf.Grp) (I : ℤ × ℤ) (xs : ℝ) (l : Fin 4)
    (anc : ℕ → ∀ j, j ≠ l → Finset (D.Ms j G).Md →
      (D.Ms j G).alive (ancAt A.G (D.preAt I) (A.blkStart D.S.K I.1 - 4 * D.S.K)))
    (X : ColumnL2 (bf.Lab ⊕ Fin fp.Mc)) (h : ℕ) (q : (∀ j, Finset (D.Ms j G).Md) × ℕ) :
    ℝ × ℝ × ℕ × ℝ × (Fin 4 → ℝ) :=
  D.threeBin G I xs (h - D.SP.Δ) l (D.slopes3 G I xs l anc h q.1) X
    (fun j => D.clsSize G I j (q.1 j)) q.2

open Classical in
/-- Blueprint `eq:principal-core` (lines 2577-2582) for the three-core pattern with side role `l`
on a leaf cell of the side states: the pattern form is at most
`2⁴/(1 - 4(2δ_*)^{1/4}) Σ_{h ∈ H} |H|⁻¹ Σ_{bins} C_{J,A} μ ν^{-J} Λ^{-(A+1)} b_Λ Π_{j ≠ l} σ_j N`
(with the factors `2` of the bands), plus the absolute tuple errors of `eq:core-numerical`. Here
`N = N_{h,bin}` is the number of tested tuples of final classes and shells `Λ = 2^i` in the bin
(at most once per tuple and shell). The side bins its window size `b_Λ`, the core roles bin their
component sizes. -/
theorem three_core_principal_bins {Cj CA CT CK : ℕ} {δs W : ℝ}
    (hV : D.S.Valid Cj CA CT CK δs W) (hCA : 1 ≤ CA) (hCT : 4 ≤ CT) (hd2 : 2 ≤ D.S.dmax)
    (hD : 2 ≤ D.S.Dstar) (hB : 2 ≤ D.S.Bstar) (hQ : 1 ≤ D.S.Q0) (hSP : D.SP = D.S.sideParams δs)
    (hstab : D.Stab) (hK : D.S.Dstar ^ 600 ≤ (2 : ℝ) ^ D.S.K) {I : ℤ × ℤ} (hI : I ∈ A.cells)
    (G : bf.Grp) (hz : ∀ j, (D.Ms j G).zc = (D.Ms 0 G).zc) (hdim : (D.Ms 0 G).zc.dim ≤ D.S.dmax)
    {δ : ℝ} (hδ : 0 < δ) (hdδ : 8 * (D.Ms 0 G).zc.dim * δ ≤ 1) (hδ8 : δ ≤ 1 / 8)
    (hδc : ∀ j, (D.Ms j G).δc = δ) (hcl : ∀ j, (D.Ms j G).cl = slotCoeff j)
    (hρ : ∀ j k, (D.Ms j G).ρ k ∈ Set.Icc (0 : ℝ) 1)
    (hQC : ∀ a b, ∃ k : ℤ, (D.S.Q0 : ℝ) * ((D.Ms 0 G).zc.C a b : ℝ) = k) {Cm : ℝ}
    (hCm0 : 0 ≤ Cm) (hCm : ∀ a b, |((D.Ms 0 G).zc.C a b : ℝ)| ≤ Cm)
    {Kt : ℕ} (hQB : (D.S.Q0 : ℝ) * 2 ^ (Kt + 1) ≤ D.S.Bstar)
    (hτc : cutTail (D.Ms 0 G).zc.dim δ Kt ≤ (D.S.Dstar ^ 300)⁻¹)
    (hτm : multTail (D.Ms 0 G).zc.dim (δ / 2) D.S.Q0 Cm Kt ≤ (D.S.Dstar ^ 300)⁻¹)
    (hMN : multNorm (D.Ms 0 G).zc.dim (δ / 2) D.S.Q0 Cm ≤ D.S.Dstar)
    (hCN : cutNorm (D.Ms 0 G).zc.dim δ ≤ D.S.Dstar) {J : ℕ} (hJ3 : 3 ≤ J)
    (hDg : ∀ j, gaugeSqNorm (D.Ms j G).zc.dim (D.Ms j G).δc ≤ D.S.Dstar) {Kf : ℕ}
    (hKf : ∀ j, 2 * gaugeTail (D.Ms j G).zc.dim (D.Ms j G).δc / 2 ^ Kf * D.S.Dstar ^ 300 ≤ 1)
    (hQBf : (D.S.Q0 : ℝ) * 2 ^ (Kf + 1) ≤ D.S.Bstar)
    (hεw : ∀ j m, D.S.Dstar⁻¹ ≤ (D.Ms j G).L.εM m)
    (hcard : ∀ j, (((D.Ms j G).alive (ancAt A.G (D.preAt I)
      (A.blkStart D.S.K I.1 - 4 * D.S.K))).card : ℝ) ≤ D.S.Dstar)
    (hΛ : ∀ j, (D.Ms j G).Λ ≤ D.S.Dstar) (hJ : 2 ≤ D.SP.Jst) (hδs : 0 < D.SP.δs)
    (hδ16 : D.SP.δs ≤ 1 / 16) (hδJ : ⌈4 * D.SP.δs * D.SP.Jst⌉₊ ≤ D.SP.Jst)
    (hq : 4 * (2 * D.SP.δs) ^ (1 / (4 : ℝ)) < 1)
    (l : Fin 4) (anc : ℕ → ∀ j, j ≠ l → Finset (D.Ms j G).Md →
      (D.Ms j G).alive (ancAt A.G (D.preAt I) (A.blkStart D.S.K I.1 - 4 * D.S.K)))
    (hanc : ∀ j (hj : j ≠ l), D.AnchorOKAt G I j (fun h => anc h j hj)) {xs : ℝ}
    (hxs : xs ∈ dyadicGridCell A.G I.1 I.2)
    (L : ∀ l G, LiftData (bf.Lab ⊕ Fin fp.Mc) (D.Ms l G).Md) (Aw Iw : ℕ)
    (hAw : 1 ≤ Aw) (hIw : D.U0 ≤ 2 ^ (Iw + 1)) :
    ‖fp.Λc I (patternPiece (fun l => D.coreAt l G I) (fun l => D.toLeaf.sv l G I)
        (fun l => D.errAt L l G I) (fun k => if k = l then 1 else 0))‖ ≤
      2 ^ 4 * (∑ h ∈ ModeComponents.upperHeights D.SP.Jst D.SP.δs,
        ((ModeComponents.upperHeights D.SP.Jst D.SP.δs).card : ℝ)⁻¹ *
          ∑ c ∈ (D.threeTested G I xs l anc (D.toLeaf.sv l G I) Iw h).image
              (D.threeBinOf G I xs l anc (D.toLeaf.sv l G I) h),
            threeBinVal κ' J Aw l c *
              (((D.threeTested G I xs l anc (D.toLeaf.sv l G I) Iw h).filter
                fun q => D.threeBinOf G I xs l anc (D.toLeaf.sv l G I) h q = c).card : ℝ)) /
          (1 - 4 * (2 * D.SP.δs) ^ (1 / (4 : ℝ))) +
      ∑ r ∈ Fintype.piFinset (compIdx (fun k => if k = l then 1 else 0)
          (fun l => D.compsAt l G I)),
        threeErrC κ' J Aw * (D.S.Dstar ^ 100)⁻¹ *
          Real.sqrt ((dyadicGridLength A.G I.1)⁻¹ * ∫ y in (dyadicGridLeft A.G I.1 I.2)..
            dyadicGridLeft A.G I.1 I.2 + dyadicGridLength A.G I.1,
              ‖augPhys (D.toLeaf.sv l G I) y‖ ^ 2) *
          ∏ k, (r k).elim 1
            (fun K => ∑ m ∈ K, ‖D.c k G (A.blkStart D.S.K I.1) (D.preAt I) m‖) := by
  refine (D.three_core_principal hV hCA hCT hd2 hD hB hQ hSP hstab hK hI G hz hdim hδ hdδ hδ8
    hδc hcl hρ hQC hCm0 hCm hQB hτc hτm hMN hCN hJ3 hDg hKf hQBf hεw hcard hΛ hJ hδs hδ16 hδJ
    hq l anc hanc hxs L Aw Iw hAw hIw).trans (add_le_add ?_ le_rfl)
  have hden : 0 < 1 - 4 * (2 * D.SP.δs) ^ (1 / (4 : ℝ)) := by linarith only [hq]
  refine div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun h _ =>
    mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr (Nat.cast_nonneg _))) (by norm_num)) hden.le
  have hb := D.three_core_binned hD hI G xs (h - D.SP.Δ) l J Aw Iw
    (Fintype.piFinset (fun j => if j = l then {∅} else D.goodCls G I j h))
    (fun p => D.slopes3 G I xs l anc h p) (D.toLeaf.sv l G I) (fun p j => D.clsSize G I j (p j))
    fun p _ j => D.clsSize_nonneg G I j (p j)
  refine le_trans hb (le_of_eq ?_)
  rfl

end SideInput

end ActiveSetup.BasicFamilies.FamParams

/-! ## The declaration `frequency-tests` (blueprint lines 2482-2585) -/

end TrilinearHT.Auto

end
