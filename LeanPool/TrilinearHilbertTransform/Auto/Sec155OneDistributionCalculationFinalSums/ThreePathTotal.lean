/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import LeanPool.TrilinearHilbertTransform.Auto.Sec155OneDistributionCalculationFinalSums.FourPathTotal

/-!
# Trilinear Hilbert transform: three_path_total
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
private def ThreePathTotalStage1Statement : Prop :=
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
    (_ : (↑D.S.dmax : ℝ) ≤ D.S.Dstar)
    (qG : bf.Grp → ℕ)
    (_ : ∀ (G : bf.Grp), (1 : ℕ) ≤ qG G ∧ qG G ≤ D.S.Q0)
    (J : ℕ)
    (_ : (1 : ℕ) ≤ J)
    (Aw : ℕ)
    (Iw : ℕ)
    (_ : (2 : ℝ) ^ Iw ≤ (2 : ℝ) * D.U0)
    (l : Fin (4 : ℕ))
    (T : Finset (ℤ × ℤ))
    (gs : ℤ × ℤ → Finset bf.Grp)
    (z : bf.Grp → ChartTag)
    (_ : ∀ I ∈ T, ∀ G ∈ gs I, (∀ (j : Fin (4 : ℕ)), (8 : ℝ) * (D.Ms j G).Λ ≤ D.S.Ξ) ∧ (∀ (j :
      Fin (4 : ℕ)), (D.Ms j G).zc = z G) ∧ (z G).dim ≤ D.S.dmax)
    (H : Finset ℕ)
    (_ : ∀ h ∈ H, h ≤ D.SP.Jst)
    (rep : ℕ → (G : bf.Grp) → (j : Fin (4 : ℕ)) → ℕ → ℕ → ℤ × (ℤ × ℤ) × (D.Ms j G).Md → (D.Ms j
      G).Md)
    (hrep : ∀ h ∈ H, ∀ I ∈ T, ∀ G ∈ gs I, ∀ (j : Fin (4 : ℕ)), (D.withQ0 (qG G)).RepOK G j h T
      (rep h G j))
    (anc : (I : ℤ × ℤ) → (G : bf.Grp) → D.AncNe3 G I l → ℕ → (j : Fin (4 : ℕ)) → j ≠ l → Finset
      (D.Ms j G).Md → ↥((D.Ms j G).alive (ancAt A.G (D.preAt I) (A.blkStart D.S.K I.1 -
      (4 : ℤ) * (↑D.S.K : ℤ)))))
    (_ : ∀ (h : ℕ) (hh : h ∈ H) (I : ℤ × ℤ) (hI : I ∈ T) (G : bf.Grp) (hG : G ∈ gs I) (hA :
      D.AncNe3 G I l) (j : Fin (4 : ℕ)) (hj : j ≠ l) (F : Finset ((D.withQ0 (qG G)).Ms j
      G).Md) (hF : F ∈ (D.withQ0 (qG G)).goodCls G I j h), anc I G hA h j hj F =
      (D.withQ0 (qG G)).repAnchor G I j h (rep h G j) (hrep h hh I hI G hG j).left hF)
    (U : ℝ)
    (ε : ℝ)
    (_ : (0 : ℝ) < ε)
    (_ : ε ≤ U)
    (K : ℝ)
    (K₁ : ℝ)
    (_ : (0 : ℝ) ≤ K)
    (_ : (0 : ℝ) ≤ K₁)
    (y : ℝ)
    (_ : ∀ h ∈ H, (10 : ℕ) ≤ h → ∀ (c : ℝ × ℝ × ℕ × ℝ × (Fin (4 : ℕ) → ℝ)), (0 : ℝ) < c.1 →
      c.1 ≤ (1 : ℝ) → (1 : ℝ) ≤ c.2.1 → (∀ (i : Fin (4 : ℕ)), (0 : ℝ) < threeAmp l c i)
      → (∀ (j : Fin (4 : ℕ)), ε ≤ threeAmp l c j ∧ threeAmp l c j ≤ U ∧ ∃ (k : ℤ),
      threeAmp l c j = (2 : ℝ) ^ k) → ∀ (κ : Fin (4 : ℕ) → ℕ × ℕ), (∀ (i : Fin (4 : ℕ))
      (hi : i ≠ l), ∑ G ∈ pathGroups T gs y, (↑((D.withQ0 (qG G)).threeUsedReps G h y l
      (pathCell A.G T y) (fun (s : ℤ) => anc (pathCell A.G T y s) G) Iw c κ (pathDepths
      T gs y G) i hi).card : ℝ) ≤ K * threeAmp l c i ^ (-2 : ℝ)) ∧ ∑ G ∈ pathGroups T gs
      y, ∑ s ∈ pathDepths T gs y G, (D.withQ0 (qG G)).sideWeight G l (pathCell A.G T y)
      c.2.2.2.1 s ≤ K * threeAmp l c l ^ (-2 : ℝ)),
  let p : ℝ :=
    (1 : ℝ) - (1 / 300 : ℝ) / (4 : ℝ)
  ∀ (_ : (0 : ℝ) < p)
    (_ : D.SP.Δ = (10 : ℕ)),
  let Ty : Finset (ℤ × ℤ) :=
    {I ∈ T | y ∈ dyadicGridCell A.G I.1 I.2}
  let Q : ℝ :=
    K₁ * (↑H.card : ℝ)⁻¹
  ∀ (_ : Q = K₁ * (↑H.card : ℝ)⁻¹)
    (_ : (0 : ℝ) ≤ Q),
  let f : ℕ → (Fin (4 : ℕ) → ℕ × ℕ) → ℤ × ℤ → bf.Grp → ℝ × ℝ × ℕ × ℝ × (Fin (4 : ℕ) → ℝ) → ℝ :=
    fun (h : ℕ) (κ : Fin (4 : ℕ) → ℕ × ℕ) (I : ℤ × ℤ) (G : bf.Grp) (c : ℝ × ℝ × ℕ × ℝ ×
      (Fin (4 : ℕ) → ℝ)) => (Q * threeBinVal κ' J Aw l c * (D.withQ0 (qG G)).threeCntA G
      I y l (anc I G) Iw h c κ) ^ p
  let BY : ℕ → Finset (ℝ × ℝ × ℕ × ℝ × (Fin (4 : ℕ) → ℝ)) :=
    fun (h : ℕ) => Ty.biUnion fun (I : ℤ × ℤ) => (gs I).biUnion fun (G : bf.Grp) =>
      (D.withQ0 (qG G)).threeRetBinsA G I y l (anc I G) Iw h ε
  ∀ (_ : ∀ h ∈ H, ∀ I ∈ Ty, ∀ G ∈ gs I, ∀ c ∈ (D.withQ0 (qG G)).threeRetBinsA G I y l (anc I
      G) Iw h ε, ∀ (j : Fin (4 : ℕ)), threeAmp l c j ≤ U)
    (_ : ∀ h ∈ H, ∀ c ∈ BY h, ((∃ (k : ℤ), c.1 = (2 : ℝ) ^ k) ∧ c.1 ≤ (1 : ℝ) ∧ (∃ (k : ℤ),
      c.2.1 = (2 : ℝ) ^ k) ∧ (1 : ℝ) ≤ c.2.1 ∧ c.2.2.1 ≤ Iw ∧ c.2.2.2.2 l = (1 : ℝ) ∧ ∀
      (j : Fin (4 : ℕ)), ε ≤ (fun (j : Fin (4 : ℕ)) => if j = l then c.2.2.2.1 else
      c.2.2.2.2 j) j ∧ (fun (j : Fin (4 : ℕ)) => if j = l then c.2.2.2.1 else c.2.2.2.2
      j) j ≤ U ∧ ∃ (k : ℤ), (fun (j : Fin (4 : ℕ)) => if j = l then c.2.2.2.1 else
      c.2.2.2.2 j) j = (2 : ℝ) ^ k) ∧ (0 : ℝ) < c.1 ∧ ∀ (i : Fin (4 : ℕ)), (0 : ℝ) <
      threeAmp l c i)
    (_ : ∀ I ∈ Ty, ∀ G ∈ gs I, ∀ h ∈ H, ∀ (κ : Fin (4 : ℕ) → ℕ × ℕ), (K₁ * ((↑H.card : ℝ)⁻¹ *
      ∑ c ∈ (D.withQ0 (qG G)).threeRetBinsA G I y l (anc I G) Iw h ε, threeBinVal κ' J
      Aw l c * (D.withQ0 (qG G)).threeCntA G I y l (anc I G) Iw h c κ)) ^ p ≤ ∑ c ∈
      (D.withQ0 (qG G)).threeRetBinsA G I y l (anc I G) Iw h ε, f h κ I G c)
    (_ : ∑ I ∈ Ty, ∑ x ∈ gs I ×ˢ H ×ˢ D.threeTypes l, ∑ c ∈ (D.withQ0 (qG x.1)).threeRetBinsA
      x.1 I y l (anc I x.1) Iw x.2.1 ε, f x.2.1 x.2.2 I x.1 c = ∑ h ∈ H, ∑ κ ∈
      D.threeTypes l, ∑ I ∈ Ty, ∑ G ∈ gs I, ∑ c ∈ (D.withQ0 (qG G)).threeRetBinsA G I y
      l (anc I G) Iw h ε, f h κ I G c)
    (_ : ∀ h ∈ H, ∀ (κ : Fin (4 : ℕ) → ℕ × ℕ), ∑ I ∈ Ty, ∑ G ∈ gs I, ∑ c ∈ (D.withQ0 (qG
      G)).threeRetBinsA G I y l (anc I G) Iw h ε, f h κ I G c ≤ ∑ c ∈ BY h, ∑ G ∈
      pathGroups T gs y, ∑ s ∈ pathDepths T gs y G, f h κ (pathCell A.G T y s) G c),
  ∑ I ∈ Ty, ∑ x ∈ gs I ×ˢ H ×ˢ D.threeTypes l, (K₁ * ((↑H.card : ℝ)⁻¹ * ∑ c ∈
    (D.withQ0 (qG x.1)).threeRetBinsA x.1 I y l (anc I x.1) Iw x.2.1 ε, threeBinVal κ'
    J Aw l c * (D.withQ0 (qG x.1)).threeCntA x.1 I y l (anc I x.1) Iw x.2.1 c x.2.2))
    ^ p ≤ (↑H.card : ℝ) * (↑(D.threeTypes l).card : ℝ) * ((K₁ * ((8 : ℝ) * entryCU κ'
    J Aw * (2 : ℝ) ^ (Aw + (4 : ℕ)) * (12 : ℝ) ^ (3 : ℕ))) ^ p * (D.fourCc * K ^ ((2 :
    ℝ) - (1 / 300 : ℝ) / (2 : ℝ))) * (((↑Iw : ℝ) + (1 : ℝ)) * ((Real.logb (2 : ℝ) (U /
    ε) + (1 : ℝ)) ^ (4 : ℕ) * bandC p J)))




private theorem three_path_total_stage_1 : ThreePathTotalStage1Statement := by
  classical
  intro κ' c₀ A bf fp D Cj CA CT CK δs W hV hCA hCT hd2 hD hB hQ0 hSP hdD qG hqG J hJ Aw Iw hIw l
    T gs z hGc H hH rep hrep anc hanc U ε hε hεU K K₁ hK hK₁ y hcap p hp0 hΔ Ty Q hQ hQnn f BY
    hamp hgen hstep hreorg hext
  have hbin : ∀ h ∈ H, ∀ κ, ∀ c ∈ BY h, ∑ G ∈ pathGroups (A := A) T gs y,
      ∑ s ∈ pathDepths (A := A) T gs y G, f h κ (pathCell A.G T y s) G c ≤
      (Q * (8 * entryCU κ' J Aw * 2 ^ (Aw + 4) * 12 ^ 3)) ^ p *
        (D.fourCc * K ^ (2 - (1 / 300 : ℝ) / 2)) *
        (c.1 ^ p * ((c.2.1 ^ J)⁻¹) ^ p * (1 + Real.log (8 * c.2.1 / c.1)) ^ 4) := by
    intro h hh κ c hc
    obtain ⟨⟨-, hμ1, -, hν1, -, -, hamp⟩, hμ, hσ⟩ := hgen h hh c hc
    have h10 : 10 ≤ h := by
      by_contra hlt
      push Not at hlt
      obtain ⟨I, -, hc'⟩ := Finset.mem_biUnion.mp hc
      obtain ⟨G, -, hc'⟩ := Finset.mem_biUnion.mp hc'
      unfold threeRetBinsA at hc'
      split_ifs at hc' with hA
      swap
      · exact Finset.notMem_empty c hc'
      unfold threeRetBins at hc'
      rw [(D.withQ0 (qG G)).threeTested_eq_empty G I y l (anc I G hA) _ Iw
        (by rw [SideInput.withQ0_SP, hΔ]; exact hlt)] at hc'
      obtain ⟨p', hp', -⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hc').1
      exact Finset.notMem_empty p' hp'
    obtain ⟨hcapc, hcapl⟩ := hcap h hh h10 c hμ hμ1 hν1 hσ hamp κ
    refine (D.three_path_bin_bound hV hCA hCT hd2 hD hB hQ0 hSP hdD qG hqG J Aw Iw hIw l T gs z hGc
        h
      h10 (hH h hh) (rep h) (hrep h hh) (fun I G => anc I G)
      (fun I hI G hG hA j hj F hF => hanc h hh I hI G hG hA j hj F hF) y c ⟨hμ, hμ1, hν1⟩ hσ κ hK
      hQnn hcapc hcapl).trans (le_of_eq ?_)
    ring
  have hC4 : 0 ≤ 8 * entryCU κ' J Aw * 2 ^ (Aw + 4) * 12 ^ 3 := by
    have := entryCU_nonneg' κ' J Aw; positivity
  have hCcK : 0 ≤ D.fourCc * K ^ (2 - (1 / 300 : ℝ) / 2) := by
    have hm : 0 ≤ D.multPoly := by
      unfold multPoly
      have : 0 ≤ Real.log (288 * (D.S.Dstar ^ 5 * D.S.H)) := by
        refine Real.log_nonneg ?_
        have hH2 := hV.two_le_H hd2 hD hB hQ0
        have h5 : (1 : ℝ) ≤ D.S.Dstar ^ 5 := one_le_pow₀ (by linarith)
        nlinarith only [hH2, h5]
      have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
      positivity
    have hl : 0 ≤ D.ellPoly := by
      unfold ellPoly
      have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
      have := Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) D.S.dmax; linarith :
        (1 : ℝ) ≤ (D.S.dmax : ℝ) + 1)
      positivity
    unfold fourCc
    have := Real.rpow_nonneg hK (2 - (1 / 300 : ℝ) / 2)
    positivity
  have hband : ∀ h ∈ H, ∑ c ∈ BY h, c.1 ^ p * ((c.2.1 ^ J)⁻¹) ^ p *
      (1 + Real.log (8 * c.2.1 / c.1)) ^ 4 ≤
        (Iw + 1) * ((Real.logb 2 (U / ε) + 1) ^ 4 * bandC p J) :=
    fun h hh => (three_bins_sum_le hp0 J hJ l Iw hε hεU (BY h) fun c hc =>
      (hgen h hh c hc).1).trans (le_of_eq (by unfold bandC; ring))
  have hQK : ∀ h ∈ H, (Q * (8 * entryCU κ' J Aw * 2 ^ (Aw + 4) * 12 ^ 3)) ^ p ≤
      (K₁ * (8 * entryCU κ' J Aw * 2 ^ (Aw + 4) * 12 ^ 3)) ^ p := by
    intro h hh
    have hcard : (1 : ℝ) ≤ H.card := by exact_mod_cast Finset.card_pos.mpr ⟨h, hh⟩
    have hQle : Q ≤ K₁ := by
      rw [hQ]
      calc K₁ * (H.card : ℝ)⁻¹ ≤ K₁ * 1 :=
            mul_le_mul_of_nonneg_left (inv_le_one_of_one_le₀ hcard) hK₁
        _ = K₁ := mul_one _
    exact Real.rpow_le_rpow (mul_nonneg hQnn hC4) (mul_le_mul_of_nonneg_right hQle hC4) hp0.le
  calc _ ≤ ∑ I ∈ Ty, ∑ x ∈ gs I ×ˢ (H ×ˢ D.threeTypes l),
        ∑ c ∈ (D.withQ0 (qG x.1)).threeRetBinsA x.1 I y l (anc I x.1) Iw x.2.1 ε,
          f x.2.1 x.2.2 I x.1 c := by
        refine Finset.sum_le_sum fun I hI => Finset.sum_le_sum fun x hx => ?_
        obtain ⟨hG, hx2⟩ := Finset.mem_product.mp hx
        obtain ⟨hh, -⟩ := Finset.mem_product.mp hx2
        exact hstep I hI x.1 hG x.2.1 hh x.2.2
    _ = _ := hreorg
    _ ≤ ∑ h ∈ H, ∑ κ ∈ D.threeTypes l, ∑ c ∈ BY h, ∑ G ∈ pathGroups (A := A) T gs y,
        ∑ s ∈ pathDepths (A := A) T gs y G, f h κ (pathCell A.G T y s) G c :=
        Finset.sum_le_sum fun h hh => Finset.sum_le_sum fun κ _ => hext h hh κ
    _ ≤ ∑ h ∈ H, ∑ κ ∈ D.threeTypes l, ∑ c ∈ BY h,
        (Q * (8 * entryCU κ' J Aw * 2 ^ (Aw + 4) * 12 ^ 3)) ^ p * (D.fourCc * K ^ (2 - (1 / 300 :
            ℝ) / 2)) *
          (c.1 ^ p * ((c.2.1 ^ J)⁻¹) ^ p * (1 + Real.log (8 * c.2.1 / c.1)) ^ 4) :=
        Finset.sum_le_sum fun h hh => Finset.sum_le_sum fun κ _ => Finset.sum_le_sum fun c hc =>
          hbin h hh κ c hc
    _ ≤ ∑ h ∈ H, ∑ _κ ∈ D.threeTypes l, (K₁ * (8 * entryCU κ' J Aw * 2 ^ (Aw + 4) * 12 ^ 3)) ^ p *
        (D.fourCc * K ^ (2 - (1 / 300 : ℝ) / 2)) *
          ((Iw + 1) * ((Real.logb 2 (U / ε) + 1) ^ 4 * bandC p J)) := by
        refine Finset.sum_le_sum fun h hh => Finset.sum_le_sum fun κ _ => ?_
        rw [← Finset.mul_sum]
        have hs0 : 0 ≤ ∑ c ∈ BY h, c.1 ^ p * ((c.2.1 ^ J)⁻¹) ^ p *
            (1 + Real.log (8 * c.2.1 / c.1)) ^ 4 := Finset.sum_nonneg fun c hc => by
          obtain ⟨⟨-, -, -, hν, -⟩, hμ, -⟩ := hgen h hh c hc
          have hl : 0 ≤ 1 + Real.log (8 * c.2.1 / c.1) := by
            have : (1 : ℝ) ≤ 8 * c.2.1 / c.1 := by
              rw [le_div_iff₀ hμ]; obtain ⟨⟨-, hμ1, -⟩, -⟩ := hgen h hh c hc; linarith
            linarith [Real.log_nonneg this]
          have : 0 ≤ (c.2.1 ^ J)⁻¹ := inv_nonneg.mpr (pow_nonneg (by linarith) J)
          have := hμ.le
          positivity
        exact mul_le_mul (mul_le_mul_of_nonneg_right (hQK h hh) hCcK) (hband h hh) hs0
          (mul_nonneg (Real.rpow_nonneg (by positivity) _) hCcK)
    _ = _ := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        unfold bandC
        ring


open Classical in
/-- Blueprint lines 2783-2817 at one point `y` for three cores with side role `l`: the powered
retained principal
quantities of the cells of the path of `y` (over their groups, the heights and the role types) sum
to at most `|H| |types| (K₁ C_J 2 · 12⁴)^p C_c K^{2-c/2} (log₂(U/ε) + 1)⁴ C_band`. -/
theorem three_path_total {Cj CA CT CK : ℕ} {δs W : ℝ} (hV : D.S.Valid Cj CA CT CK δs W)
    (hCA : 1 ≤ CA) (hCT : 4 ≤ CT) (hd2 : 2 ≤ D.S.dmax) (hD : 2 ≤ D.S.Dstar)
    (hB : 2 ≤ D.S.Bstar) (hQ0 : 1 ≤ D.S.Q0) (hSP : D.SP = D.S.sideParams δs)
    (hdD : (D.S.dmax : ℝ) ≤ D.S.Dstar) (qG : bf.Grp → ℕ) (hqG : ∀ G, 1 ≤ qG G ∧ qG G ≤ D.S.Q0) (J :
        ℕ)
        (hJ : 1 ≤ J) (Aw Iw : ℕ)
    (hIw : (2 : ℝ) ^ Iw ≤ 2 * D.U0) (l : Fin 4) (T : Finset (ℤ × ℤ))
    (gs : ℤ × ℤ → Finset bf.Grp) (z : bf.Grp → ChartTag)
    (hGc : ∀ I ∈ T, ∀ G ∈ gs I, (∀ j, 8 * (D.Ms j G).Λ ≤ D.S.Ξ) ∧
      (∀ j, (D.Ms j G).zc = z G) ∧ (z G).dim ≤ D.S.dmax)
    (H : Finset ℕ) (hH : ∀ h ∈ H, h ≤ D.SP.Jst)
    (rep : ℕ → ∀ G j, ℕ → ℕ → ℤ × (ℤ × ℤ) × (D.Ms j G).Md → (D.Ms j G).Md)
    (hrep : ∀ h ∈ H, ∀ I ∈ T, ∀ G ∈ gs I, ∀ j, (D.withQ0 (qG G)).RepOK G j h T (rep h G j))
    (anc : ∀ (I : ℤ × ℤ) (G : bf.Grp), D.AncNe3 G I l → ℕ → ∀ j, j ≠ l → Finset (D.Ms j G).Md →
      (D.Ms j G).alive (ancAt A.G (D.preAt I) (A.blkStart D.S.K I.1 - 4 * D.S.K)))
    (hanc : ∀ h (hh : h ∈ H), ∀ I (hI : I ∈ T), ∀ G (hG : G ∈ gs I), ∀ (hA : D.AncNe3 G I l) j
      (hj : j ≠ l) F (hF : F ∈ (D.withQ0 (qG G)).goodCls G I j h),
      anc I G hA h j hj F =
        (D.withQ0 (qG G)).repAnchor G I j h (rep h G j) (hrep h hh I hI G hG j).1 hF)
    {U ε : ℝ} (hε : 0 < ε) (hεU : ε ≤ U)
    (hU : ∀ I ∈ T, ∀ G ∈ gs I, ∀ h ∈ H, ∀ j, j ≠ l → ∀ F ∈ (D.withQ0 (qG G)).goodCls G I j h,
      (D.withQ0 (qG G)).clsSize G I j F ≤ U)
    (hUs : ∀ I ∈ T, ∀ G ∈ gs I, Real.sqrt ((dyadicGridLength A.G I.1)⁻¹ *
      ∫ y in (dyadicGridLeft A.G I.1 I.2)..dyadicGridLeft A.G I.1 I.2 + dyadicGridLength A.G I.1,
        ‖augPhys ((D.withQ0 (qG G)).toLeaf.sv l G I) y‖ ^ 2) ≤ U)
    {K K₁ : ℝ} (hK : 0 ≤ K) (hK₁ : 0 ≤ K₁) (y : ℝ)
    (hcap : ∀ h ∈ H, 10 ≤ h → ∀ c : ℝ × ℝ × ℕ × ℝ × (Fin 4 → ℝ), 0 < c.1 → c.1 ≤ 1 →
      1 ≤ c.2.1 → (∀ i, 0 < threeAmp l c i) →
      (∀ j, ε ≤ threeAmp l c j ∧ threeAmp l c j ≤ U ∧
        ∃ k : ℤ, threeAmp l c j = (2 : ℝ) ^ k) → ∀ κ, (∀ i (hi : i ≠ l),
        ∑ G ∈ pathGroups (A := A) T gs y, (((D.withQ0 (qG G)).threeUsedReps G h y l (pathCell A.G T
            y)
          (fun s => anc (pathCell A.G T y s) G) Iw c κ (pathDepths (A := A) T gs y G) i
            hi).card : ℝ) ≤ K * threeAmp l c i ^ (-2 : ℝ)) ∧
        ∑ G ∈ pathGroups (A := A) T gs y, ∑ s ∈ pathDepths (A := A) T gs y G,
          (D.withQ0 (qG G)).sideWeight G l (pathCell A.G T y) c.2.2.2.1 s ≤ K * threeAmp l c l ^ (-2
              : ℝ)) :
    ∑ I ∈ T with y ∈ dyadicGridCell A.G I.1 I.2, ∑ x ∈ gs I ×ˢ (H ×ˢ D.threeTypes l),
      (K₁ * ((H.card : ℝ)⁻¹ * ∑ c ∈ (D.withQ0 (qG x.1)).threeRetBinsA x.1 I y l (anc I x.1) Iw x.2.1
          ε,
        threeBinVal κ' J Aw l c * (D.withQ0 (qG x.1)).threeCntA x.1 I y l (anc I x.1) Iw x.2.1 c
            x.2.2)) ^
        (1 - (1 / 300 : ℝ) / 4) ≤
      H.card * (D.threeTypes l).card * ((K₁ * (8 * entryCU κ' J Aw * 2 ^ (Aw + 4) * 12 ^ 3)) ^ (1
          - (1 / 300 : ℝ) / 4) *
        (D.fourCc * K ^ (2 - (1 / 300 : ℝ) / 2)) *
        ((Iw + 1) * ((Real.logb 2 (U / ε) + 1) ^ 4 * bandC (1 - (1 / 300 : ℝ) / 4) J))) := by
  set p : ℝ := 1 - (1 / 300 : ℝ) / 4 with hp
  have hp0 : 0 < p := by rw [hp]; norm_num
  have hp1 : p ≤ 1 := by rw [hp]; norm_num
  have hΔ : D.SP.Δ = 10 := by rw [hSP]; rfl
  set Ty := T.filter fun I => y ∈ dyadicGridCell A.G I.1 I.2 with hTy
  set! Q := K₁ * (H.card : ℝ)⁻¹ with hQ
  have hQnn : 0 ≤ Q := mul_nonneg hK₁ (inv_nonneg.mpr (Nat.cast_nonneg _))
  set! f : ℕ → (Fin 4 → ℕ × ℕ) → ℤ × ℤ → bf.Grp → ℝ × ℝ × ℕ × ℝ × (Fin 4 → ℝ) → ℝ :=
    fun h κ I G c => (Q * threeBinVal κ' J Aw l c * (D.withQ0 (qG G)).threeCntA G I y l (anc I G) Iw
        h c κ) ^ p
        with hf
  set! BY : ℕ → Finset (ℝ × ℝ × ℕ × ℝ × (Fin 4 → ℝ)) := fun h =>
    Ty.biUnion fun I => (gs I).biUnion fun G => (D.withQ0 (qG G)).threeRetBinsA G I y l (anc I G) Iw
        h ε with hBY
  have hamp : ∀ h ∈ H, ∀ I ∈ Ty, ∀ G ∈ gs I, ∀ c ∈ (D.withQ0 (qG G)).threeRetBinsA G I y l (anc I G)
      Iw h ε,
      ∀ j, threeAmp l c j ≤ U := by
    intro h hh I hI G hG c hc j
    unfold threeRetBinsA at hc
    split_ifs at hc with hA
    swap
    · exact absurd hc (Finset.notMem_empty _)
    obtain ⟨hc1, -⟩ := Finset.mem_filter.mp hc
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hc1
    have hIT := (Finset.mem_filter.mp hI).1
    unfold threeTested threeTestedOf at hq
    obtain ⟨hmem, -, hwin, hpos⟩ := Finset.mem_filter.mp hq
    have hgood := Fintype.mem_piFinset.mp (Finset.mem_product.mp hmem).1
    unfold threeAmp
    split_ifs with hjl
    · exact (dyadicBand_le hwin).trans (((D.withQ0 (qG G)).winB_le_sideSize G I _ _ l _ _ q.2).trans
        (hUs I hIT G hG))
    · have hF := hgood j
      simp only [hjl, ↓reduceIte] at hF
      exact (dyadicBand_le (hpos j hjl)).trans (hU I hIT G hG h hh j hjl _ hF)
  have hgen : ∀ h ∈ H, ∀ c ∈ BY h, ((∃ k : ℤ, c.1 = (2 : ℝ) ^ k) ∧ c.1 ≤ 1 ∧
      (∃ k : ℤ, c.2.1 = (2 : ℝ) ^ k) ∧ 1 ≤ c.2.1 ∧ c.2.2.1 ≤ Iw ∧ c.2.2.2.2 l = 1 ∧
      ∀ j, ε ≤ (fun j => if j = l then c.2.2.2.1 else c.2.2.2.2 j) j ∧
        (fun j => if j = l then c.2.2.2.1 else c.2.2.2.2 j) j ≤ U ∧
        ∃ k : ℤ, (fun j => if j = l then c.2.2.2.1 else c.2.2.2.2 j) j = (2 : ℝ) ^ k) ∧
      0 < c.1 ∧ (∀ i, 0 < threeAmp l c i) := by
    intro h hh c hc
    obtain ⟨I, hI, hc⟩ := Finset.mem_biUnion.mp hc
    obtain ⟨G, hG, hc⟩ := Finset.mem_biUnion.mp hc
    have hc' := hc
    unfold threeRetBinsA at hc'
    split_ifs at hc' with hA
    swap
    · exact absurd hc' (Finset.notMem_empty _)
    obtain ⟨hc1, hcε⟩ := Finset.mem_filter.mp hc'
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ :=
      (D.withQ0 (qG G)).threeBin_basic hD G I y l (anc I G hA) Iw h hc1
    exact ⟨⟨h1, h2, h3, h4, h5, h6, fun j => ⟨hcε j, hamp h hh I hI G hG c hc j, h9 j⟩⟩, h7, h8⟩
  have hval0 : ∀ h ∈ H, ∀ c ∈ BY h, 0 ≤ threeBinVal κ' J Aw l c := by
    intro h hh c hc
    obtain ⟨I, -, hc⟩ := Finset.mem_biUnion.mp hc
    obtain ⟨G, -, hc⟩ := Finset.mem_biUnion.mp hc
    exact (D.withQ0 (qG G)).threeBinVal_nonneg_of_memA hD J Aw hc
  have hf0 : ∀ h ∈ H, ∀ κ I G, ∀ c ∈ BY h, 0 ≤ f h κ I G c := fun h hh κ I G c hc =>
    Real.rpow_nonneg (mul_nonneg (mul_nonneg hQnn (hval0 h hh c hc))
      (D.withQ0 (qG G)).threeCntA_nonneg) p
  have hretBY : ∀ h, ∀ I ∈ Ty, ∀ G ∈ gs I,
      (D.withQ0 (qG G)).threeRetBinsA G I y l (anc I G) Iw h ε ⊆ BY h :=
    fun h I hI G hG c hc => Finset.mem_biUnion.mpr ⟨I, hI, Finset.mem_biUnion.mpr ⟨G, hG, hc⟩⟩
  -- (a) subadditivity of `x^p` over the bins of one configuration
  have hstep : ∀ I ∈ Ty, ∀ G ∈ gs I, ∀ h ∈ H, ∀ κ,
      (K₁ * ((H.card : ℝ)⁻¹ * ∑ c ∈ (D.withQ0 (qG G)).threeRetBinsA G I y l (anc I G) Iw h ε,
        threeBinVal κ' J Aw l c * (D.withQ0 (qG G)).threeCntA G I y l (anc I G) Iw h c κ)) ^ p ≤
      ∑ c ∈ (D.withQ0 (qG G)).threeRetBinsA G I y l (anc I G) Iw h ε, f h κ I G c := by
    intro I hI G hG h hh κ
    have e : K₁ * ((H.card : ℝ)⁻¹ * ∑ c ∈ (D.withQ0 (qG G)).threeRetBinsA G I y l (anc I G) Iw h ε,
        threeBinVal κ' J Aw l c * (D.withQ0 (qG G)).threeCntA G I y l (anc I G) Iw h c κ) =
        ∑ c ∈ (D.withQ0 (qG G)).threeRetBinsA G I y l (anc I G) Iw h ε,
          Q * threeBinVal κ' J Aw l c * (D.withQ0 (qG G)).threeCntA G I y l (anc I G) Iw h c κ := by
      rw [Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun c _ => by rw [hQ]; ring
    rw [e]
    exact rpow_finset_sum_le _ _ (fun c hc => mul_nonneg (mul_nonneg hQnn
      (hval0 h hh c (hretBY h I hI G hG hc))) (D.withQ0 (qG G)).threeCntA_nonneg) hp0 hp1
  -- (b) the configurations: groups, heights, types
  have hreorg : ∑ I ∈ Ty, ∑ x ∈ gs I ×ˢ (H ×ˢ D.threeTypes l),
      ∑ c ∈ (D.withQ0 (qG x.1)).threeRetBinsA x.1 I y l (anc I x.1) Iw x.2.1 ε,
        f x.2.1 x.2.2 I x.1 c =
      ∑ h ∈ H, ∑ κ ∈ D.threeTypes l, ∑ I ∈ Ty, ∑ G ∈ gs I,
        ∑ c ∈ (D.withQ0 (qG G)).threeRetBinsA G I y l (anc I G) Iw h ε, f h κ I G c := by
    simp only [Finset.sum_product]
    calc ∑ I ∈ Ty, ∑ G ∈ gs I, ∑ h ∈ H, ∑ κ ∈ D.threeTypes l,
          ∑ c ∈ (D.withQ0 (qG G)).threeRetBinsA G I y l (anc I G) Iw h ε, f h κ I G c
        = ∑ I ∈ Ty, ∑ h ∈ H, ∑ G ∈ gs I, ∑ κ ∈ D.threeTypes l,
          ∑ c ∈ (D.withQ0 (qG G)).threeRetBinsA G I y l (anc I G) Iw h ε, f h κ I G c :=
          Finset.sum_congr rfl fun I _ => Finset.sum_comm
      _ = ∑ I ∈ Ty, ∑ h ∈ H, ∑ κ ∈ D.threeTypes l, ∑ G ∈ gs I,
          ∑ c ∈ (D.withQ0 (qG G)).threeRetBinsA G I y l (anc I G) Iw h ε, f h κ I G c :=
          Finset.sum_congr rfl fun I _ => Finset.sum_congr rfl fun h _ => Finset.sum_comm
      _ = ∑ h ∈ H, ∑ I ∈ Ty, ∑ κ ∈ D.threeTypes l, ∑ G ∈ gs I,
          ∑ c ∈ (D.withQ0 (qG G)).threeRetBinsA G I y l (anc I G) Iw h ε, f h κ I G c :=
              Finset.sum_comm
      _ = _ := Finset.sum_congr rfl fun h _ => Finset.sum_comm
  -- (c) extend to the bins along the path and reindex by the depths
  have hext : ∀ h ∈ H, ∀ κ, ∑ I ∈ Ty, ∑ G ∈ gs I,
      ∑ c ∈ (D.withQ0 (qG G)).threeRetBinsA G I y l (anc I G) Iw h ε, f h κ I G c ≤
      ∑ c ∈ BY h, ∑ G ∈ pathGroups (A := A) T gs y, ∑ s ∈ pathDepths (A := A) T gs y G,
        f h κ (pathCell A.G T y s) G c := by
    intro h hh κ
    calc _ ≤ ∑ I ∈ Ty, ∑ G ∈ gs I, ∑ c ∈ BY h, f h κ I G c :=
          Finset.sum_le_sum fun I hI => Finset.sum_le_sum fun G hG =>
            Finset.sum_le_sum_of_subset_of_nonneg (hretBY h I hI G hG) fun c hc _ =>
              hf0 h hh κ I G c hc
      _ = ∑ I ∈ Ty, ∑ c ∈ BY h, ∑ G ∈ gs I, f h κ I G c :=
          Finset.sum_congr rfl fun I _ => Finset.sum_comm
      _ = ∑ c ∈ BY h, ∑ I ∈ Ty, ∑ G ∈ gs I, f h κ I G c := Finset.sum_comm
      _ = ∑ c ∈ BY h, ∑ G ∈ pathGroups (A := A) T gs y, ∑ s ∈ pathDepths (A := A) T gs y G,
          f h κ (pathCell A.G T y s) G c := Finset.sum_congr rfl fun c _ => by
          unfold pathGroups pathDepths
          convert path_sum_reindex A.G T gs y (fun I G => f h κ I G c)
  -- (d) the per-bin path bound
  expose_names
  exact @three_path_total_stage_1 κ' c₀ A bf fp D Cj CA CT CK δs W hV hCA hCT hd2 hD hB hQ0 hSP
    hdD qG hqG J hJ Aw Iw hIw l T gs z hGc H hH rep hrep anc hanc U ε hε hεU K K₁ hK hK₁ y hcap
    hp0 hΔ hQ hQnn hamp hgen hstep hreorg hext

open Classical in
/-- Blueprint `eq:core-final` (lines 2808-2817) for the three-core patterns with side role `l` on
the side states:
let `T` be the retained cells under the root `R` with their groups `g(I)`, the anchors the
hereditary representatives, and assume the principal bounds of `eq:principal-core`
(`‖Λ_{I,G}‖ ≤ K₁ ×` the height-averaged bin sum `+ err_{I,G}`), the retained amplitudes `σ ≤ U`,
at most `D_*` alive modes, and the path caps of `eq:top-count` along every retained path.
Removing the negligible amplitudes (`< ε`), `eq:min-power` with subadditivity of `x^p`, the path
estimates (`three_path_total`) and `eq:path` give, with `p = 1 - 1/1200`,
`Σ_I |I| min(η, C_I) ≤ η^{1/1200} |R| M_p + Σ_I |I| Σ_G (err_{I,G} + K₁ · negligible)`,
where `M_p = |H| |types| (K₁ C₃)^p C_c K^{2-c/2} (I_w + 1) (log₂(U/ε) + 1)⁴ C_band` is polynomial
in the parameters (`P^{C₄}`). -/
theorem three_core_final_side {Cj CA CT CK : ℕ} {δs W : ℝ} (hV : D.S.Valid Cj CA CT CK δs W)
    (hCA : 1 ≤ CA) (hCT : 4 ≤ CT) (hd2 : 2 ≤ D.S.dmax) (hD : 2 ≤ D.S.Dstar)
    (hB : 2 ≤ D.S.Bstar) (hQ0 : 1 ≤ D.S.Q0) (hSP : D.SP = D.S.sideParams δs)
    (hdD : (D.S.dmax : ℝ) ≤ D.S.Dstar) (qG : bf.Grp → ℕ) (hqG : ∀ G, 1 ≤ qG G ∧ qG G ≤ D.S.Q0) (J :
        ℕ) (hJ : 1 ≤ J) (Aw Iw : ℕ)
    (hIw : (2 : ℝ) ^ Iw ≤ 2 * D.U0) (l : Fin 4) (R : ℤ × ℤ) (T : Finset (ℤ × ℤ))
    (hT : ∀ I ∈ T, dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G R.1 R.2)
    (gs : ℤ × ℤ → Finset bf.Grp) (z : bf.Grp → ChartTag)
    (hGc : ∀ I ∈ T, ∀ G ∈ gs I, (∀ j, 8 * (D.Ms j G).Λ ≤ D.S.Ξ) ∧
      (∀ j, (D.Ms j G).zc = z G) ∧ (z G).dim ≤ D.S.dmax)
    (H : Finset ℕ) (hH : ∀ h ∈ H, h ≤ D.SP.Jst)
    (rep : ℕ → ∀ G j, ℕ → ℕ → ℤ × (ℤ × ℤ) × (D.Ms j G).Md → (D.Ms j G).Md)
    (hrep : ∀ h ∈ H, ∀ I ∈ T, ∀ G ∈ gs I, ∀ j, (D.withQ0 (qG G)).RepOK G j h T (rep h G j))
    (anc : ∀ (I : ℤ × ℤ) (G : bf.Grp), D.AncNe3 G I l → ℕ → ∀ j, j ≠ l → Finset (D.Ms j G).Md →
      (D.Ms j G).alive (ancAt A.G (D.preAt I) (A.blkStart D.S.K I.1 - 4 * D.S.K)))
    (hanc : ∀ h (hh : h ∈ H), ∀ I (hI : I ∈ T), ∀ G (hG : G ∈ gs I), ∀ (hA : D.AncNe3 G I l) j
      (hj : j ≠ l) F (hF : F ∈ (D.withQ0 (qG G)).goodCls G I j h),
      anc I G hA h j hj F =
        (D.withQ0 (qG G)).repAnchor G I j h (rep h G j) (hrep h hh I hI G hG j).1 hF)
    (hcard : ∀ I ∈ T, ∀ G ∈ gs I, ∀ j, (((D.Ms j G).alive (ancAt A.G (D.preAt I)
      (A.blkStart D.S.K I.1 - 4 * D.S.K))).card : ℝ) ≤ D.S.Dstar)
    {U ε : ℝ} (hε : 0 < ε) (hεU : ε ≤ U)
    (hU : ∀ I ∈ T, ∀ G ∈ gs I, ∀ h ∈ H, ∀ j, j ≠ l → ∀ F ∈ (D.withQ0 (qG G)).goodCls G I j h,
      (D.withQ0 (qG G)).clsSize G I j F ≤ U)
    (hUs : ∀ I ∈ T, ∀ G ∈ gs I, Real.sqrt ((dyadicGridLength A.G I.1)⁻¹ *
      ∫ y in (dyadicGridLeft A.G I.1 I.2)..dyadicGridLeft A.G I.1 I.2 + dyadicGridLength A.G I.1,
        ‖augPhys ((D.withQ0 (qG G)).toLeaf.sv l G I) y‖ ^ 2) ≤ U)
    {K K₁ : ℝ} (hK : 0 ≤ K) (hK₁ : 0 ≤ K₁)
    (hcap : ∀ y, ∀ h ∈ H, 10 ≤ h → ∀ c : ℝ × ℝ × ℕ × ℝ × (Fin 4 → ℝ), 0 < c.1 → c.1 ≤ 1 →
      1 ≤ c.2.1 → (∀ i, 0 < threeAmp l c i) →
      (∀ j, ε ≤ threeAmp l c j ∧ threeAmp l c j ≤ U ∧
        ∃ k : ℤ, threeAmp l c j = (2 : ℝ) ^ k) → ∀ κ, (∀ i (hi : i ≠ l),
        ∑ G ∈ pathGroups (A := A) T gs y, (((D.withQ0 (qG G)).threeUsedReps G h y l (pathCell A.G T
            y)
          (fun s => anc (pathCell A.G T y s) G) Iw c κ (pathDepths (A := A) T gs y G) i
            hi).card : ℝ) ≤ K * threeAmp l c i ^ (-2 : ℝ)) ∧
        ∑ G ∈ pathGroups (A := A) T gs y, ∑ s ∈ pathDepths (A := A) T gs y G,
          (D.withQ0 (qG G)).sideWeight G l (pathCell A.G T y) c.2.2.2.1 s ≤ K * threeAmp l c l ^
              (-2 : ℝ))
    (Λ3 Err : ℤ × ℤ → bf.Grp → ℝ) (hErr : ∀ I G, 0 ≤ Err I G)
    (hP : ∀ I ∈ T, ∀ G ∈ gs I, ∀ y ∈ dyadicGridCell A.G I.1 I.2, Λ3 I G ≤
      K₁ * ∑ h ∈ H, (H.card : ℝ)⁻¹ * (D.withQ0 (qG G)).threeBinSumA J Aw Iw G I y l (anc I G) h +
        Err I G)
    (CI : ℤ × ℤ → ℝ) (hCI : ∀ I ∈ T, CI I ≤ ∑ G ∈ gs I, Λ3 I G) {η : ℝ} (hη : 0 ≤ η) :
    ∑ I ∈ T, dyadicGridLength A.G I.1 * min η (CI I) ≤
      η ^ (1 - (1 - (1 / 300 : ℝ) / 4)) * (dyadicGridLength A.G R.1 *
        (H.card * (D.threeTypes l).card * ((K₁ * (8 * entryCU κ' J Aw * 2 ^ (Aw + 4) * 12 ^ 3)) ^
          (1 - (1 / 300 : ℝ) / 4) * (D.fourCc * K ^ (2 - (1 / 300 : ℝ) / 2)) *
          ((Iw + 1) * ((Real.logb 2 (U / ε) + 1) ^ 4 * bandC (1 - (1 / 300 : ℝ) / 4) J))))) +
        ∑ I ∈ T, dyadicGridLength A.G I.1 * ∑ G ∈ gs I,
          (Err I G + K₁ * (8 * entryCU κ' J Aw * 2 ^ (Aw + 4) * 12 ^ 3 * ε * U ^ 3 *
            (D.S.Dstar ^ 3 * (Iw + 1)))) := by
  have hNeg0 : 0 ≤ 8 * entryCU κ' J Aw * 2 ^ (Aw + 4) * 12 ^ 3 * ε * U ^ 3 *
            (D.S.Dstar ^ 3 * (Iw + 1)) := by
    have := entryCU_nonneg' κ' J Aw
    have : 0 ≤ U := hε.le.trans hεU
    have : (0 : ℝ) ≤ D.S.Dstar := by linarith
    positivity
  refine core_final_pointwise A.G R T hT (fun I => gs I ×ˢ (H ×ˢ D.threeTypes l))
    (fun I x y => K₁ * ((H.card : ℝ)⁻¹ * ∑ c ∈ (D.withQ0 (qG x.1)).threeRetBinsA x.1 I y l (anc I
        x.1) Iw x.2.1 ε,
      threeBinVal κ' J Aw l c * (D.withQ0 (qG x.1)).threeCntA x.1 I y l (anc I x.1) Iw x.2.1 c
          x.2.2))
    (fun I x y => mul_nonneg hK₁ (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
      (Finset.sum_nonneg fun c hc => mul_nonneg
        ((D.withQ0 (qG x.1)).threeBinVal_nonneg_of_memA hD J Aw hc)
        (D.withQ0 (qG x.1)).threeCntA_nonneg)))
    CI (fun I => ∑ G ∈ gs I, (Err I G + K₁ * (8 * entryCU κ' J Aw * 2 ^ (Aw + 4) * 12 ^ 3 * ε * U
        ^ 3 *
      (D.S.Dstar ^ 3 * (Iw + 1)))))
    (fun I _ => Finset.sum_nonneg fun G _ => add_nonneg (hErr I G) (mul_nonneg hK₁ hNeg0))
    (fun I hI y hy => ?_) hη (by norm_num) (by norm_num) (fun y => ?_)
  · -- the cell decomposition
    refine (hCI I hI).trans ?_
    calc ∑ G ∈ gs I, Λ3 I G ≤ ∑ G ∈ gs I, (K₁ * (∑ h ∈ H, ∑ κ ∈ D.threeTypes l,
          (H.card : ℝ)⁻¹ * ∑ c ∈ (D.withQ0 (qG G)).threeRetBinsA G I y l (anc I G) Iw h ε,
            threeBinVal κ' J Aw l c * (D.withQ0 (qG G)).threeCntA G I y l (anc I G) Iw h c κ +
          8 * entryCU κ' J Aw * 2 ^ (Aw + 4) * 12 ^ 3 * ε * U ^ 3 *
            (D.S.Dstar ^ 3 * (Iw + 1))) + Err I G) := by
          refine Finset.sum_le_sum fun G hG => (hP I hI G hG y hy).trans ?_
          refine add_le_add (mul_le_mul_of_nonneg_left ?_ hK₁) le_rfl
          exact (D.withQ0 (qG G)).three_principal_splitA hD J Aw Iw G I y l (anc I G) H (hcard I hI
              G hG)
            (hε.le.trans hεU) hε.le (hU I hI G hG) (hUs I hI G hG)
      _ = ∑ x ∈ gs I ×ˢ (H ×ˢ D.threeTypes l), K₁ * ((H.card : ℝ)⁻¹ *
          ∑ c ∈ (D.withQ0 (qG x.1)).threeRetBinsA x.1 I y l (anc I x.1) Iw x.2.1 ε,
            threeBinVal κ' J Aw l c * (D.withQ0 (qG x.1)).threeCntA x.1 I y l (anc I x.1) Iw x.2.1 c
                x.2.2) +
          ∑ G ∈ gs I, (Err I G + K₁ * (8 * entryCU κ' J Aw * 2 ^ (Aw + 4) * 12 ^ 3 * ε * U ^ 3 *
            (D.S.Dstar ^ 3 * (Iw + 1)))) := by
          simp only [Finset.sum_product, mul_add, Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun G _ => by ring
  · exact D.three_path_total hV hCA hCT hd2 hD hB hQ0 hSP hdD qG hqG J hJ Aw Iw hIw l T gs z hGc H
      hH rep
      hrep anc hanc hε hεU hU hUs hK hK₁ y (hcap y)

end SideInput

end ActiveSetup.BasicFamilies.FamParams

/-- `min(η, ·)` is subadditive on nonnegative sums (`η ≥ 0`). -/
theorem min_sum_le_sum_min {ι : Type*} (s : Finset ι) (x : ι → ℝ) (hx : ∀ i ∈ s, 0 ≤ x i)
    {η : ℝ} (hη : 0 ≤ η) : min η (∑ i ∈ s, x i) ≤ ∑ i ∈ s, min η (x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hη]
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have hxa := hx a (Finset.mem_insert_self a s)
    have hs := ih fun i hi => hx i (Finset.mem_insert_of_mem hi)
    have hsum0 : 0 ≤ ∑ i ∈ s, x i :=
      Finset.sum_nonneg fun i hi => hx i (Finset.mem_insert_of_mem hi)
    have key : min η (x a + ∑ i ∈ s, x i) ≤ min η (x a) + min η (∑ i ∈ s, x i) := by
      rcases le_total η (x a) with h1 | h1
      · rw [min_eq_left h1]
        have := min_le_left η (x a + ∑ i ∈ s, x i)
        have : 0 ≤ min η (∑ i ∈ s, x i) := le_min hη hsum0
        linarith
      · rw [min_eq_right h1]
        rcases le_total η (∑ i ∈ s, x i) with h2 | h2
        · rw [min_eq_left h2]
          have := min_le_left η (x a + ∑ i ∈ s, x i)
          linarith
        · rw [min_eq_right h2]
          exact min_le_right _ _
    linarith

/-- Blueprint `eq:core-final` over the patterns with at least three cores: if the core quantity of
each cell is at most the sum of the pattern quantities `x_τ(I) ≥ 0`, then
`Σ_I |I| min(η, C_I) ≤ Σ_τ Σ_I |I| min(η, x_τ(I))`, so the bounds for the four-core pattern and the
three-core patterns (`four_core_final_side`, `three_core_final_side`) add up. -/
theorem core_final_patterns (G : RealDyadicGrid) (T : Finset (ℤ × ℤ)) {τ : Type*}
    (P : Finset τ) (x : τ → ℤ × ℤ → ℝ) (hx : ∀ t ∈ P, ∀ I ∈ T, 0 ≤ x t I) (CI : ℤ × ℤ → ℝ)
    (hCI : ∀ I ∈ T, CI I ≤ ∑ t ∈ P, x t I) {η : ℝ} (hη : 0 ≤ η) :
    ∑ I ∈ T, dyadicGridLength G I.1 * min η (CI I) ≤
      ∑ t ∈ P, ∑ I ∈ T, dyadicGridLength G I.1 * min η (x t I) := by
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun I hI => ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (dyadicGridLength_pos G I.1).le
  exact (min_le_min_left η (hCI I hI)).trans
    (min_sum_le_sum_min P (fun t => x t I) (fun t ht => hx t ht I hI) hη)

/-! ## The exported core estimate (declaration `core-estimate`, blueprint lines 2820-2822) -/

end TrilinearHT.Auto

end
