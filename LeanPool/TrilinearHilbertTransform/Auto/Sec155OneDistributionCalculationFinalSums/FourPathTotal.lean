/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

/- Adapted for Lean Pool from roos-j/lean-trilinearht at
7b4209609e6a7fb9d9935973ee8541495f943660. Imports, names, proof organization and
Mathlib interfaces have been updated; original authorship is retained above. -/

public import LeanPool.TrilinearHilbertTransform.Auto.Sec155OneDistributionCalculationFinalSums.Setup

/-!
# Trilinear Hilbert transform: four_path_total
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
private def FourPathTotalStage1Statement : Prop :=
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
    (_ : (2 : ℕ) ≤ D.S.dmax)
    (_ : (2 : ℝ) ≤ D.S.Dstar)
    (_ : (2 : ℝ) ≤ D.S.Bstar)
    (_ : (1 : ℕ) ≤ D.S.Q0)
    (qG : bf.Grp → ℕ)
    (J : ℕ)
    (_ : (1 : ℕ) ≤ J)
    (T : Finset (ℤ × ℤ))
    (gs : ℤ × ℤ → Finset bf.Grp)
    (H : Finset ℕ)
    (anc : (I : ℤ × ℤ) → (G : bf.Grp) → D.AncNe G I → ℕ → (j : Fin (4 : ℕ)) → Finset (D.Ms j
      G).Md → ↥((D.Ms j G).alive (ancAt A.G (D.preAt I) (A.blkStart D.S.K I.1 - (4 : ℤ)
      * (↑D.S.K : ℤ)))))
    (U : ℝ)
    (ε : ℝ)
    (_ : (0 : ℝ) < ε)
    (_ : ε ≤ U)
    (K : ℝ)
    (K₁ : ℝ)
    (_ : (0 : ℝ) ≤ K)
    (_ : (0 : ℝ) ≤ K₁)
    (y : ℝ),
  let p : ℝ :=
    (1 : ℝ) - (1 / 300 : ℝ) / (4 : ℝ)
  ∀ (_ : (0 : ℝ) < p),
  let Ty : Finset (ℤ × ℤ) :=
    {I ∈ T | y ∈ dyadicGridCell A.G I.1 I.2}
  let Q : ℝ :=
    K₁ * (↑H.card : ℝ)⁻¹
  ∀ (_ : Q = K₁ * (↑H.card : ℝ)⁻¹)
    (_ : (0 : ℝ) ≤ Q),
  let f : ℕ → (Fin (4 : ℕ) → ℕ × ℕ) → ℤ × ℤ → bf.Grp → ℝ × ℝ × (Fin (4 : ℕ) → ℝ) → ℝ :=
    fun (h : ℕ) (κ : Fin (4 : ℕ) → ℕ × ℕ) (I : ℤ × ℤ) (G : bf.Grp) (c : ℝ × ℝ × (Fin (4
      : ℕ) → ℝ)) => (Q * fourBinVal κ' J c * (D.withQ0 (qG G)).fourCntA G I y (anc I G)
      h c κ) ^ p
  let BY : ℕ → Finset (ℝ × ℝ × (Fin (4 : ℕ) → ℝ)) :=
    fun (h : ℕ) => Ty.biUnion fun (I : ℤ × ℤ) => (gs I).biUnion fun (G : bf.Grp) =>
      (D.withQ0 (qG G)).fourRetBinsA G I y (anc I G) h ε
  ∀ (_ : ∀ h ∈ H, ∀ c ∈ BY h, ((∃ (k : ℤ), c.1 = (2 : ℝ) ^ k) ∧ c.1 ≤ (1 : ℝ) ∧ (∃ (k : ℤ),
      c.2.1 = (2 : ℝ) ^ k) ∧ (1 : ℝ) ≤ c.2.1 ∧ ∀ (j : Fin (4 : ℕ)), ε ≤ c.2.2 j ∧ c.2.2
      j ≤ U ∧ ∃ (k : ℤ), c.2.2 j = (2 : ℝ) ^ k) ∧ (0 : ℝ) < c.1 ∧ ∀ (i : Fin (4 : ℕ)),
      (0 : ℝ) < c.2.2 i)
    (_ : ∀ I ∈ Ty, ∀ G ∈ gs I, ∀ h ∈ H, ∀ (κ : Fin (4 : ℕ) → ℕ × ℕ), (K₁ * ((↑H.card : ℝ)⁻¹ *
      ∑ c ∈ (D.withQ0 (qG G)).fourRetBinsA G I y (anc I G) h ε, fourBinVal κ' J c *
      (D.withQ0 (qG G)).fourCntA G I y (anc I G) h c κ)) ^ p ≤ ∑ c ∈ (D.withQ0 (qG
      G)).fourRetBinsA G I y (anc I G) h ε, f h κ I G c)
    (_ : ∑ I ∈ Ty, ∑ x ∈ gs I ×ˢ H ×ˢ D.fourTypes, ∑ c ∈ (D.withQ0 (qG x.1)).fourRetBinsA x.1
      I y (anc I x.1) x.2.1 ε, f x.2.1 x.2.2 I x.1 c = ∑ h ∈ H, ∑ κ ∈ D.fourTypes, ∑ I ∈
      Ty, ∑ G ∈ gs I, ∑ c ∈ (D.withQ0 (qG G)).fourRetBinsA G I y (anc I G) h ε, f h κ I
      G c)
    (_ : ∀ h ∈ H, ∀ (κ : Fin (4 : ℕ) → ℕ × ℕ), ∑ I ∈ Ty, ∑ G ∈ gs I, ∑ c ∈ (D.withQ0 (qG
      G)).fourRetBinsA G I y (anc I G) h ε, f h κ I G c ≤ ∑ c ∈ BY h, ∑ G ∈ pathGroups T
      gs y, ∑ s ∈ pathDepths T gs y G, f h κ (pathCell A.G T y s) G c)
    (_ : ∀ h ∈ H, ∀ (κ : Fin (4 : ℕ) → ℕ × ℕ), ∀ c ∈ BY h, ∑ G ∈ pathGroups T gs y, ∑ s ∈
      pathDepths T gs y G, f h κ (pathCell A.G T y s) G c ≤ (Q * (fourKC κ' J * (2 : ℝ)
      * (12 : ℝ) ^ (4 : ℕ))) ^ p * (D.fourCc * K ^ ((2 : ℝ) - (1 / 300 : ℝ) / (2 : ℝ)))
      * (c.1 ^ p * (c.2.1 ^ J)⁻¹ ^ p * ((1 : ℝ) + Real.log ((8 : ℝ) * c.2.1 / c.1)) ^ (4
      : ℕ))),
  ∑ I ∈ Ty, ∑ x ∈ gs I ×ˢ H ×ˢ D.fourTypes, (K₁ * ((↑H.card : ℝ)⁻¹ * ∑ c ∈ (D.withQ0
    (qG x.1)).fourRetBinsA x.1 I y (anc I x.1) x.2.1 ε, fourBinVal κ' J c * (D.withQ0
    (qG x.1)).fourCntA x.1 I y (anc I x.1) x.2.1 c x.2.2)) ^ p ≤ (↑H.card : ℝ) *
    (↑D.fourTypes.card : ℝ) * ((K₁ * (fourKC κ' J * (2 : ℝ) * (12 : ℝ) ^ (4 : ℕ))) ^ p
    * (D.fourCc * K ^ ((2 : ℝ) - (1 / 300 : ℝ) / (2 : ℝ))) * ((Real.logb (2 : ℝ) (U /
    ε) + (1 : ℝ)) ^ (4 : ℕ) * bandC p J))




private theorem four_path_total_stage_1 : FourPathTotalStage1Statement := by
  classical
  intro κ' c₀ A bf fp D Cj CA CT CK δs W hV hd2 hD hB hQ0 qG J hJ T gs H anc U ε hε hεU K K₁ hK
    hK₁ y p hp0 Ty Q hQ hQnn f BY hgen hstep hreorg hext hbin
  have hC4 : 0 ≤ fourKC κ' J * 2 * 12 ^ 4 := by have := fourKC_nonneg κ' J; positivity
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
      (1 + Real.log (8 * c.2.1 / c.1)) ^ 4 ≤ (Real.logb 2 (U / ε) + 1) ^ 4 * bandC p J :=
    fun h hh => four_bins_sum_le hp0 J hJ hε hεU (BY h) fun c hc => (hgen h hh c hc).1
  have hQK : ∀ h ∈ H, (Q * (fourKC κ' J * 2 * 12 ^ 4)) ^ p ≤
      (K₁ * (fourKC κ' J * 2 * 12 ^ 4)) ^ p := by
    intro h hh
    have hcard : (1 : ℝ) ≤ H.card := by exact_mod_cast Finset.card_pos.mpr ⟨h, hh⟩
    have hQle : Q ≤ K₁ := by
      rw [hQ]
      calc K₁ * (H.card : ℝ)⁻¹ ≤ K₁ * 1 :=
            mul_le_mul_of_nonneg_left (inv_le_one_of_one_le₀ hcard) hK₁
        _ = K₁ := mul_one _
    exact Real.rpow_le_rpow (mul_nonneg hQnn hC4) (mul_le_mul_of_nonneg_right hQle hC4) hp0.le
  calc _ ≤ ∑ I ∈ Ty, ∑ x ∈ gs I ×ˢ (H ×ˢ D.fourTypes),
        ∑ c ∈ (D.withQ0 (qG x.1)).fourRetBinsA x.1 I y (anc I x.1) x.2.1 ε, f x.2.1 x.2.2 I x.1 c :=
            by
        refine Finset.sum_le_sum fun I hI => Finset.sum_le_sum fun x hx => ?_
        obtain ⟨hG, hx2⟩ := Finset.mem_product.mp hx
        obtain ⟨hh, -⟩ := Finset.mem_product.mp hx2
        exact hstep I hI x.1 hG x.2.1 hh x.2.2
    _ = _ := hreorg
    _ ≤ ∑ h ∈ H, ∑ κ ∈ D.fourTypes, ∑ c ∈ BY h, ∑ G ∈ pathGroups (A := A) T gs y,
        ∑ s ∈ pathDepths (A := A) T gs y G, f h κ (pathCell A.G T y s) G c :=
        Finset.sum_le_sum fun h hh => Finset.sum_le_sum fun κ _ => hext h hh κ
    _ ≤ ∑ h ∈ H, ∑ κ ∈ D.fourTypes, ∑ c ∈ BY h,
        (Q * (fourKC κ' J * 2 * 12 ^ 4)) ^ p * (D.fourCc * K ^ (2 - (1 / 300 : ℝ) / 2)) *
          (c.1 ^ p * ((c.2.1 ^ J)⁻¹) ^ p * (1 + Real.log (8 * c.2.1 / c.1)) ^ 4) :=
        Finset.sum_le_sum fun h hh => Finset.sum_le_sum fun κ _ => Finset.sum_le_sum fun c hc =>
          hbin h hh κ c hc
    _ ≤ ∑ h ∈ H, ∑ _κ ∈ D.fourTypes, (K₁ * (fourKC κ' J * 2 * 12 ^ 4)) ^ p *
        (D.fourCc * K ^ (2 - (1 / 300 : ℝ) / 2)) *
          ((Real.logb 2 (U / ε) + 1) ^ 4 * bandC p J) := by
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
/-- Blueprint lines 2783-2817 at one point `y` for four cores: the powered retained principal
quantities of the cells of the path of `y` (over their groups, the heights and the role types) sum
to at most `|H| |types| (K₁ C_J 2 · 12⁴)^p C_c K^{2-c/2} (log₂(U/ε) + 1)⁴ C_band`. -/
theorem four_path_total {Cj CA CT CK : ℕ} {δs W : ℝ} (hV : D.S.Valid Cj CA CT CK δs W)
    (hCA : 1 ≤ CA) (hCT : 4 ≤ CT) (hd2 : 2 ≤ D.S.dmax) (hD : 2 ≤ D.S.Dstar)
    (hB : 2 ≤ D.S.Bstar) (hQ0 : 1 ≤ D.S.Q0) (hSP : D.SP = D.S.sideParams δs)
    (hdD : (D.S.dmax : ℝ) ≤ D.S.Dstar) (qG : bf.Grp → ℕ) (hqG : ∀ G, 1 ≤ qG G ∧ qG G ≤ D.S.Q0) (J :
        ℕ)
        (hJ : 1 ≤ J) (T : Finset (ℤ × ℤ))
    (gs : ℤ × ℤ → Finset bf.Grp) (z : bf.Grp → ChartTag)
    (hGc : ∀ I ∈ T, ∀ G ∈ gs I, (∀ j, 8 * (D.Ms j G).Λ ≤ D.S.Ξ) ∧
      (∀ j, (D.Ms j G).zc = z G) ∧ (z G).dim ≤ D.S.dmax)
    (H : Finset ℕ) (hH : ∀ h ∈ H, h ≤ D.SP.Jst)
    (rep : ℕ → ∀ G j, ℕ → ℕ → ℤ × (ℤ × ℤ) × (D.Ms j G).Md → (D.Ms j G).Md)
    (hrep : ∀ h ∈ H, ∀ I ∈ T, ∀ G ∈ gs I, ∀ j, (D.withQ0 (qG G)).RepOK G j h T (rep h G j))
    (anc : ∀ (I : ℤ × ℤ) (G : bf.Grp), D.AncNe G I → ℕ → ∀ j, Finset (D.Ms j G).Md →
      (D.Ms j G).alive (ancAt A.G (D.preAt I) (A.blkStart D.S.K I.1 - 4 * D.S.K)))
    (hanc : ∀ h (hh : h ∈ H), ∀ I (hI : I ∈ T), ∀ G (hG : G ∈ gs I), ∀ (hA : D.AncNe G I) j F
      (hF : F ∈ (D.withQ0 (qG G)).goodCls G I j h),
      anc I G hA h j F =
        (D.withQ0 (qG G)).repAnchor G I j h (rep h G j) (hrep h hh I hI G hG j).1 hF)
    {U ε : ℝ} (hε : 0 < ε) (hεU : ε ≤ U)
    (hU : ∀ I ∈ T, ∀ G ∈ gs I, ∀ h ∈ H, ∀ j, ∀ F ∈ (D.withQ0 (qG G)).goodCls G I j h, (D.withQ0
        (qG G)).clsSize G I j F ≤ U)
    {K K₁ : ℝ} (hK : 0 ≤ K) (hK₁ : 0 ≤ K₁) (y : ℝ)
    (hcap : ∀ h ∈ H, 10 ≤ h → ∀ c : ℝ × ℝ × (Fin 4 → ℝ), 0 < c.1 → c.1 ≤ 1 → 1 ≤ c.2.1 →
      (∀ i, 0 < c.2.2 i) →
      (∀ j, ε ≤ c.2.2 j ∧ c.2.2 j ≤ U ∧ ∃ k : ℤ, c.2.2 j = (2 : ℝ) ^ k) → ∀ κ i,
        ∑ G ∈ pathGroups (A := A) T gs y,
        (((D.withQ0 (qG G)).fourUsedReps G h y (pathCell A.G T y) (fun s => anc (pathCell A.G T y s)
            G) c κ
          (pathDepths (A := A) T gs y G) i).card : ℝ) ≤ K * c.2.2 i ^ (-2 : ℝ)) :
    ∑ I ∈ T with y ∈ dyadicGridCell A.G I.1 I.2, ∑ x ∈ gs I ×ˢ (H ×ˢ D.fourTypes),
      (K₁ * ((H.card : ℝ)⁻¹ * ∑ c ∈ (D.withQ0 (qG x.1)).fourRetBinsA x.1 I y (anc I x.1) x.2.1 ε,
        fourBinVal κ' J c * (D.withQ0 (qG x.1)).fourCntA x.1 I y (anc I x.1) x.2.1 c x.2.2)) ^
        (1 - (1 / 300 : ℝ) / 4) ≤
      H.card * D.fourTypes.card * ((K₁ * (fourKC κ' J * 2 * 12 ^ 4)) ^ (1 - (1 / 300 : ℝ) / 4) *
        (D.fourCc * K ^ (2 - (1 / 300 : ℝ) / 2)) *
        ((Real.logb 2 (U / ε) + 1) ^ 4 * bandC (1 - (1 / 300 : ℝ) / 4) J)) := by
  set p : ℝ := 1 - (1 / 300 : ℝ) / 4 with hp
  have hp0 : 0 < p := by rw [hp]; norm_num
  have hp1 : p ≤ 1 := by rw [hp]; norm_num
  have hΔ : D.SP.Δ = 10 := by rw [hSP]; rfl
  set Ty := T.filter fun I => y ∈ dyadicGridCell A.G I.1 I.2 with hTy
  set! Q := K₁ * (H.card : ℝ)⁻¹ with hQ
  have hQnn : 0 ≤ Q := mul_nonneg hK₁ (inv_nonneg.mpr (Nat.cast_nonneg _))
  set! f : ℕ → (Fin 4 → ℕ × ℕ) → ℤ × ℤ → bf.Grp → ℝ × ℝ × (Fin 4 → ℝ) → ℝ :=
    fun h κ I G c => (Q * fourBinVal κ' J c * (D.withQ0 (qG G)).fourCntA G I y (anc I G) h c κ) ^ p
        with hf
  set! BY : ℕ → Finset (ℝ × ℝ × (Fin 4 → ℝ)) := fun h =>
    Ty.biUnion fun I => (gs I).biUnion fun G => (D.withQ0 (qG G)).fourRetBinsA G I y (anc I G) h ε
        with hBY
  have hgen : ∀ h ∈ H, ∀ c ∈ BY h, ((∃ k : ℤ, c.1 = (2 : ℝ) ^ k) ∧ c.1 ≤ 1 ∧
      (∃ k : ℤ, c.2.1 = (2 : ℝ) ^ k) ∧ 1 ≤ c.2.1 ∧
      ∀ j, ε ≤ c.2.2 j ∧ c.2.2 j ≤ U ∧ ∃ k : ℤ, c.2.2 j = (2 : ℝ) ^ k) ∧
      0 < c.1 ∧ (∀ i, 0 < c.2.2 i) := by
    intro h hh c hc
    obtain ⟨I, hI, hc⟩ := Finset.mem_biUnion.mp hc
    obtain ⟨G, hG, hc⟩ := Finset.mem_biUnion.mp hc
    unfold fourRetBinsA at hc
    split_ifs at hc with hA
    · exact (D.withQ0 (qG G)).fourBin_genuine hD G I y (anc I G hA) h
        (hU I (Finset.mem_filter.mp hI).1 G hG h hh) hc
    · exact absurd hc (Finset.notMem_empty _)
  have hval0 : ∀ h ∈ H, ∀ c ∈ BY h, 0 ≤ fourBinVal κ' J c := by
    intro h hh c hc
    obtain ⟨⟨-, -, -, hν, -⟩, hμ, hσ⟩ := hgen h hh c hc
    rw [fourBinVal_eq]
    have := fourKC_nonneg κ' J
    have : 0 ≤ (c.2.1 ^ J)⁻¹ := inv_nonneg.mpr (pow_nonneg (by linarith) J)
    have : 0 ≤ ∏ j, c.2.2 j := Finset.prod_nonneg fun j _ => (hσ j).le
    have := hμ.le
    positivity
  have hf0 : ∀ h ∈ H, ∀ κ I G, ∀ c ∈ BY h, 0 ≤ f h κ I G c := fun h hh κ I G c hc =>
    Real.rpow_nonneg (mul_nonneg (mul_nonneg hQnn (hval0 h hh c hc))
      (D.withQ0 (qG G)).fourCntA_nonneg) p
  have hretBY : ∀ h, ∀ I ∈ Ty, ∀ G ∈ gs I, (D.withQ0 (qG G)).fourRetBinsA G I y (anc I G) h ε ⊆ BY h
      :=
    fun h I hI G hG c hc => Finset.mem_biUnion.mpr ⟨I, hI, Finset.mem_biUnion.mpr ⟨G, hG, hc⟩⟩
  -- (a) subadditivity of `x^p` over the bins of one configuration
  have hstep : ∀ I ∈ Ty, ∀ G ∈ gs I, ∀ h ∈ H, ∀ κ,
      (K₁ * ((H.card : ℝ)⁻¹ * ∑ c ∈ (D.withQ0 (qG G)).fourRetBinsA G I y (anc I G) h ε,
        fourBinVal κ' J c * (D.withQ0 (qG G)).fourCntA G I y (anc I G) h c κ)) ^ p ≤
      ∑ c ∈ (D.withQ0 (qG G)).fourRetBinsA G I y (anc I G) h ε, f h κ I G c := by
    intro I hI G hG h hh κ
    have e : K₁ * ((H.card : ℝ)⁻¹ * ∑ c ∈ (D.withQ0 (qG G)).fourRetBinsA G I y (anc I G) h ε,
        fourBinVal κ' J c * (D.withQ0 (qG G)).fourCntA G I y (anc I G) h c κ) =
        ∑ c ∈ (D.withQ0 (qG G)).fourRetBinsA G I y (anc I G) h ε,
          Q * fourBinVal κ' J c * (D.withQ0 (qG G)).fourCntA G I y (anc I G) h c κ := by
      rw [Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun c _ => by rw [hQ]; ring
    rw [e]
    exact rpow_finset_sum_le _ _ (fun c hc => mul_nonneg (mul_nonneg hQnn
      (hval0 h hh c (hretBY h I hI G hG hc))) (D.withQ0 (qG G)).fourCntA_nonneg) hp0 hp1
  -- (b) the configurations: groups, heights, types
  have hreorg : ∑ I ∈ Ty, ∑ x ∈ gs I ×ˢ (H ×ˢ D.fourTypes),
      ∑ c ∈ (D.withQ0 (qG x.1)).fourRetBinsA x.1 I y (anc I x.1) x.2.1 ε, f x.2.1 x.2.2 I x.1 c =
      ∑ h ∈ H, ∑ κ ∈ D.fourTypes, ∑ I ∈ Ty, ∑ G ∈ gs I,
        ∑ c ∈ (D.withQ0 (qG G)).fourRetBinsA G I y (anc I G) h ε, f h κ I G c := by
    simp only [Finset.sum_product]
    calc ∑ I ∈ Ty, ∑ G ∈ gs I, ∑ h ∈ H, ∑ κ ∈ D.fourTypes,
          ∑ c ∈ (D.withQ0 (qG G)).fourRetBinsA G I y (anc I G) h ε, f h κ I G c
        = ∑ I ∈ Ty, ∑ h ∈ H, ∑ G ∈ gs I, ∑ κ ∈ D.fourTypes,
          ∑ c ∈ (D.withQ0 (qG G)).fourRetBinsA G I y (anc I G) h ε, f h κ I G c :=
          Finset.sum_congr rfl fun I _ => Finset.sum_comm
      _ = ∑ I ∈ Ty, ∑ h ∈ H, ∑ κ ∈ D.fourTypes, ∑ G ∈ gs I,
          ∑ c ∈ (D.withQ0 (qG G)).fourRetBinsA G I y (anc I G) h ε, f h κ I G c :=
          Finset.sum_congr rfl fun I _ => Finset.sum_congr rfl fun h _ => Finset.sum_comm
      _ = ∑ h ∈ H, ∑ I ∈ Ty, ∑ κ ∈ D.fourTypes, ∑ G ∈ gs I,
          ∑ c ∈ (D.withQ0 (qG G)).fourRetBinsA G I y (anc I G) h ε, f h κ I G c := Finset.sum_comm
      _ = _ := Finset.sum_congr rfl fun h _ => Finset.sum_comm
  -- (c) extend to the bins along the path and reindex by the depths
  have hext : ∀ h ∈ H, ∀ κ, ∑ I ∈ Ty, ∑ G ∈ gs I,
      ∑ c ∈ (D.withQ0 (qG G)).fourRetBinsA G I y (anc I G) h ε, f h κ I G c ≤
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
  have hbin : ∀ h ∈ H, ∀ κ, ∀ c ∈ BY h, ∑ G ∈ pathGroups (A := A) T gs y,
      ∑ s ∈ pathDepths (A := A) T gs y G, f h κ (pathCell A.G T y s) G c ≤
      (Q * (fourKC κ' J * 2 * 12 ^ 4)) ^ p * (D.fourCc * K ^ (2 - (1 / 300 : ℝ) / 2)) *
        (c.1 ^ p * ((c.2.1 ^ J)⁻¹) ^ p * (1 + Real.log (8 * c.2.1 / c.1)) ^ 4) := by
    intro h hh κ c hc
    obtain ⟨⟨-, hμ1, -, hν1, hamp⟩, hμ, hσ⟩ := hgen h hh c hc
    have h10 : 10 ≤ h := by
      by_contra hlt
      push Not at hlt
      obtain ⟨I, -, hc'⟩ := Finset.mem_biUnion.mp hc
      obtain ⟨G, -, hc'⟩ := Finset.mem_biUnion.mp hc'
      unfold fourRetBinsA at hc'
      split_ifs at hc' with hA
      swap
      · exact Finset.notMem_empty c hc'
      unfold fourRetBins at hc'
      rw [(D.withQ0 (qG G)).fourTested_eq_empty G I y (anc I G hA)
        (by rw [SideInput.withQ0_SP, hΔ]; exact hlt)] at hc'
      obtain ⟨p', hp', -⟩ := Finset.mem_image.mp (Finset.mem_filter.mp hc').1
      exact Finset.notMem_empty p' hp'
    have hb := D.four_path_bin_bound hV hCA hCT hd2 hD hB hQ0 hSP hdD qG hqG J T gs z hGc h h10
      (hH h hh) (rep h) (hrep h hh) (fun I G => anc I G)
      (fun I hI G hG hA j F hF => hanc h hh I hI G hG hA j F hF) y c ⟨hμ, hμ1, hν1⟩ hσ κ hK hQnn
      (fun i => hcap h hh h10 c hμ hμ1 hν1 hσ hamp κ i)
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun G _ => Finset.sum_congr rfl fun s _ =>
      rfl)) (hb.trans (le_of_eq ?_))
    have hν0 : 0 ≤ (c.2.1 ^ J)⁻¹ := inv_nonneg.mpr (pow_nonneg (by linarith) J)
    have hC4 : 0 ≤ fourKC κ' J * 2 * 12 ^ 4 := by have := fourKC_nonneg κ' J; positivity
    rw [show Q * (fourKC κ' J * 2 * 12 ^ 4 * (c.1 * (c.2.1 ^ J)⁻¹)) =
      (Q * (fourKC κ' J * 2 * 12 ^ 4)) * (c.1 * (c.2.1 ^ J)⁻¹) by ring,
      Real.mul_rpow (mul_nonneg hQnn hC4) (mul_nonneg hμ.le hν0), Real.mul_rpow hμ.le hν0]
    unfold fourCc
    ring
  expose_names
  exact @four_path_total_stage_1 κ' c₀ A bf fp D Cj CA CT CK δs W hV hd2 hD hB hQ0 qG J hJ T gs H
    anc U ε hε hεU K K₁ hK hK₁ y hp0 hQ hQnn hgen hstep hreorg hext hbin

end SideInput

end ActiveSetup.BasicFamilies.FamParams

namespace ActiveSetup.BasicFamilies.FamParams
variable {κ' : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ' c₀} {bf : A.BasicFamilies}
  {fp : bf.FamParams}

namespace SideInput
variable (D : fp.SideInput)

open Classical in
/-- Occupied four-core bins have nonnegative values. -/
theorem fourBinVal_nonneg_of_mem (hD : 2 ≤ D.S.Dstar) (J : ℕ) (G : bf.Grp) (I : ℤ × ℤ)
    (xs : ℝ) (anc : ℕ → ∀ j, Finset (D.Ms j G).Md →
      (D.Ms j G).alive (ancAt A.G (D.preAt I) (A.blkStart D.S.K I.1 - 4 * D.S.K))) (h : ℕ)
    {c : ℝ × ℝ × (Fin 4 → ℝ)}
    (hc : c ∈ (D.fourTested G I xs anc h).image (D.fourBinOf G I xs anc h)) :
    0 ≤ fourBinVal κ' J c := by
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hc
  unfold fourTested fourTestedOf at hp
  obtain ⟨-, hpass, -⟩ := Finset.mem_filter.mp hp
  obtain ⟨-, -, hμ3, -, -, -, hν3, -⟩ := D.fourBands_spec (by linarith) (D.one_le_U0 hD) hpass
  have hU0i : 0 < D.U0⁻¹ := inv_pos.mpr (by linarith [D.one_le_U0 hD])
  have hμ : 0 < (D.fourBinOf G I xs anc h p).1 := lt_trans (half_pos hU0i) hμ3
  have hν : 1 ≤ (D.fourBinOf G I xs anc h p).2.1 := hν3
  rw [fourBinVal_eq]
  have := fourKC_nonneg κ' J
  have : 0 ≤ ((D.fourBinOf G I xs anc h p).2.1 ^ J)⁻¹ :=
    inv_nonneg.mpr (pow_nonneg (by linarith) J)
  have : 0 ≤ ∏ j, (D.fourBinOf G I xs anc h p).2.2 j :=
    Finset.prod_nonneg fun j _ => (dyadicBand_pos _).le
  have := hμ.le
  positivity

/-- Retained four-core bins with anchors depending on `AncNe G I` have nonnegative values. -/
theorem fourBinVal_nonneg_of_memA (hD : 2 ≤ D.S.Dstar) (J : ℕ) {G : bf.Grp} {I : ℤ × ℤ}
    {xs : ℝ} {anc : D.AncNe G I → ℕ → ∀ j, Finset (D.Ms j G).Md →
      (D.Ms j G).alive (ancAt A.G (D.preAt I) (A.blkStart D.S.K I.1 - 4 * D.S.K))} {h : ℕ}
    {ε : ℝ} {c : ℝ × ℝ × (Fin 4 → ℝ)} (hc : c ∈ D.fourRetBinsA G I xs anc h ε) :
    0 ≤ fourBinVal κ' J c := by
  unfold fourRetBinsA at hc
  split_ifs at hc with hA
  · exact D.fourBinVal_nonneg_of_mem hD J G I xs (anc hA) h (Finset.mem_filter.mp hc).1
  · exact absurd hc (Finset.notMem_empty _)

open Classical in
/-- Blueprint `eq:core-final` (lines 2808-2817) for the four-core patterns on the side states:
let `T` be the retained cells under the root `R` with their groups `g(I)`, the anchors the
hereditary representatives, and assume the principal bounds of `eq:principal-core`
(`‖Λ_{I,G}‖ ≤ K₁ ×` the height-averaged bin sum `+ err_{I,G}`), the retained amplitudes `σ ≤ U`,
at most `D_*` alive modes, and the path caps of `eq:top-count` along every retained path.
Removing the negligible amplitudes (`< ε`), `eq:min-power` with subadditivity of `x^p`, the path
estimates (`four_path_total`) and `eq:path` give, with `p = 1 - 1/1200`,
`Σ_I |I| min(η, C_I) ≤ η^{1/1200} |R| M_p + Σ_I |I| Σ_G (err_{I,G} + K₁ · 2 C_J 12⁴ ε U³ D_*^4)`,
where `M_p = |H| |types| (K₁ C_J 2 · 12⁴)^p C_c K^{2-c/2} (log₂(U/ε) + 1)⁴ C_band` is polynomial
in the parameters (`P^{C₄}`). -/
theorem four_core_final_side {Cj CA CT CK : ℕ} {δs W : ℝ} (hV : D.S.Valid Cj CA CT CK δs W)
    (hCA : 1 ≤ CA) (hCT : 4 ≤ CT) (hd2 : 2 ≤ D.S.dmax) (hD : 2 ≤ D.S.Dstar)
    (hB : 2 ≤ D.S.Bstar) (hQ0 : 1 ≤ D.S.Q0) (hSP : D.SP = D.S.sideParams δs)
    (hdD : (D.S.dmax : ℝ) ≤ D.S.Dstar) (qG : bf.Grp → ℕ) (hqG : ∀ G, 1 ≤ qG G ∧ qG G ≤ D.S.Q0) (J :
        ℕ)
        (hJ : 1 ≤ J) (R : ℤ × ℤ) (T : Finset (ℤ × ℤ))
    (hT : ∀ I ∈ T, dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G R.1 R.2)
    (gs : ℤ × ℤ → Finset bf.Grp) (z : bf.Grp → ChartTag)
    (hGc : ∀ I ∈ T, ∀ G ∈ gs I, (∀ j, 8 * (D.Ms j G).Λ ≤ D.S.Ξ) ∧
      (∀ j, (D.Ms j G).zc = z G) ∧ (z G).dim ≤ D.S.dmax)
    (H : Finset ℕ) (hH : ∀ h ∈ H, h ≤ D.SP.Jst)
    (rep : ℕ → ∀ G j, ℕ → ℕ → ℤ × (ℤ × ℤ) × (D.Ms j G).Md → (D.Ms j G).Md)
    (hrep : ∀ h ∈ H, ∀ I ∈ T, ∀ G ∈ gs I, ∀ j, (D.withQ0 (qG G)).RepOK G j h T (rep h G j))
    (anc : ∀ (I : ℤ × ℤ) (G : bf.Grp), D.AncNe G I → ℕ → ∀ j, Finset (D.Ms j G).Md →
      (D.Ms j G).alive (ancAt A.G (D.preAt I) (A.blkStart D.S.K I.1 - 4 * D.S.K)))
    (hanc : ∀ h (hh : h ∈ H), ∀ I (hI : I ∈ T), ∀ G (hG : G ∈ gs I), ∀ (hA : D.AncNe G I) j F
      (hF : F ∈ (D.withQ0 (qG G)).goodCls G I j h),
      anc I G hA h j F =
        (D.withQ0 (qG G)).repAnchor G I j h (rep h G j) (hrep h hh I hI G hG j).1 hF)
    (hcard : ∀ I ∈ T, ∀ G ∈ gs I, ∀ j, (((D.Ms j G).alive (ancAt A.G (D.preAt I)
      (A.blkStart D.S.K I.1 - 4 * D.S.K))).card : ℝ) ≤ D.S.Dstar)
    {U ε : ℝ} (hε : 0 < ε) (hεU : ε ≤ U)
    (hU : ∀ I ∈ T, ∀ G ∈ gs I, ∀ h ∈ H, ∀ j, ∀ F ∈ (D.withQ0 (qG G)).goodCls G I j h, (D.withQ0
        (qG G)).clsSize G I j F ≤ U)
    {K K₁ : ℝ} (hK : 0 ≤ K) (hK₁ : 0 ≤ K₁)
    (hcap : ∀ y, ∀ h ∈ H, 10 ≤ h → ∀ c : ℝ × ℝ × (Fin 4 → ℝ), 0 < c.1 → c.1 ≤ 1 →
      1 ≤ c.2.1 → (∀ i, 0 < c.2.2 i) →
      (∀ j, ε ≤ c.2.2 j ∧ c.2.2 j ≤ U ∧ ∃ k : ℤ, c.2.2 j = (2 : ℝ) ^ k) →
      ∀ κ i, ∑ G ∈ pathGroups (A := A) T gs y,
        (((D.withQ0 (qG G)).fourUsedReps G h y (pathCell A.G T y) (fun s => anc (pathCell A.G T y s)
            G) c κ
          (pathDepths (A := A) T gs y G) i).card : ℝ) ≤ K * c.2.2 i ^ (-2 : ℝ))
    (Λ4 Err : ℤ × ℤ → bf.Grp → ℝ) (hErr : ∀ I G, 0 ≤ Err I G)
    (hP : ∀ I ∈ T, ∀ G ∈ gs I, ∀ y ∈ dyadicGridCell A.G I.1 I.2, Λ4 I G ≤
      K₁ * ∑ h ∈ H, (H.card : ℝ)⁻¹ * (D.withQ0 (qG G)).fourBinSumA J G I y (anc I G) h + Err I G)
    (CI : ℤ × ℤ → ℝ) (hCI : ∀ I ∈ T, CI I ≤ ∑ G ∈ gs I, Λ4 I G) {η : ℝ} (hη : 0 ≤ η) :
    ∑ I ∈ T, dyadicGridLength A.G I.1 * min η (CI I) ≤
      η ^ (1 - (1 - (1 / 300 : ℝ) / 4)) * (dyadicGridLength A.G R.1 *
        (H.card * D.fourTypes.card * ((K₁ * (fourKC κ' J * 2 * 12 ^ 4)) ^
          (1 - (1 / 300 : ℝ) / 4) * (D.fourCc * K ^ (2 - (1 / 300 : ℝ) / 2)) *
          ((Real.logb 2 (U / ε) + 1) ^ 4 * bandC (1 - (1 / 300 : ℝ) / 4) J)))) +
        ∑ I ∈ T, dyadicGridLength A.G I.1 * ∑ G ∈ gs I,
          (Err I G + K₁ * (2 * fourKC κ' J * 12 ^ 4 * ε * U ^ 3 * D.S.Dstar ^ 4)) := by
  have hNeg0 : 0 ≤ 2 * fourKC κ' J * 12 ^ 4 * ε * U ^ 3 * D.S.Dstar ^ 4 := by
    have := fourKC_nonneg κ' J
    have : 0 ≤ U := hε.le.trans hεU
    have : (0 : ℝ) ≤ D.S.Dstar := by linarith
    positivity
  refine core_final_pointwise A.G R T hT (fun I => gs I ×ˢ (H ×ˢ D.fourTypes))
    (fun I x y => K₁ * ((H.card : ℝ)⁻¹ * ∑ c ∈ (D.withQ0 (qG x.1)).fourRetBinsA x.1 I y (anc I x.1)
        x.2.1 ε,
      fourBinVal κ' J c * (D.withQ0 (qG x.1)).fourCntA x.1 I y (anc I x.1) x.2.1 c x.2.2))
    (fun I x y => mul_nonneg hK₁ (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
      (Finset.sum_nonneg fun c hc => mul_nonneg
        ((D.withQ0 (qG x.1)).fourBinVal_nonneg_of_memA hD J hc)
        (D.withQ0 (qG x.1)).fourCntA_nonneg)))
    CI (fun I => ∑ G ∈ gs I, (Err I G + K₁ * (2 * fourKC κ' J * 12 ^ 4 * ε * U ^ 3 *
      D.S.Dstar ^ 4)))
    (fun I _ => Finset.sum_nonneg fun G _ => add_nonneg (hErr I G) (mul_nonneg hK₁ hNeg0))
    (fun I hI y hy => ?_) hη (by norm_num) (by norm_num) (fun y => ?_)
  · -- the cell decomposition
    refine (hCI I hI).trans ?_
    calc ∑ G ∈ gs I, Λ4 I G ≤ ∑ G ∈ gs I, (K₁ * (∑ h ∈ H, ∑ κ ∈ D.fourTypes,
          (H.card : ℝ)⁻¹ * ∑ c ∈ (D.withQ0 (qG G)).fourRetBinsA G I y (anc I G) h ε,
            fourBinVal κ' J c * (D.withQ0 (qG G)).fourCntA G I y (anc I G) h c κ +
          2 * fourKC κ' J * 12 ^ 4 * ε * U ^ 3 * D.S.Dstar ^ 4) + Err I G) := by
          refine Finset.sum_le_sum fun G hG => (hP I hI G hG y hy).trans ?_
          refine add_le_add (mul_le_mul_of_nonneg_left ?_ hK₁) le_rfl
          exact (D.withQ0 (qG G)).four_principal_splitA hD J G I y (anc I G) H (hcard I hI G hG)
            (hε.le.trans hεU) hε.le (hU I hI G hG)
      _ = ∑ x ∈ gs I ×ˢ (H ×ˢ D.fourTypes), K₁ * ((H.card : ℝ)⁻¹ *
          ∑ c ∈ (D.withQ0 (qG x.1)).fourRetBinsA x.1 I y (anc I x.1) x.2.1 ε,
            fourBinVal κ' J c * (D.withQ0 (qG x.1)).fourCntA x.1 I y (anc I x.1) x.2.1 c x.2.2) +
          ∑ G ∈ gs I, (Err I G + K₁ * (2 * fourKC κ' J * 12 ^ 4 * ε * U ^ 3 *
            D.S.Dstar ^ 4)) := by
          simp only [Finset.sum_product, mul_add, Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun G _ => by ring
  · exact D.four_path_total hV hCA hCT hd2 hD hB hQ0 hSP hdD qG hqG J hJ T gs z hGc H hH rep hrep
      anc
      hanc hε hεU hU hK hK₁ y (hcap y)

end SideInput

end ActiveSetup.BasicFamilies.FamParams

open Classical in
/-- The sum over occupied three-core bins `c = (μ, ν, i, b, σ)` (shells `i ≤ I_w`, dyadic bands
`μ ≤ 1 ≤ ν`, dyadic amplitudes `threeAmp` in `[ε, U]` for a fixed side role `l`): the powered
kernel factors with the logarithmic coefficient sum to at most `(I_w + 1) (log₂(U/ε) + 1)⁴`
times the convergent band series. -/
theorem three_bins_sum_le {p : ℝ} (hp : 0 < p) (J : ℕ) (hJ : 1 ≤ J) (l : Fin 4) (Iw : ℕ)
    {ε U : ℝ} (hε : 0 < ε) (hεU : ε ≤ U) (B : Finset (ℝ × ℝ × ℕ × ℝ × (Fin 4 → ℝ)))
    (hB : ∀ c ∈ B, (∃ k : ℤ, c.1 = (2 : ℝ) ^ k) ∧ c.1 ≤ 1 ∧ (∃ k : ℤ, c.2.1 = (2 : ℝ) ^ k) ∧
      1 ≤ c.2.1 ∧ c.2.2.1 ≤ Iw ∧ c.2.2.2.2 l = 1 ∧ ∀ j, ε ≤ (fun j => if j = l then c.2.2.2.1 else
          c.2.2.2.2 j) j ∧
        (fun j => if j = l then c.2.2.2.1 else c.2.2.2.2 j) j ≤ U ∧
        ∃ k : ℤ, (fun j => if j = l then c.2.2.2.1 else c.2.2.2.2 j) j = (2 : ℝ) ^ k) :
    ∑ c ∈ B, c.1 ^ p * ((c.2.1 ^ J)⁻¹) ^ p * (1 + Real.log (8 * c.2.1 / c.1)) ^ 4 ≤
      (Iw + 1) * ((Real.logb 2 (U / ε) + 1) ^ 4 * ∑' t : ℕ × ℕ, ((2 : ℝ) ^ (-p)) ^ t.1 *
        ((2 : ℝ) ^ (-((J : ℝ) * p))) ^ t.2 * (4 ^ 4 * (1 + t.1 + t.2 : ℝ) ^ 4)) := by
  have hJ0 : (0 : ℝ) < J := by exact_mod_cast hJ
  set Cb := ∑' t : ℕ × ℕ, ((2 : ℝ) ^ (-p)) ^ t.1 * ((2 : ℝ) ^ (-((J : ℝ) * p))) ^ t.2 *
    (4 ^ 4 * (1 + t.1 + t.2 : ℝ) ^ 4) with hCb
  have hCb0 : 0 ≤ Cb := tsum_nonneg fun t => by positivity
  set amp : ℝ × ℝ × ℕ × ℝ × (Fin 4 → ℝ) → (Fin 4 → ℝ) := fun c j =>
    if j = l then c.2.2.2.1 else c.2.2.2.2 j with hamp
  set f : ℝ × ℝ × ℕ × ℝ × (Fin 4 → ℝ) → ℝ := fun c =>
    c.1 ^ p * ((c.2.1 ^ J)⁻¹) ^ p * (1 + Real.log (8 * c.2.1 / c.1)) ^ 4 with hf
  -- group by the amplitude tuple and the shell
  set key : ℝ × ℝ × ℕ × ℝ × (Fin 4 → ℝ) → (Fin 4 → ℝ) × ℕ := fun c => (amp c, c.2.2.1) with hkey
  rw [← Finset.sum_fiberwise_of_maps_to (g := key) (t := B.image key)
    (fun c hc => Finset.mem_image_of_mem _ hc)]
  have hfiber : ∀ k ∈ B.image key, ∑ c ∈ B.filter (fun c => key c = k), f c ≤ Cb := by
    intro k _
    have hinj : Set.InjOn (fun c : ℝ × ℝ × ℕ × ℝ × (Fin 4 → ℝ) => (c.1, c.2.1))
        (B.filter fun c => key c = k : Set _) := by
      intro c hc d hd hcd
      simp only [Prod.mk.injEq] at hcd
      have h1 := (Finset.mem_filter.mp (Finset.mem_coe.mp hc)).2
      have h2 := (Finset.mem_filter.mp (Finset.mem_coe.mp hd)).2
      have hk := h1.trans h2.symm
      simp only [hkey, Prod.mk.injEq] at hk
      have hb : c.2.2.2.1 = d.2.2.2.1 := by
        have := congrFun hk.1 l
        simpa only [hamp, ↓reduceIte] using this
      have hσ : c.2.2.2.2 = d.2.2.2.2 := by
        funext j
        by_cases hjl : j = l
        · subst hjl
          rw [(hB c (Finset.mem_filter.mp (Finset.mem_coe.mp hc)).1).2.2.2.2.2.1,
            (hB d (Finset.mem_filter.mp (Finset.mem_coe.mp hd)).1).2.2.2.2.2.1]
        · have := congrFun hk.1 j
          simpa only [hamp, hjl, ↓reduceIte] using this
      exact Prod.ext hcd.1 (Prod.ext hcd.2 (Prod.ext hk.2 (Prod.ext hb hσ)))
    have hT := dyadic_band_sum_le hp hJ0 ((B.filter fun c => key c = k).image
      fun c => (c.1, c.2.1)) (fun x hx => by
        obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hx
        obtain ⟨h1, h2, h3, h4, -⟩ := hB c (Finset.mem_filter.mp hc).1
        obtain ⟨u, hu⟩ := exists_nat_of_zpow_le_one h1 h2
        obtain ⟨v, hv⟩ := exists_nat_of_one_le_zpow h3 h4
        exact ⟨u, v, hu, hv⟩)
    rw [Finset.sum_image hinj] at hT
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun c _ => ?_)) hT
    simp only [hf]
    rw [← Real.rpow_natCast]
  have hsub : B.image key ⊆ (B.image amp) ×ˢ Finset.range (Iw + 1) := by
    intro k hk
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hk
    exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hc,
      Finset.mem_range.mpr (Nat.lt_succ_of_le (hB c hc).2.2.2.2.1)⟩
  have hamps : ((B.image amp).card : ℝ) ≤ (Real.logb 2 (U / ε) + 1) ^ 4 :=
    dyadic_quadruples_card hε hεU _ fun a ha j => by
      obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp ha
      exact (hB c hc).2.2.2.2.2.2 j
  have hkeys : ((B.image key).card : ℝ) ≤ (Iw + 1) * (Real.logb 2 (U / ε) + 1) ^ 4 := by
    have h1 := Finset.card_le_card hsub
    rw [Finset.card_product, Finset.card_range] at h1
    have h2 : ((B.image key).card : ℝ) ≤ ((B.image amp).card : ℝ) * (Iw + 1) := by
      exact_mod_cast h1
    nlinarith only [Nat.cast_nonneg (α := ℝ) (B.image amp).card, hamps, h2]
  calc ∑ k ∈ B.image key, ∑ c ∈ B.filter (fun c => key c = k), f c
      ≤ ∑ _k ∈ B.image key, Cb := Finset.sum_le_sum hfiber
    _ = ((B.image key).card : ℝ) * Cb := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (Iw + 1) * (Real.logb 2 (U / ε) + 1) ^ 4 * Cb := mul_le_mul_of_nonneg_right hkeys hCb0
    _ = _ := by ring

namespace ActiveSetup.BasicFamilies.FamParams
variable {κ' : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ' c₀} {bf : A.BasicFamilies}
  {fp : bf.FamParams}

namespace SideInput
variable (D : fp.SideInput)

/-- The three-core bin value factors as `8 C_{J,A} 2^{A+4} 12³ · μ ν^{-J} Λ^{-(A+1)} · Π
threeAmp`. -/
theorem threeBinVal_eq (J Aw : ℕ) (l : Fin 4) (c : ℝ × ℝ × ℕ × ℝ × (Fin 4 → ℝ)) :
    threeBinVal κ' J Aw l c = 8 * entryCU κ' J Aw * 2 ^ (Aw + 4) * 12 ^ 3 *
      (c.1 * (c.2.1 ^ J)⁻¹ * ((2 : ℝ) ^ c.2.2.1)⁻¹ ^ (Aw + 1)) * ∏ j, threeAmp l c j := by
  have hprodE : ∏ j, threeAmp l c j = c.2.2.2.1 * ∏ j ∈ Finset.univ.erase l, c.2.2.2.2 j := by
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ l)]
    unfold threeAmp
    simp only [↓reduceIte]
    congr 1
    exact Finset.prod_congr rfl fun j hj =>
      ite_eq_right_iff.mpr fun h' => absurd h' (Finset.ne_of_mem_erase hj)
  unfold threeBinVal
  rw [hprodE, Finset.prod_congr rfl fun j _ => (show 6 * (2 * c.2.2.2.2 j) =
    12 * c.2.2.2.2 j by ring), Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_erase_of_mem (Finset.mem_univ l), Finset.card_univ, Fintype.card_fin]
  ring

/-- The class size of the empty class is `0`, so its band is `1`. -/
theorem dyadicBand_clsSize_empty (G : bf.Grp) (I : ℤ × ℤ) (j : Fin 4) :
    dyadicBand (D.clsSize G I j ∅) = 1 := by
  have : D.clsSize G I j ∅ = 0 := by
    unfold clsSize clsUnits
    simp
  rw [this]
  unfold dyadicBand
  simp

open Classical in
/-- Below the height `Δ` there are no tested three-core tuples. -/
theorem threeTested_eq_empty (G : bf.Grp) (I : ℤ × ℤ) (xs : ℝ) (l : Fin 4)
    (anc : ℕ → ∀ j, j ≠ l → Finset (D.Ms j G).Md →
      (D.Ms j G).alive (ancAt A.G (D.preAt I) (A.blkStart D.S.K I.1 - 4 * D.S.K)))
    (X : ColumnL2 (bf.Lab ⊕ Fin fp.Mc)) (Iw : ℕ) {h : ℕ} (hh : h < D.SP.Δ) :
    D.threeTested G I xs l anc X Iw h = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun q hq => ?_
  unfold threeTested threeTestedOf at hq
  obtain ⟨j, hj⟩ := exists_ne l
  have hF := Fintype.mem_piFinset.mp (Finset.mem_product.mp (Finset.mem_filter.mp hq).1).1 j
  simp only [hj, ↓reduceIte] at hF
  obtain ⟨m, hm, -⟩ := D.mem_goodCls hF
  exact absurd hm.1 (by omega)

/-- The core role types with the side role normalized to `(0, 0)`. -/
noncomputable def threeTypes (l : Fin 4) : Finset (Fin 4 → ℕ × ℕ) :=
  D.fourTypes.filter fun κ => κ l = (0, 0)

open Classical in
/-- The tested three-core tuples and shells of a bin split by their core role types. -/
theorem card_bin_eq_sum_types3 (G : bf.Grp) (I : ℤ × ℤ) (xs : ℝ) (l : Fin 4)
    (anc : ℕ → ∀ j, j ≠ l → Finset (D.Ms j G).Md →
      (D.Ms j G).alive (ancAt A.G (D.preAt I) (A.blkStart D.S.K I.1 - 4 * D.S.K)))
    (X : ColumnL2 (bf.Lab ⊕ Fin fp.Mc)) (Iw h : ℕ)
    (hcard : ∀ j, (((D.Ms j G).alive (ancAt A.G (D.preAt I)
      (A.blkStart D.S.K I.1 - 4 * D.S.K))).card : ℝ) ≤ D.S.Dstar)
    (c : ℝ × ℝ × ℕ × ℝ × (Fin 4 → ℝ)) :
    (((D.threeTested G I xs l anc X Iw h).filter fun q =>
        D.threeBinOf G I xs l anc X h q = c).card : ℝ) =
      ∑ κ ∈ D.threeTypes l, (((D.threeTested G I xs l anc X Iw h).filter fun q =>
        D.threeBinOf G I xs l anc X h q = c ∧
          ∀ j, j ≠ l → D.classTypeOf G I j h (q.1 j) = κ j).card : ℝ) := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun q j =>
      if j = l then ((0, 0) : ℕ × ℕ) else D.classTypeOf G I j h (q.1 j))
    (t := D.threeTypes l) (fun q _ => by
      unfold threeTypes fourTypes
      refine Finset.mem_filter.mpr ⟨Fintype.mem_piFinset.mpr fun j => ?_, by simp⟩
      beta_reduce
      split_ifs
      · exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (Nat.succ_pos _),
          Finset.mem_range.mpr (Nat.succ_pos _)⟩
      · exact D.classTypeOf_mem G I j h _ (hcard j))]
  push_cast
  refine Finset.sum_congr rfl fun κ hκ => ?_
  have hκl : κ l = (0, 0) := (Finset.mem_filter.mp hκ).2
  rw [Finset.filter_filter]
  congr 2
  ext q
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hq, h1, h2⟩
    refine ⟨hq, h1, fun j hj => ?_⟩
    have := congrFun h2 j
    simpa only [hj, ↓reduceIte] using this
  · rintro ⟨hq, h1, h2⟩
    refine ⟨hq, h1, funext fun j => ?_⟩
    by_cases hj : j = l
    · subst hj; simp only [↓reduceIte, hκl]
    · simp only [hj, ↓reduceIte]; exact h2 j hj

end SideInput

end ActiveSetup.BasicFamilies.FamParams

namespace ActiveSetup.BasicFamilies.FamParams
variable {κ' : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ' c₀} {bf : A.BasicFamilies}
  {fp : bf.FamParams}

namespace SideInput
variable (D : fp.SideInput)

open Classical in
/-- The retained occupied three-core bins (all amplitudes of `threeAmp` at least `ε`). -/
noncomputable def threeRetBins (G : bf.Grp) (I : ℤ × ℤ) (xs : ℝ) (l : Fin 4)
    (anc : ℕ → ∀ j, j ≠ l → Finset (D.Ms j G).Md →
      (D.Ms j G).alive (ancAt A.G (D.preAt I) (A.blkStart D.S.K I.1 - 4 * D.S.K)))
    (Iw h : ℕ) (ε : ℝ) : Finset (ℝ × ℝ × ℕ × ℝ × (Fin 4 → ℝ)) :=
  ((D.threeTested G I xs l anc (D.toLeaf.sv l G I) Iw h).image
    (D.threeBinOf G I xs l anc (D.toLeaf.sv l G I) h)).filter fun c => ∀ j, ε ≤ threeAmp l c j

open Classical in
/-- The number of tested three-core tuples and shells in the bin `c` with the core types `κ`. -/
noncomputable def threeCnt (G : bf.Grp) (I : ℤ × ℤ) (xs : ℝ) (l : Fin 4)
    (anc : ℕ → ∀ j, j ≠ l → Finset (D.Ms j G).Md →
      (D.Ms j G).alive (ancAt A.G (D.preAt I) (A.blkStart D.S.K I.1 - 4 * D.S.K)))
    (Iw h : ℕ) (c : ℝ × ℝ × ℕ × ℝ × (Fin 4 → ℝ)) (κ : Fin 4 → ℕ × ℕ) : ℝ :=
  (((D.threeTested G I xs l anc (D.toLeaf.sv l G I) Iw h).filter fun q =>
    D.threeBinOf G I xs l anc (D.toLeaf.sv l G I) h q = c ∧
      ∀ j, j ≠ l → D.classTypeOf G I j h (q.1 j) = κ j).card : ℝ)

open Classical in
/-- The retained occupied three-core bins at a cell and group, with anchors depending on a proof of
`AncNe3 G I l` (the alive sets of the core roles at the decision cell are nonempty); empty
otherwise. -/
noncomputable def threeRetBinsA (G : bf.Grp) (I : ℤ × ℤ) (xs : ℝ) (l : Fin 4)
    (anc : D.AncNe3 G I l → ℕ → ∀ j, j ≠ l → Finset (D.Ms j G).Md →
      (D.Ms j G).alive (ancAt A.G (D.preAt I) (A.blkStart D.S.K I.1 - 4 * D.S.K)))
    (Iw h : ℕ) (ε : ℝ) : Finset (ℝ × ℝ × ℕ × ℝ × (Fin 4 → ℝ)) :=
  if hA : D.AncNe3 G I l then D.threeRetBins G I xs l (anc hA) Iw h ε else ∅

open Classical in
/-- The number of tested three-core tuples and shells in the bin `c` with the core types `κ`, with
anchors depending on a proof of `AncNe3 G I l`; zero otherwise. -/
noncomputable def threeCntA (G : bf.Grp) (I : ℤ × ℤ) (xs : ℝ) (l : Fin 4)
    (anc : D.AncNe3 G I l → ℕ → ∀ j, j ≠ l → Finset (D.Ms j G).Md →
      (D.Ms j G).alive (ancAt A.G (D.preAt I) (A.blkStart D.S.K I.1 - 4 * D.S.K)))
    (Iw h : ℕ) (c : ℝ × ℝ × ℕ × ℝ × (Fin 4 → ℝ)) (κ : Fin 4 → ℕ × ℕ) : ℝ :=
  if hA : D.AncNe3 G I l then D.threeCnt G I xs l (anc hA) Iw h c κ else 0

theorem threeCntA_nonneg {G : bf.Grp} {I : ℤ × ℤ} {xs : ℝ} {l : Fin 4}
    {anc : D.AncNe3 G I l → ℕ → ∀ j, j ≠ l → Finset (D.Ms j G).Md →
      (D.Ms j G).alive (ancAt A.G (D.preAt I) (A.blkStart D.S.K I.1 - 4 * D.S.K))}
    {Iw h : ℕ} {c : ℝ × ℝ × ℕ × ℝ × (Fin 4 → ℝ)} {κ : Fin 4 → ℕ × ℕ} :
    0 ≤ D.threeCntA G I xs l anc Iw h c κ := by
  unfold threeCntA threeCnt
  split_ifs
  · exact Nat.cast_nonneg _
  · exact le_rfl

open Classical in
/-- The three-core bin sum `Σ_c v(c) N_c` of the tested tuples and shells at a cell, group and
height (side role `l`, the principal quantity of `eq:principal-core`), with anchors depending on a
proof of `AncNe3 G I l`; zero otherwise. -/
noncomputable def threeBinSumA (J Aw Iw : ℕ) (G : bf.Grp) (I : ℤ × ℤ) (xs : ℝ) (l : Fin 4)
    (anc : D.AncNe3 G I l → ℕ → ∀ j, j ≠ l → Finset (D.Ms j G).Md →
      (D.Ms j G).alive (ancAt A.G (D.preAt I) (A.blkStart D.S.K I.1 - 4 * D.S.K)))
    (h : ℕ) : ℝ :=
  if hA : D.AncNe3 G I l then
    ∑ c ∈ (D.threeTested G I xs l (anc hA) (D.toLeaf.sv l G I) Iw h).image
        (D.threeBinOf G I xs l (anc hA) (D.toLeaf.sv l G I) h), threeBinVal κ' J Aw l c *
      (((D.threeTested G I xs l (anc hA) (D.toLeaf.sv l G I) Iw h).filter fun q =>
        D.threeBinOf G I xs l (anc hA) (D.toLeaf.sv l G I) h q = c).card : ℝ)
  else 0

open Classical in
/-- Occupied three-core bins are genuine and have nonnegative values. -/
theorem threeBin_basic (hD : 2 ≤ D.S.Dstar) (G : bf.Grp) (I : ℤ × ℤ) (xs : ℝ) (l : Fin 4)
    (anc : ℕ → ∀ j, j ≠ l → Finset (D.Ms j G).Md →
      (D.Ms j G).alive (ancAt A.G (D.preAt I) (A.blkStart D.S.K I.1 - 4 * D.S.K)))
    (Iw h : ℕ) {c : ℝ × ℝ × ℕ × ℝ × (Fin 4 → ℝ)}
    (hc : c ∈ (D.threeTested G I xs l anc (D.toLeaf.sv l G I) Iw h).image
      (D.threeBinOf G I xs l anc (D.toLeaf.sv l G I) h)) :
    (∃ k : ℤ, c.1 = (2 : ℝ) ^ k) ∧ c.1 ≤ 1 ∧ (∃ k : ℤ, c.2.1 = (2 : ℝ) ^ k) ∧ 1 ≤ c.2.1 ∧
      c.2.2.1 ≤ Iw ∧ c.2.2.2.2 l = 1 ∧ 0 < c.1 ∧ (∀ i, 0 < threeAmp l c i) ∧
      (∀ i, ∃ k : ℤ, threeAmp l c i = (2 : ℝ) ^ k) := by
  obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hc
  have hq' := hq
  unfold threeTested threeTestedOf at hq'
  obtain ⟨hmem, hpass, -, -⟩ := Finset.mem_filter.mp hq'
  obtain ⟨hpi, hrange⟩ := Finset.mem_product.mp hmem
  obtain ⟨-, -, hμ3, hμ4, -, -, hν3, -⟩ := D.threeBands_spec (by linarith) (D.one_le_U0 hD) hpass
  have hU0i : 0 < D.U0⁻¹ := inv_pos.mpr (by linarith [D.one_le_U0 hD])
  have hl := Fintype.mem_piFinset.mp hpi l
  simp only [↓reduceIte, Finset.mem_singleton] at hl
  refine ⟨⟨_, rfl⟩, hμ4, ⟨_, rfl⟩, hν3, Nat.lt_succ_iff.mp (Finset.mem_range.mp hrange), ?_,
    lt_trans (half_pos hU0i) hμ3, fun i => ?_, fun i => ?_⟩
  · change dyadicBand (D.clsSize G I l (q.1 l)) = 1
    rw [hl]; exact D.dyadicBand_clsSize_empty G I l
  · unfold threeAmp; split_ifs <;> exact dyadicBand_pos _
  · unfold threeAmp; split_ifs <;> exact ⟨_, rfl⟩

open Classical in
theorem threeBinVal_nonneg_of_mem (hD : 2 ≤ D.S.Dstar) (J Aw : ℕ) (G : bf.Grp) (I : ℤ × ℤ)
    (xs : ℝ) (l : Fin 4) (anc : ℕ → ∀ j, j ≠ l → Finset (D.Ms j G).Md →
      (D.Ms j G).alive (ancAt A.G (D.preAt I) (A.blkStart D.S.K I.1 - 4 * D.S.K)))
    (Iw h : ℕ) {c : ℝ × ℝ × ℕ × ℝ × (Fin 4 → ℝ)}
    (hc : c ∈ (D.threeTested G I xs l anc (D.toLeaf.sv l G I) Iw h).image
      (D.threeBinOf G I xs l anc (D.toLeaf.sv l G I) h)) :
    0 ≤ threeBinVal κ' J Aw l c := by
  obtain ⟨-, -, -, hν, -, -, hμ, hamp, -⟩ := D.threeBin_basic hD G I xs l anc Iw h hc
  rw [threeBinVal_eq]
  have := entryCU_nonneg' κ' J Aw
  have : 0 ≤ (c.2.1 ^ J)⁻¹ := inv_nonneg.mpr (pow_nonneg (by linarith) J)
  have : 0 ≤ ((2 : ℝ) ^ c.2.2.1)⁻¹ ^ (Aw + 1) := by positivity
  have : 0 ≤ ∏ j, threeAmp l c j := Finset.prod_nonneg fun j _ => (hamp j).le
  have := hμ.le
  positivity


/-- Retained three-core bins with anchors depending on `AncNe3 G I l` have nonnegative values. -/
theorem threeBinVal_nonneg_of_memA (hD : 2 ≤ D.S.Dstar) (J Aw : ℕ) {G : bf.Grp} {I : ℤ × ℤ}
    {xs : ℝ} {l : Fin 4} {anc : D.AncNe3 G I l → ℕ → ∀ j, j ≠ l → Finset (D.Ms j G).Md →
      (D.Ms j G).alive (ancAt A.G (D.preAt I) (A.blkStart D.S.K I.1 - 4 * D.S.K))}
    {Iw h : ℕ} {ε : ℝ} {c : ℝ × ℝ × ℕ × ℝ × (Fin 4 → ℝ)}
    (hc : c ∈ D.threeRetBinsA G I xs l anc Iw h ε) : 0 ≤ threeBinVal κ' J Aw l c := by
  unfold threeRetBinsA at hc
  split_ifs at hc with hA
  · exact D.threeBinVal_nonneg_of_mem hD J Aw G I xs l (anc hA) Iw h (Finset.mem_filter.mp hc).1
  · exact absurd hc (Finset.notMem_empty _)
open Classical in
/-- The per-cell decomposition of `eq:core-final` for three cores (side role `l`). -/
theorem three_principal_split (hD : 2 ≤ D.S.Dstar) (J Aw Iw : ℕ) (G : bf.Grp) (I : ℤ × ℤ)
    (y : ℝ) (l : Fin 4) (anc : ℕ → ∀ j, j ≠ l → Finset (D.Ms j G).Md →
      (D.Ms j G).alive (ancAt A.G (D.preAt I) (A.blkStart D.S.K I.1 - 4 * D.S.K)))
    (H : Finset ℕ)
    (hcard : ∀ j, (((D.Ms j G).alive (ancAt A.G (D.preAt I)
      (A.blkStart D.S.K I.1 - 4 * D.S.K))).card : ℝ) ≤ D.S.Dstar)
    {U ε : ℝ} (hU0 : 0 ≤ U) (hε : 0 ≤ ε)
    (hU : ∀ h ∈ H, ∀ j, j ≠ l → ∀ F ∈ D.goodCls G I j h, D.clsSize G I j F ≤ U)
    (hUs : Real.sqrt ((dyadicGridLength A.G I.1)⁻¹ *
      ∫ y in (dyadicGridLeft A.G I.1 I.2)..dyadicGridLeft A.G I.1 I.2 + dyadicGridLength A.G I.1,
        ‖augPhys (D.toLeaf.sv l G I) y‖ ^ 2) ≤ U) :
    ∑ h ∈ H, (H.card : ℝ)⁻¹ * ∑ c ∈ (D.threeTested G I y l anc (D.toLeaf.sv l G I) Iw h).image
        (D.threeBinOf G I y l anc (D.toLeaf.sv l G I) h), threeBinVal κ' J Aw l c *
          (((D.threeTested G I y l anc (D.toLeaf.sv l G I) Iw h).filter fun q =>
            D.threeBinOf G I y l anc (D.toLeaf.sv l G I) h q = c).card : ℝ) ≤
      ∑ h ∈ H, ∑ κ ∈ D.threeTypes l, (H.card : ℝ)⁻¹ * ∑ c ∈ D.threeRetBins G I y l anc Iw h ε,
        threeBinVal κ' J Aw l c * D.threeCnt G I y l anc Iw h c κ +
      8 * entryCU κ' J Aw * 2 ^ (Aw + 4) * 12 ^ 3 * ε * U ^ 3 * (D.S.Dstar ^ 3 * (Iw + 1)) := by
  set K₀ := 8 * entryCU κ' J Aw * 2 ^ (Aw + 4) * 12 ^ 3 * ε * U ^ 3 with hK₀
  have hK0 : 0 ≤ K₀ := by have := entryCU_nonneg' κ' J Aw; positivity
  have hD3 : (0 : ℝ) ≤ D.S.Dstar ^ 3 * (Iw + 1) := by
    have : (0 : ℝ) ≤ D.S.Dstar := by linarith
    positivity
  have hper : ∀ h ∈ H, ∑ c ∈ ((D.threeTested G I y l anc (D.toLeaf.sv l G I) Iw h).image
      (D.threeBinOf G I y l anc (D.toLeaf.sv l G I) h)).filter (fun c => ∃ j, threeAmp l c j < ε),
        threeBinVal κ' J Aw l c * (((D.threeTested G I y l anc (D.toLeaf.sv l G I) Iw h).filter
          fun q => D.threeBinOf G I y l anc (D.toLeaf.sv l G I) h q = c).card : ℝ) ≤
      K₀ * (D.S.Dstar ^ 3 * (Iw + 1)) := fun h hh =>
    (sum_bins_filter_le _ _ _ _ hK0 fun q hq hs => D.threeBinVal_small hD J Aw G I y l anc Iw h
      hε (hU h hh) hUs hq hs).trans
      (mul_le_mul_of_nonneg_left (D.card_threeTested_le G I y l anc _ Iw h hcard) hK0)
  have hneg : ∑ h ∈ H, (H.card : ℝ)⁻¹ * ∑ c ∈ ((D.threeTested G I y l anc (D.toLeaf.sv l G I)
      Iw h).image (D.threeBinOf G I y l anc (D.toLeaf.sv l G I) h)).filter
        (fun c => ∃ j, threeAmp l c j < ε), threeBinVal κ' J Aw l c *
          (((D.threeTested G I y l anc (D.toLeaf.sv l G I) Iw h).filter fun q =>
            D.threeBinOf G I y l anc (D.toLeaf.sv l G I) h q = c).card : ℝ) ≤
      K₀ * (D.S.Dstar ^ 3 * (Iw + 1)) := by
    calc _ ≤ ∑ _h ∈ H, (H.card : ℝ)⁻¹ * (K₀ * (D.S.Dstar ^ 3 * (Iw + 1))) :=
          Finset.sum_le_sum fun h hh => mul_le_mul_of_nonneg_left (hper h hh)
            (inv_nonneg.mpr (Nat.cast_nonneg _))
      _ = (H.card : ℝ) * (H.card : ℝ)⁻¹ * (K₀ * (D.S.Dstar ^ 3 * (Iw + 1))) := by
          rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ 1 * (K₀ * (D.S.Dstar ^ 3 * (Iw + 1))) := by
          refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg hK0 hD3)
          rcases (Nat.cast_nonneg (α := ℝ) H.card).eq_or_lt with h0 | h0
          · rw [← h0]; norm_num
          · rw [mul_inv_cancel₀ h0.ne']
      _ = _ := one_mul _
  have hret : ∀ h ∈ H, ∑ c ∈ (D.threeTested G I y l anc (D.toLeaf.sv l G I) Iw h).image
      (D.threeBinOf G I y l anc (D.toLeaf.sv l G I) h), threeBinVal κ' J Aw l c *
        (((D.threeTested G I y l anc (D.toLeaf.sv l G I) Iw h).filter fun q =>
          D.threeBinOf G I y l anc (D.toLeaf.sv l G I) h q = c).card : ℝ) =
      ∑ κ ∈ D.threeTypes l, ∑ c ∈ D.threeRetBins G I y l anc Iw h ε,
        threeBinVal κ' J Aw l c * D.threeCnt G I y l anc Iw h c κ +
      ∑ c ∈ ((D.threeTested G I y l anc (D.toLeaf.sv l G I) Iw h).image
        (D.threeBinOf G I y l anc (D.toLeaf.sv l G I) h)).filter
        (fun c => ∃ j, threeAmp l c j < ε), threeBinVal κ' J Aw l c *
          (((D.threeTested G I y l anc (D.toLeaf.sv l G I) Iw h).filter fun q =>
            D.threeBinOf G I y l anc (D.toLeaf.sv l G I) h q = c).card : ℝ) := by
    intro h _
    rw [← Finset.sum_filter_add_sum_filter_not _ (fun c => ∀ j, ε ≤ threeAmp l c j)]
    congr 1
    · rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [D.card_bin_eq_sum_types3 G I y l anc _ Iw h hcard c, Finset.mul_sum]
      rfl
    · refine Finset.sum_congr ?_ fun _ _ => rfl
      ext c
      simp only [Finset.mem_filter, not_forall, not_le]
  calc _ = ∑ h ∈ H, ((H.card : ℝ)⁻¹ * ∑ κ ∈ D.threeTypes l,
        ∑ c ∈ D.threeRetBins G I y l anc Iw h ε,
          threeBinVal κ' J Aw l c * D.threeCnt G I y l anc Iw h c κ + (H.card : ℝ)⁻¹ *
        ∑ c ∈ ((D.threeTested G I y l anc (D.toLeaf.sv l G I) Iw h).image
          (D.threeBinOf G I y l anc (D.toLeaf.sv l G I) h)).filter
          (fun c => ∃ j, threeAmp l c j < ε), threeBinVal κ' J Aw l c *
            (((D.threeTested G I y l anc (D.toLeaf.sv l G I) Iw h).filter fun q =>
              D.threeBinOf G I y l anc (D.toLeaf.sv l G I) h q = c).card : ℝ)) :=
        Finset.sum_congr rfl fun h hh => by rw [hret h hh, mul_add]
    _ = _ + _ := Finset.sum_add_distrib
    _ ≤ _ := by
        refine add_le_add (le_of_eq ?_) (hneg.trans (le_of_eq (by rw [hK₀])))
        refine Finset.sum_congr rfl fun h _ => ?_
        rw [Finset.mul_sum]


open Classical in
/-- `three_principal_split` with anchors depending on a proof of `AncNe3 G I l`: without anchors
both principal quantities vanish. -/
theorem three_principal_splitA (hD : 2 ≤ D.S.Dstar) (J Aw Iw : ℕ) (G : bf.Grp) (I : ℤ × ℤ)
    (y : ℝ) (l : Fin 4) (anc : D.AncNe3 G I l → ℕ → ∀ j, j ≠ l → Finset (D.Ms j G).Md →
      (D.Ms j G).alive (ancAt A.G (D.preAt I) (A.blkStart D.S.K I.1 - 4 * D.S.K)))
    (H : Finset ℕ)
    (hcard : ∀ j, (((D.Ms j G).alive (ancAt A.G (D.preAt I)
      (A.blkStart D.S.K I.1 - 4 * D.S.K))).card : ℝ) ≤ D.S.Dstar)
    {U ε : ℝ} (hU0 : 0 ≤ U) (hε : 0 ≤ ε)
    (hU : ∀ h ∈ H, ∀ j, j ≠ l → ∀ F ∈ D.goodCls G I j h, D.clsSize G I j F ≤ U)
    (hUs : Real.sqrt ((dyadicGridLength A.G I.1)⁻¹ *
      ∫ y in (dyadicGridLeft A.G I.1 I.2)..dyadicGridLeft A.G I.1 I.2 + dyadicGridLength A.G I.1,
        ‖augPhys (D.toLeaf.sv l G I) y‖ ^ 2) ≤ U) :
    ∑ h ∈ H, (H.card : ℝ)⁻¹ * D.threeBinSumA J Aw Iw G I y l anc h ≤
      ∑ h ∈ H, ∑ κ ∈ D.threeTypes l, (H.card : ℝ)⁻¹ * ∑ c ∈ D.threeRetBinsA G I y l anc Iw h ε,
        threeBinVal κ' J Aw l c * D.threeCntA G I y l anc Iw h c κ +
      8 * entryCU κ' J Aw * 2 ^ (Aw + 4) * 12 ^ 3 * ε * U ^ 3 * (D.S.Dstar ^ 3 * (Iw + 1)) := by
  by_cases hA : D.AncNe3 G I l
  · simp only [threeBinSumA, threeRetBinsA, threeCntA, dite_eq_left hA]
    exact D.three_principal_split hD J Aw Iw G I y l (anc hA) H hcard hU0 hε hU hUs
  · simp only [threeBinSumA, threeRetBinsA, dite_eq_right hA, mul_zero, Finset.sum_const_zero,
      Finset.sum_empty, zero_add]
    have := entryCU_nonneg' κ' J Aw
    have : (0 : ℝ) ≤ D.S.Dstar := by linarith
    positivity
end SideInput

end ActiveSetup.BasicFamilies.FamParams

namespace ActiveSetup.BasicFamilies.FamParams
variable {κ' : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ' c₀} {bf : A.BasicFamilies}
  {fp : bf.FamParams}

namespace SideInput
variable (D : fp.SideInput)

theorem fourCc_nonneg {Cj CA CT CK : ℕ} {δs W : ℝ} (hV : D.S.Valid Cj CA CT CK δs W)
    (hd2 : 2 ≤ D.S.dmax) (hD : 2 ≤ D.S.Dstar) (hB : 2 ≤ D.S.Bstar) (hQ0 : 1 ≤ D.S.Q0) :
    0 ≤ D.fourCc := by
  have hm : 0 ≤ D.multPoly := by
    unfold multPoly
    have : 0 ≤ Real.log (288 * (D.S.Dstar ^ 5 * D.S.H)) := by
      refine Real.log_nonneg ?_
      have hH2 := hV.two_le_H hd2 hD hB hQ0
      have h5 : (1 : ℝ) ≤ D.S.Dstar ^ 5 := one_le_pow₀ (by linarith)
      nlinarith
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
    positivity
  have hl : 0 ≤ D.ellPoly := by
    unfold ellPoly
    have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    have := Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) D.S.dmax; linarith :
      (1 : ℝ) ≤ (D.S.dmax : ℝ) + 1)
    positivity
  unfold fourCc
  positivity

open Classical in
/-- Blueprint lines 2783-2806 at one point, height, core type tuple and three-core bin `c`
(side role `l`): the powered principal quantities along the path of `y` sum to at most
`(Q C₃ μ ν^{-J})^p · C_c (1 + log(8ν/μ))⁴ · K^{2-c/2}`, given the path caps of `eq:top-count` and
the side cap at `y` (`three_group_sum_side`, `three_coef_sched`). -/
theorem three_path_bin_bound {Cj CA CT CK : ℕ} {δs W : ℝ} (hV : D.S.Valid Cj CA CT CK δs W)
    (hCA : 1 ≤ CA) (hCT : 4 ≤ CT) (hd2 : 2 ≤ D.S.dmax) (hD : 2 ≤ D.S.Dstar)
    (hB : 2 ≤ D.S.Bstar) (hQ0 : 1 ≤ D.S.Q0) (hSP : D.SP = D.S.sideParams δs)
    (hdD : (D.S.dmax : ℝ) ≤ D.S.Dstar) (qG : bf.Grp → ℕ) (hqG : ∀ G, 1 ≤ qG G ∧ qG G ≤ D.S.Q0)
        (J Aw Iw
        : ℕ) (hIw : (2 : ℝ) ^ Iw ≤ 2 * D.U0)
    (l : Fin 4) (T : Finset (ℤ × ℤ)) (gs : ℤ × ℤ → Finset bf.Grp) (z : bf.Grp → ChartTag)
    (hGc : ∀ I ∈ T, ∀ G ∈ gs I, (∀ j, 8 * (D.Ms j G).Λ ≤ D.S.Ξ) ∧
      (∀ j, (D.Ms j G).zc = z G) ∧ (z G).dim ≤ D.S.dmax)
    (h : ℕ) (hh : 10 ≤ h) (hhJ : h ≤ D.SP.Jst)
    (rep : ∀ G j, ℕ → ℕ → ℤ × (ℤ × ℤ) × (D.Ms j G).Md → (D.Ms j G).Md)
    (hrep : ∀ I ∈ T, ∀ G ∈ gs I, ∀ j, (D.withQ0 (qG G)).RepOK G j h T (rep G j))
    (anc : ∀ (I : ℤ × ℤ) (G : bf.Grp), D.AncNe3 G I l → ℕ → ∀ j, j ≠ l → Finset (D.Ms j G).Md →
      (D.Ms j G).alive (ancAt A.G (D.preAt I) (A.blkStart D.S.K I.1 - 4 * D.S.K)))
    (hanc : ∀ I (hI : I ∈ T), ∀ G (hG : G ∈ gs I), ∀ (hA : D.AncNe3 G I l) j (hj : j ≠ l) F
      (hF : F ∈ (D.withQ0 (qG G)).goodCls G I j h),
      anc I G hA h j hj F = (D.withQ0 (qG G)).repAnchor G I j h (rep G j) (hrep I hI G hG j).1 hF)
    (y : ℝ) (c : ℝ × ℝ × ℕ × ℝ × (Fin 4 → ℝ)) (hc : 0 < c.1 ∧ c.1 ≤ 1 ∧ 1 ≤ c.2.1)
    (hσ : ∀ i, 0 < threeAmp l c i) (κ : Fin 4 → ℕ × ℕ) {K Q : ℝ} (hK : 0 ≤ K) (hQ : 0 ≤ Q)
    (hcap : ∀ i (hi : i ≠ l), ∑ G ∈ pathGroups (A := A) T gs y,
      (((D.withQ0 (qG G)).threeUsedReps G h y l (pathCell A.G T y) (fun s => anc (pathCell A.G T y
          s) G) Iw c κ
        (pathDepths (A := A) T gs y G) i hi).card : ℝ) ≤ K * threeAmp l c i ^ (-2 : ℝ))
    (hcapl : ∑ G ∈ pathGroups (A := A) T gs y, ∑ s ∈ pathDepths (A := A) T gs y G,
      (D.withQ0 (qG G)).sideWeight G l (pathCell A.G T y) c.2.2.2.1 s ≤ K * threeAmp l c l ^ (-2 :
          ℝ)) :
    ∑ G ∈ pathGroups (A := A) T gs y, ∑ s ∈ pathDepths (A := A) T gs y G,
      (Q * threeBinVal κ' J Aw l c * (D.withQ0 (qG G)).threeCntA G (pathCell A.G T y s) y l
        (anc (pathCell A.G T y s) G) Iw h c κ) ^ (1 - (1 / 300 : ℝ) / 4) ≤
      (Q * (8 * entryCU κ' J Aw * 2 ^ (Aw + 4) * 12 ^ 3)) ^ (1 - (1 / 300 : ℝ) / 4) *
        (c.1 ^ (1 - (1 / 300 : ℝ) / 4) * ((c.2.1 ^ J)⁻¹) ^ (1 - (1 / 300 : ℝ) / 4)) *
        (D.fourCc * (1 + Real.log (8 * c.2.1 / c.1)) ^ 4 * K ^ (2 - (1 / 300 : ℝ) / 2)) := by
  set p : ℝ := 1 - (1 / 300 : ℝ) / 4 with hp
  have hp0 : 0 < p := by rw [hp]; norm_num
  set Gy := pathGroups (A := A) T gs y with hGy
  set Sp := pathDepths (A := A) T gs y with hSp
  set cellOf := pathCell A.G T y with hcellOf
  have hpath : ∀ G ∈ Gy, ∀ s ∈ Sp G, cellOf s ∈ T ∧
      y ∈ dyadicGridCell A.G (cellOf s).1 (cellOf s).2 := fun G _ s hs =>
    ⟨(mem_pathDepths hs).1, (mem_pathDepths hs).2.1⟩
  have hcell : ∀ s, (cellOf s).1 = s := pathCell_fst A.G T y
  have hGdata : ∀ G ∈ Gy, ∃ I ∈ T, G ∈ gs I := fun G hG => by
    obtain ⟨I, hI, hGI⟩ := Finset.mem_biUnion.mp hG
    exact ⟨I, (Finset.mem_filter.mp hI).1, hGI⟩
  have hG : ∀ G ∈ Gy, (∀ j, 8 * (D.Ms j G).Λ ≤ D.S.Ξ) ∧ (∀ j, (D.Ms j G).zc = z G) ∧
      (z G).dim ≤ D.S.dmax ∧ ∃ hrep' : ∀ j, (D.withQ0 (qG G)).RepOK G j h T (rep G j),
        (D.withQ0 (qG G)).ThreePathAnc G h l T (rep G) hrep' cellOf (fun s => anc (cellOf s) G)
            (Sp G) := by
    intro G hGG
    obtain ⟨I, hIT, hGI⟩ := hGdata G hGG
    obtain ⟨hΛ, hz, hdim⟩ := hGc I hIT G hGI
    refine ⟨hΛ, hz, hdim, hrep I hIT G hGI, fun s hs hA j hj F hF => ?_⟩
    obtain ⟨hcT, -, hGc'⟩ := mem_pathDepths hs
    exact hanc (cellOf s) hcT G hGc' hA j hj F hF
  have hgs := D.three_group_sum_side hV hCA hCT hd2 hD hB hQ0 hSP hdD qG hqG Gy h hh hhJ l T rep z
      Sp
    hpath hcell (fun G s => anc (cellOf s) G) hG hIw c hc hσ κ hK hcap hcapl
  have hcard : ∀ G ∈ Gy, ∀ s ∈ Sp G, (((D.withQ0 (qG G)).threePathE G h y l cellOf (fun s => anc
      (cellOf s) G)
      Iw c κ s).card : ℝ) =
        (D.withQ0 (qG G)).threeCntA G (cellOf s) y l (anc (cellOf s) G) Iw h c κ := by
    intro G hGG s hs
    obtain ⟨hΛ, -, -, hrep', hanc'⟩ := hG G hGG
    unfold threeCntA
    split_ifs with hA
    · unfold threeCnt
      exact_mod_cast (D.withQ0 (qG G)).threePathE_card G h l T (rep G) hrep' hΛ
        (by simp only [SideInput.withQ0_S, ModeSchedule.withQ0_Dstar]; linarith) (hpath G hGG)
        hanc' Iw c κ hs hA
    · unfold threePathE
      rw [dite_eq_right hA, Finset.card_empty, Nat.cast_zero]
  have hcoef := D.three_coef_sched hV hd2 hD hB hQ0 hSP hhJ hc.1 hc.2.1 hc.2.2
  have hlog : (1 + Real.log (2 * c.2.1 / c.1)) ^ 4 ≤ (1 + Real.log (8 * c.2.1 / c.1)) ^ 4 := by
    have h1 : (1 : ℝ) ≤ 2 * c.2.1 / c.1 := by rw [le_div_iff₀ hc.1]; linarith [hc.2.1, hc.2.2]
    have h2 : 2 * c.2.1 / c.1 ≤ 8 * c.2.1 / c.1 :=
      div_le_div_of_nonneg_right (by linarith [hc.2.2]) hc.1.le
    have := Real.log_le_log (by linarith) h2
    exact pow_le_pow_left₀ (by linarith [Real.log_nonneg h1]) (by linarith) 4
  have hPi : 0 ≤ ∏ i, threeAmp l c i := Finset.prod_nonneg fun i _ => (hσ i).le
  have hC3 : 0 ≤ 8 * entryCU κ' J Aw * 2 ^ (Aw + 4) * 12 ^ 3 := by
    have := entryCU_nonneg' κ' J Aw; positivity
  have hν0 : 0 ≤ (c.2.1 ^ J)⁻¹ := inv_nonneg.mpr (pow_nonneg (by linarith [hc.2.2]) J)
  have hΛ0 : 0 ≤ ((2 : ℝ) ^ c.2.2.1)⁻¹ ^ (Aw + 1) := by positivity
  have hΛ1 : (((2 : ℝ) ^ c.2.2.1)⁻¹ ^ (Aw + 1)) ^ p ≤ 1 :=
    Real.rpow_le_one hΛ0 (pow_le_one₀ (inv_nonneg.mpr (by positivity))
      (inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num)))) hp0.le
  have hV0 : 0 ≤ Q * (8 * entryCU κ' J Aw * 2 ^ (Aw + 4) * 12 ^ 3) * (c.1 * (c.2.1 ^ J)⁻¹ *
      ((2 : ℝ) ^ c.2.2.1)⁻¹ ^ (Aw + 1)) :=
    mul_nonneg (mul_nonneg hQ hC3) (mul_nonneg (mul_nonneg hc.1.le hν0) hΛ0)
  have hK' : 0 ≤ K ^ (2 - (1 / 300 : ℝ) / 2) := Real.rpow_nonneg hK _
  calc ∑ G ∈ Gy, ∑ s ∈ Sp G, (Q * threeBinVal κ' J Aw l c *
        (D.withQ0 (qG G)).threeCntA G (cellOf s) y l (anc (cellOf s) G) Iw h c κ) ^ p
      = (Q * (8 * entryCU κ' J Aw * 2 ^ (Aw + 4) * 12 ^ 3) * (c.1 * (c.2.1 ^ J)⁻¹ *
          ((2 : ℝ) ^ c.2.2.1)⁻¹ ^ (Aw + 1))) ^ p *
        ((∑ G ∈ Gy, ∑ s ∈ Sp G, (((D.withQ0 (qG G)).threePathE G h y l cellOf (fun s => anc
            (cellOf s) G)
          Iw c κ s).card : ℝ) ^ p) * (∏ i, threeAmp l c i) ^ p) := by
        rw [Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun G hGG => ?_
        rw [Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun s hs => ?_
        rw [← hcard G hGG s hs, threeBinVal_eq,
          show Q * (8 * entryCU κ' J Aw * 2 ^ (Aw + 4) * 12 ^ 3 * (c.1 * (c.2.1 ^ J)⁻¹ *
            ((2 : ℝ) ^ c.2.2.1)⁻¹ ^ (Aw + 1)) * ∏ j, threeAmp l c j) *
            (((D.withQ0 (qG G)).threePathE G h y l cellOf (fun s => anc (cellOf s) G) Iw c κ s).card
                : ℝ) =
            (Q * (8 * entryCU κ' J Aw * 2 ^ (Aw + 4) * 12 ^ 3) * (c.1 * (c.2.1 ^ J)⁻¹ *
              ((2 : ℝ) ^ c.2.2.1)⁻¹ ^ (Aw + 1))) * (∏ j, threeAmp l c j) *
            (((D.withQ0 (qG G)).threePathE G h y l cellOf (fun s => anc (cellOf s) G) Iw c κ s).card
                : ℝ) by ring,
          Real.mul_rpow (mul_nonneg hV0 hPi) (Nat.cast_nonneg _), Real.mul_rpow hV0 hPi]
        ring
    _ ≤ (Q * (8 * entryCU κ' J Aw * 2 ^ (Aw + 4) * 12 ^ 3) * (c.1 * (c.2.1 ^ J)⁻¹ *
          ((2 : ℝ) ^ c.2.2.1)⁻¹ ^ (Aw + 1))) ^ p *
        (D.fourCc * (1 + Real.log (8 * c.2.1 / c.1)) ^ 4 * K ^ (2 - (1 / 300 : ℝ) / 2)) := by
        refine mul_le_mul_of_nonneg_left (hgs.trans ?_) (Real.rpow_nonneg hV0 _)
        calc _ ≤ (D.fourCc * (1 + Real.log (2 * c.2.1 / c.1)) ^ 4) *
              K ^ (2 - (1 / 300 : ℝ) / 2) := by
              refine mul_le_mul_of_nonneg_right ?_ hK'
              unfold fourCc
              exact hcoef
          _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlog
              (D.fourCc_nonneg hV hd2 hD hB hQ0)) hK'
    _ ≤ _ := by
        have hX : 0 ≤ D.fourCc * (1 + Real.log (8 * c.2.1 / c.1)) ^ 4 *
            K ^ (2 - (1 / 300 : ℝ) / 2) :=
          mul_nonneg (mul_nonneg (D.fourCc_nonneg hV hd2 hD hB hQ0) (by
            have h1 : (1 : ℝ) ≤ 8 * c.2.1 / c.1 := by
              rw [le_div_iff₀ hc.1]; linarith only [hc.2.1, hc.2.2]
            have := Real.log_nonneg h1
            positivity)) hK'
        refine mul_le_mul_of_nonneg_right ?_ hX
        rw [Real.mul_rpow (mul_nonneg hQ hC3) (mul_nonneg (mul_nonneg hc.1.le hν0) hΛ0),
          Real.mul_rpow (mul_nonneg hc.1.le hν0) hΛ0, Real.mul_rpow hc.1.le hν0]
        have h0 : 0 ≤ (Q * (8 * entryCU κ' J Aw * 2 ^ (Aw + 4) * 12 ^ 3)) ^ p *
            (c.1 ^ p * ((c.2.1 ^ J)⁻¹) ^ p) :=
          mul_nonneg (Real.rpow_nonneg (mul_nonneg hQ hC3) _)
            (mul_nonneg (Real.rpow_nonneg hc.1.le _) (Real.rpow_nonneg hν0 _))
        calc _ = (Q * (8 * entryCU κ' J Aw * 2 ^ (Aw + 4) * 12 ^ 3)) ^ p *
              (c.1 ^ p * ((c.2.1 ^ J)⁻¹) ^ p) * (((2 : ℝ) ^ c.2.2.1)⁻¹ ^ (Aw + 1)) ^ p := by ring
          _ ≤ (Q * (8 * entryCU κ' J Aw * 2 ^ (Aw + 4) * 12 ^ 3)) ^ p *
              (c.1 ^ p * ((c.2.1 ^ J)⁻¹) ^ p) * 1 := mul_le_mul_of_nonneg_left hΛ1 h0
          _ = _ := mul_one _

end SideInput

end ActiveSetup.BasicFamilies.FamParams

namespace ActiveSetup.BasicFamilies.FamParams
variable {κ' : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ' c₀} {bf : A.BasicFamilies}
  {fp : bf.FamParams}

namespace SideInput
variable (D : fp.SideInput)



end SideInput
end ActiveSetup.BasicFamilies.FamParams
end TrilinearHT.Auto
end
