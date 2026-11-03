/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

/- Adapted for Lean Pool from roos-j/lean-trilinearht at
7b4209609e6a7fb9d9935973ee8541495f943660. Imports, names, proof organization and
Mathlib interfaces have been updated; original authorship is retained above. -/

public import LeanPool.TrilinearHilbertTransform.Auto.Sec124BinaryLocalizationVariation.LeafBound

/-!
# Trilinear Hilbert transform: mainRange_wholeRanges
-/

@[expose] public section

section
namespace TrilinearHT.Auto
open MeasureTheory Metric
open scoped FourierTransform ComplexConjugate ENNReal
namespace ActiveSetup.BasicFamilies.FamParams
variable {κ : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ c₀} {bf : A.BasicFamilies}
  (fp : bf.FamParams)

open scoped Classical in
private def MainRangeWholeRangesHaStatement.{u_1, u_2} : Prop :=
  ∀ (κ : LocalKernelClass)
    (c₀ : ℕ)
    (A : ActiveSetup κ c₀)
    (bf : A.BasicFamilies)
    (fp : bf.FamParams)
    (l : Fin (4 : ℕ))
    (s : List (CatCol bf.Vtx))
    (d : bf.Vtx)
    (ι : Type u_1)
    (κ' : Type u_2)
    (grp : ι → bf.Grp)
    (T : ι → Finset κ')
    (u : ι → κ' → ℤ × ℤ)
    (rk : ι → κ' → ℕ)
    (hq : ι → κ' → ℕ),
  let L : ι → κ' → Finset (bf.Lab ⊕ Fin fp.Mc) :=
    fun (G : ι) (q : κ') => mainLabelsM A.G fp.Mc (bf.origCols l) s (u G q) (rk G q)
      (fun (x : bf.Vtx) => x ∈ fp.K.mask bf.admT A.famVtxBound (grp G) (hq G q)
      (bf.admAt (u G q))) d
  ∀ (β : ι → κ' → bf.Lab ⊕ Fin fp.Mc → ℂ),
  let key : ι → κ' → bf.Lab ⊕ Fin fp.Mc → bf.VLab fp.Mc :=
    fun (G : ι) (q : κ') => bf.vKey fp.Mc (u G q)
  let F : ι → bf.VLab fp.Mc → Finset κ' :=
    fun (G : ι) (v' : bf.VLab fp.Mc) => {q ∈ T G | ∃ v ∈ L G q, key G q v = v'}
  let occ : ι → bf.VLab fp.Mc → Finset (ℤ × ℤ) :=
    fun (G : ι) (v' : bf.VLab fp.Mc) => Finset.image (u G) (F G v')
  let g : ι → κ' → bf.VLab fp.Mc → ℂ :=
    fun (G : ι) (q : κ') (v' : bf.VLab fp.Mc) => ∑ v ∈ L G q with key G q v = v', β G q
      v
  let cc : ι → bf.VLab fp.Mc → ℤ × ℤ → ℂ :=
    fun (G : ι) (v' : bf.VLab fp.Mc) (I : ℤ × ℤ) => ∑ q ∈ F G v' with u G q = I, g G q
      v'
  let a : ι → bf.VLab fp.Mc → ℝ → ℂ :=
    occCoef A.G occ cc
  ∀ (G : ι) (v' : bf.VLab fp.Mc) (y : ℝ), a G v' y = ∑ q ∈ T G, (dyadicGridCell A.G (u
    G q).1 (u G q).2).indicator (fun (_ : ℝ) => g G q v') y


open scoped Classical in
private def MainRangeWholeRangesStage1Statement.{u_1, u_2} : Prop :=
  ∀ (κ : LocalKernelClass)
    (c₀ : ℕ)
    (A : ActiveSetup κ c₀)
    (bf : A.BasicFamilies)
    (fp : bf.FamParams)
    (l : Fin (4 : ℕ))
    (s : List (CatCol bf.Vtx))
    (_ : ∀ e ∈ s, ∃ R ∈ residueBox (bf.vtag e.tag).dim (9 : ℕ), ∃ (γ : ℝ), e = templateCol
      (bf.vtag e.tag) l R γ e.birth e.rank e.tag)
    (_ : ∀ e ∈ s, bf.occAvail (↑e.tag.2 : ℤ × ℤ) e.tag.1)
    (d : bf.Vtx)
    (ι : Type u_1)
    (κ' : Type u_2)
    [Fintype ι]
    (grp : ι → bf.Grp)
    (_ : Function.Injective grp)
    (k : ℕ)
    (T : ι → Finset κ')
    (u : ι → κ' → ℤ × ℤ)
    (_ : ∀ (G : ι), ∀ q ∈ T G, u G q ∈ A.cells)
    (rk : ι → κ' → ℕ)
    (hq : ι → κ' → ℕ)
    (_ : ∀ (G : ι) (q : κ'), hq G q ≤ fp.Hmax)
    (w : ι → κ' → ↥(ColumnL2 (bf.Lab ⊕ Fin fp.Mc)))
    (_ : ∀ (G : ι), ∀ q ∈ T G, fp.Cert k (grp G) (u G q))
    (ra : ℝ)
    (rb : ℝ)
    (_ : ∀ I ∈ A.cells, dyadicGridCell A.G I.1 I.2 ⊆ Set.Icc ra rb)
    (τ : ℝ)
    (_ : (0 : ℝ) < τ)
    (_ : τ ≤ (1 : ℝ))
    (_ : Real.exp ((↑A.Dg : ℝ) * ((1 : ℝ) + Real.log A.Hsrc + Real.log τ⁻¹) ^ A.Dg) ≤ fp.Hed)
    (N : ℕ)
    (_ : ∀ (y : ℝ), (Finset.card ({p : ι × (bf.Lab ⊕ Fin fp.Mc) | ∃ q ∈ T p.1, y ∈
      dyadicGridCell A.G (u p.1 q).1 (u p.1 q).2 ∧ p.2 ∈ mainLabelsM A.G fp.Mc
      (bf.origCols l) s (u p.1 q) (rk p.1 q) (fun (x : bf.Vtx) => x ∈ fp.K.mask bf.admT
      A.famVtxBound (grp p.1) (hq p.1 q) (bf.admAt (u p.1 q))) d})) ≤ N),
  let L : ι → κ' → Finset (bf.Lab ⊕ Fin fp.Mc) :=
    fun (G : ι) (q : κ') => mainLabelsM A.G fp.Mc (bf.origCols l) s (u G q) (rk G q)
      (fun (x : bf.Vtx) => x ∈ fp.K.mask bf.admT A.famVtxBound (grp G) (hq G q)
      (bf.admAt (u G q))) d
  ∀ (β : ι → κ' → bf.Lab ⊕ Fin fp.Mc → ℂ),
  let key : ι → κ' → bf.Lab ⊕ Fin fp.Mc → bf.VLab fp.Mc :=
    fun (G : ι) (q : κ') => bf.vKey fp.Mc (u G q)
  let F : ι → bf.VLab fp.Mc → Finset κ' :=
    fun (G : ι) (v' : bf.VLab fp.Mc) => {q ∈ T G | ∃ v ∈ L G q, key G q v = v'}
  let occ : ι → bf.VLab fp.Mc → Finset (ℤ × ℤ) :=
    fun (G : ι) (v' : bf.VLab fp.Mc) => Finset.image (u G) (F G v')
  let g : ι → κ' → bf.VLab fp.Mc → ℂ :=
    fun (G : ι) (q : κ') (v' : bf.VLab fp.Mc) => ∑ v ∈ L G q with key G q v = v', β G q
      v
  let cc : ι → bf.VLab fp.Mc → ℤ × ℤ → ℂ :=
    fun (G : ι) (v' : bf.VLab fp.Mc) (I : ℤ × ℤ) => ∑ q ∈ F G v' with u G q = I, g G q
      v'
  let a : ι → bf.VLab fp.Mc → ℝ → ℂ :=
    occCoef A.G occ cc
  ∀ (_ : ∀ (G : ι) (v' : bf.VLab fp.Mc) (y : ℝ), a G v' y ≠ (0 : ℂ) → ∃ q ∈ T G, y ∈
      dyadicGridCell A.G (u G q).1 (u G q).2 ∧ ∃ v ∈ L G q, key G q v = v')
    (_ : ∀ (G : ι), ∀ q ∈ T G, ∀ v ∈ L G q, ∀ y ∈ dyadicGridCell A.G (u G q).1 (u G q).2,
      mainScalar fp.Mc (bf.origCols l) s (bf.vLab fp.Mc (key G q v)) y = bf.vPhi fp.Mc s
      (key G q v) y)
    (_ : ∀ (G G' : ι) (q q' : κ'), q ∈ T G → q' ∈ T G' → ∀ v ∈ L G q, ∀ v' ∈ L G' q', ∀ y ∈
      dyadicGridCell A.G (u G q).1 (u G q).2, y ∈ dyadicGridCell A.G (u G' q').1 (u G'
      q').2 → bf.vLab fp.Mc (key G q v) = bf.vLab fp.Mc (key G' q' v') → key G q v = key
      G' q' v')
    (_ : ∀ (G : ι), (↑(↑(∑ q ∈ T G, w G q) : ℝ →ₘ[volume] ColumnHilbert (bf.Lab ⊕ Fin fp.Mc))
      : ℝ → ColumnHilbert (bf.Lab ⊕ Fin fp.Mc)) =ᵐ[volume] fun (y : ℝ) => ∑ v' : bf.VLab
      fp.Mc, a G v' y • privateColumnValue (mainScalar fp.Mc (bf.origCols l) s)
      (mainWeight fp.Mc (bf.origCols l)) (bf.vLab fp.Mc v') y),
  ‖∑ G : ι, ∑ q ∈ T G, w G q‖ ^ (2 : ℕ) ≤ ((1 : ℝ) + τ * (↑N : ℝ) * A.colBudget ^ (2 :
    ℕ)) * ∑ G : ι, ‖∑ q ∈ T G, w G q‖ ^ (2 : ℕ)




private theorem mainRange_wholeRanges_ha : MainRangeWholeRangesHaStatement := by
  classical
  intro κ c₀ A bf fp l s d ι κ' grp T u rk hq L β key F occ g cc a G v' y
  have h1 : ∀ I, (dyadicGridCell A.G I.1 I.2).indicator (fun _ => cc G v' I) y =
      ∑ q ∈ (F G v').filter (fun q => u G q = I),
        (dyadicGridCell A.G (u G q).1 (u G q).2).indicator (fun _ => g G q v') y := by
    intro I
    by_cases hy : y ∈ dyadicGridCell A.G I.1 I.2
    · rw [Set.indicator_of_mem hy]
      refine Finset.sum_congr rfl fun q hq => ?_
      rw [(Finset.mem_filter.mp hq).2, Set.indicator_of_mem hy]
    · rw [Set.indicator_of_notMem hy]
      refine (Finset.sum_eq_zero fun q hq => ?_).symm
      rw [(Finset.mem_filter.mp hq).2, Set.indicator_of_notMem hy]
  change ∑ I ∈ occ G v', _ = _
  simp_rw [h1]
  rw [Finset.sum_fiberwise_of_maps_to (s := F G v') (t := occ G v') (g := u G)
    (fun q hq => Finset.mem_image_of_mem (u G) hq)
    (fun q => (dyadicGridCell A.G (u G q).1 (u G q).2).indicator (fun _ => g G q v') y)]
  refine Finset.sum_subset (s₁ := F G v') (s₂ := T G)
    (f := fun q => (dyadicGridCell A.G (u G q).1 (u G q).2).indicator (fun _ => g G q v') y)
    (Finset.filter_subset _ _) fun q hq hqF => ?_
  have hg : g G q v' = 0 := by
    refine Finset.sum_eq_zero fun v hv => ?_
    exact absurd (Finset.mem_filter.mpr ⟨hq, v, (Finset.mem_filter.mp hv).1,
      (Finset.mem_filter.mp hv).2⟩) hqF
  rw [hg]
  simp
-- presence of a coefficient



private theorem mainRange_wholeRanges_stage_1 : MainRangeWholeRangesStage1Statement := by
  classical
  intro κ c₀ A bf fp l s hT htag d ι κ' inst grp hgrp k T u hu rk hq hqH w hcert ra rb hroot τ hτ
    hτ1 hHed N hN L β key F occ g cc a hpres hφ hfib hfun
  have hnorm : ∀ (b : bf.VLab fp.Mc → ℂ) (y : ℝ),
      (∀ v', b v' ≠ 0 → ∃ G, ∃ q ∈ T G, y ∈ dyadicGridCell A.G (u G q).1 (u G q).2 ∧
        ∃ v ∈ L G q, key G q v = v') →
      ‖∑ v', b v' • privateColumnValue (mainScalar fp.Mc (bf.origCols l) s)
          (mainWeight fp.Mc (bf.origCols l)) (bf.vLab fp.Mc v') y‖ =
        ‖groupOutput (bf.vPhi fp.Mc s) (bf.vEps fp.Mc) (fun v' _ => b v') y‖ := by
    intro b y hb
    rw [← groupOutput_pushforward (bf.vLab fp.Mc) (mainScalar fp.Mc (bf.origCols l) s)
      (mainWeight fp.Mc (bf.origCols l)) (fun v' _ => b v') y]
    refine groupOutput_fiber_norm (bf.vLab fp.Mc) _ _ _ _ (fun x => ?_)
      (fun v' => (bf.vEps_pos fp.Mc v').le) (fun v' _ => b v') y (fun v' hv' => ?_)
      (fun v' => bf.vEps_eq fp.Mc l v') (fun v₁ v₂ heq h₁ h₂ => ?_)
    · rcases x with x | n
      · exact ((bf.P x.1 x.2.1).Ψ.D.privateWeight_pos x.2.2).le
      · exact zero_le_one
    · obtain ⟨G, q, hq, hy, v, hv, rfl⟩ := hb v' hv'
      exact hφ G q hq v hv y hy
    · obtain ⟨G, q, hq, hy, v, hv, rfl⟩ := hb v₁ h₁
      obtain ⟨G', q', hq', hy', v'', hv'', rfl⟩ := hb v₂ h₂
      exact hfib G G' q q' hq hq' v hv v'' hv'' y hy hy' heq
  have hpt : ∀ G, (fun y => ‖((∑ q ∈ T G, w G q : ColumnL2 (bf.Lab ⊕ Fin fp.Mc)) :
      ℝ → ColumnHilbert (bf.Lab ⊕ Fin fp.Mc)) y‖ ^ 2) =ᵐ[volume]
      fun y => ‖groupOutput (bf.vPhi fp.Mc s) (bf.vEps fp.Mc) (a G) y‖ ^ 2 := by
    intro G
    filter_upwards [hfun G] with y hy
    rw [hy, hnorm (fun v' => a G v' y) y fun v' h => ⟨G, hpres G v' y h⟩]
    rfl
  have htot : (fun y => ‖((∑ G, ∑ q ∈ T G, w G q : ColumnL2 (bf.Lab ⊕ Fin fp.Mc)) :
      ℝ → ColumnHilbert (bf.Lab ⊕ Fin fp.Mc)) y‖ ^ 2) =ᵐ[volume]
      fun y => ‖∑ G, groupOutput (bf.vPhi fp.Mc s) (bf.vEps fp.Mc) (a G) y‖ ^ 2 := by
    have hall : ∀ᵐ y ∂volume, ∀ G, ((∑ q ∈ T G, w G q : ColumnL2 (bf.Lab ⊕ Fin fp.Mc)) :
        ℝ → ColumnHilbert (bf.Lab ⊕ Fin fp.Mc)) y =
          ∑ v', a G v' y • privateColumnValue (mainScalar fp.Mc (bf.origCols l) s)
            (mainWeight fp.Mc (bf.origCols l)) (bf.vLab fp.Mc v') y :=
      Filter.eventually_all.mpr hfun
    filter_upwards [Lp.coeFn_fun_finsetSum (Finset.univ : Finset ι)
      (fun G => (∑ q ∈ T G, w G q : ColumnL2 (bf.Lab ⊕ Fin fp.Mc))), hall] with y h1 h2
    rw [h1]
    simp only [h2]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul]
    have hb : ∀ v', ∑ G, a G v' y ≠ 0 → ∃ G, ∃ q ∈ T G,
        y ∈ dyadicGridCell A.G (u G q).1 (u G q).2 ∧ ∃ v ∈ L G q, key G q v = v' := by
      intro v' h
      obtain ⟨G, -, hG⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
      exact ⟨G, hpres G v' y hG⟩
    rw [hnorm (fun v' => ∑ G, a G v' y) y hb, sum_groupOutput]
    rfl
  -- the whole-range bound for the vertex-labelled outputs
  have hwr := fp.vWholeRanges l s hT htag d grp hgrp k occ ?_ cc
    (Mc' := ∑ G, ∑ q ∈ T G, ∑ v, ‖β G q v‖) (by positivity) ?_
    (K₀ := ∑ G, (T G).card) ?_ (ra := ra) (rb := rb) ?_ hτ hτ1 hHed (N := N) ?_
  rotate_left
  · -- the occurrences are certified endpoint occurrences
    intro G v' I hI
    obtain ⟨q, hqF, rfl⟩ := Finset.mem_image.mp hI
    obtain ⟨hqT, v, hv, hkey⟩ := Finset.mem_filter.mp hqF
    obtain ⟨hvL, hvM⟩ := mem_mainLabelsM.mp hv
    refine ⟨hu G q hqT, ?_, ⟨hq G q, hqH G q, ?_⟩, hcert G q hqT⟩
    · rw [← hkey]
      rcases v with x | n
      · exact ⟨x, mem_mainLabels.mp hvL, rfl⟩
      · obtain ⟨hn, -⟩ := (mem_mainLabels.mp hvL : ∃ hn : (n : ℕ) < s.length, _)
        exact hn
    · rw [← hkey]
      rcases v with x | n
      · exact hvM
      · exact hvM
  · intro G v' I
    refine (norm_sum_le _ _).trans ?_
    refine le_trans ?_ (Finset.single_le_sum (f := fun G => ∑ q ∈ T G, ∑ v, ‖β G q v‖)
      (fun _ _ => by positivity) (Finset.mem_univ G))
    refine le_trans (Finset.sum_le_sum fun q _ => norm_sum_le _ _) ?_
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg
      ((Finset.filter_subset _ _).trans (Finset.filter_subset _ _))
      fun _ _ _ => by positivity) ?_
    exact Finset.sum_le_sum fun q _ => Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ _) fun _ _ _ => norm_nonneg _
  · intro G v'
    refine (Finset.card_image_le.trans (Finset.card_filter_le _ _)).trans ?_
    exact Finset.single_le_sum (f := fun G => (T G).card) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ G)
  · intro G v' I hI
    obtain ⟨q, hqF, rfl⟩ := Finset.mem_image.mp hI
    exact hroot _ (hu G q (Finset.mem_filter.mp hqF).1)
  · intro y
    refine le_trans (Finset.card_le_card_of_injOn (fun p => (p.1, bf.vLab fp.Mc p.2))
      (fun p hp => ?_) (fun p hp p' hp' heq => ?_)) (hN y)
    · obtain ⟨-, hp⟩ := Finset.mem_filter.mp hp
      obtain ⟨q, hq, hy, v, hv, hkey⟩ := hpres p.1 p.2 y hp
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, q, hq, hy, ?_⟩
      dsimp only
      rw [← hkey, bf.vLab_vKey]
      exact hv
    · obtain ⟨-, hp⟩ := Finset.mem_filter.mp hp
      obtain ⟨-, hp'⟩ := Finset.mem_filter.mp hp'
      obtain ⟨q, hq, hy, v, hv, hkey⟩ := hpres p.1 p.2 y hp
      obtain ⟨q', hq', hy', v', hv', hkey'⟩ := hpres p'.1 p'.2 y hp'
      simp only [Prod.mk.injEq] at heq
      obtain ⟨h1, h2⟩ := heq
      refine Prod.ext h1 ?_
      rw [← hkey, ← hkey'] at h2 ⊢
      exact hfib p.1 p'.1 q q' hq hq' v hv v' hv' y hy hy' h2
  -- conclusion
  rw [columnL2_norm_sq_eq, integral_congr_ae htot]
  refine hwr.trans (le_of_eq ?_)
  congr 1
  refine Finset.sum_congr rfl fun G _ => ?_
  rw [columnL2_norm_sq_eq, integral_congr_ae (hpt G)]


open Classical in
/-- Blueprint lem:whole-ranges (lines 1777-1789) in vector form on the main columns: group vectors
that are sums of elements of main ranges at certified active cells, with the group's ball masks at
pads at most `H_max`, are almost orthogonal across the groups of one color,
`‖Σ_G Z_G‖² ≤ (1 + τ N colBudget²) Σ_G ‖Z_G‖²`, where at most `N` group-label pairs are present
at each point. -/
theorem mainRange_wholeRanges (l : Fin 4) (s : List (CatCol bf.Vtx))
    (hT : ∀ e ∈ s, ∃ R ∈ residueBox (bf.vtag e.tag).dim 9, ∃ γ : ℝ,
      e = templateCol (bf.vtag e.tag) l R γ e.birth e.rank e.tag)
    (htag : ∀ e ∈ s, bf.occAvail e.tag.2.1 e.tag.1) (d : bf.Vtx)
    {ι κ' : Type*} [Fintype ι] (grp : ι → bf.Grp) (hgrp : Function.Injective grp) (k : ℕ)
    (T : ι → Finset κ') (u : ι → κ' → ℤ × ℤ) (hu : ∀ G, ∀ q ∈ T G, u G q ∈ A.cells)
    (rk hq : ι → κ' → ℕ) (hqH : ∀ G q, hq G q ≤ fp.Hmax)
    (w : ι → κ' → ColumnL2 (bf.Lab ⊕ Fin fp.Mc))
    (hw : ∀ G, ∀ q ∈ T G, w G q ∈ mainRange A.G fp.Mc (bf.origCols l) s (u G q) (rk G q)
      (fun x => x ∈ fp.K.mask bf.admT A.famVtxBound (grp G) (hq G q) (bf.admAt (u G q))))
    (hcert : ∀ G, ∀ q ∈ T G, fp.Cert k (grp G) (u G q))
    {ra rb : ℝ} (hroot : ∀ I ∈ A.cells, dyadicGridCell A.G I.1 I.2 ⊆ Set.Icc ra rb)
    {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hHed : Real.exp (A.Dg * (1 + Real.log A.Hsrc + Real.log τ⁻¹) ^ A.Dg) ≤ fp.Hed)
    {N : ℕ} (hN : ∀ y, ((Finset.univ : Finset (ι × (bf.Lab ⊕ Fin fp.Mc))).filter fun p =>
      ∃ q ∈ T p.1, y ∈ dyadicGridCell A.G (u p.1 q).1 (u p.1 q).2 ∧
        p.2 ∈ mainLabelsM A.G fp.Mc (bf.origCols l) s (u p.1 q) (rk p.1 q)
          (fun x => x ∈ fp.K.mask bf.admT A.famVtxBound (grp p.1) (hq p.1 q)
            (bf.admAt (u p.1 q))) d).card ≤ N) :
    ‖∑ G, ∑ q ∈ T G, w G q‖ ^ 2 ≤
      (1 + τ * N * A.colBudget ^ 2) * ∑ G, ‖∑ q ∈ T G, w G q‖ ^ 2 := by
  set! L : ι → κ' → Finset (bf.Lab ⊕ Fin fp.Mc) := fun G q =>
    mainLabelsM A.G fp.Mc (bf.origCols l) s (u G q) (rk G q)
      (fun x => x ∈ fp.K.mask bf.admT A.famVtxBound (grp G) (hq G q) (bf.admAt (u G q))) d
  have hex : ∀ G q, ∃ β : bf.Lab ⊕ Fin fp.Mc → ℂ, q ∈ T G →
      w G q = ∑ v ∈ L G q, β v • mainCol A.G fp.Mc (bf.origCols l) s (u G q) v := by
    intro G q
    by_cases h : q ∈ T G
    · obtain ⟨β, hβ⟩ := mainRange_exists_coeffM d (hw G q h)
      exact ⟨β, fun _ => hβ⟩
    · exact ⟨0, fun h' => absurd h' h⟩
  choose β hβ using hex
  have hLsub : ∀ G, ∀ q ∈ T G, L G q ⊆ mainLabels A.G fp.Mc (bf.origCols l) s (u G q) (rk G q) :=
    fun G q _ => mainLabelsM_subset _ _ _ _ _
  -- the vertex-labelled occurrences and coefficients
  set! key : ι → κ' → bf.Lab ⊕ Fin fp.Mc → bf.VLab fp.Mc := fun G q => bf.vKey fp.Mc (u G q)
  set! F : ι → bf.VLab fp.Mc → Finset κ' := fun G v' =>
    (T G).filter fun q => ∃ v ∈ L G q, key G q v = v'
  set! occ : ι → bf.VLab fp.Mc → Finset (ℤ × ℤ) := fun G v' => (F G v').image (u G)
  set! g : ι → κ' → bf.VLab fp.Mc → ℂ := fun G q v' =>
    ∑ v ∈ (L G q).filter (fun v => key G q v = v'), β G q v
  set! cc : ι → bf.VLab fp.Mc → ℤ × ℤ → ℂ := fun G v' I =>
    ∑ q ∈ (F G v').filter (fun q => u G q = I), g G q v'
  set! a := occCoef A.G occ cc
  -- the combined coefficients as sums over the index set
  have ha : ∀ G v' y, a G v' y = ∑ q ∈ T G,
      (dyadicGridCell A.G (u G q).1 (u G q).2).indicator (fun _ => g G q v') y := by
    expose_names
    exact @mainRange_wholeRanges_ha κ c₀ A bf fp l s d ι κ' grp T u rk hq β
  have hpres : ∀ G v' y, a G v' y ≠ 0 → ∃ q ∈ T G,
      y ∈ dyadicGridCell A.G (u G q).1 (u G q).2 ∧ ∃ v ∈ L G q, key G q v = v' := by
    intro G v' y h
    rw [ha] at h
    obtain ⟨q, hq, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    have hy : y ∈ dyadicGridCell A.G (u G q).1 (u G q).2 := by
      by_contra hy; exact hne (Set.indicator_of_notMem hy _)
    rw [Set.indicator_of_mem hy] at hne
    obtain ⟨v, hv, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    exact ⟨q, hq, hy, v, (Finset.mem_filter.mp hv).1, (Finset.mem_filter.mp hv).2⟩
  -- the scalars agree at present labels, and present labels of one fiber agree
  have hφ : ∀ G q, q ∈ T G → ∀ v ∈ L G q, ∀ y ∈ dyadicGridCell A.G (u G q).1 (u G q).2,
      mainScalar fp.Mc (bf.origCols l) s (bf.vLab fp.Mc (key G q v)) y =
        bf.vPhi fp.Mc s (key G q v) y := by
    intro G q _ v hv y hy
    rcases v with x | n
    · have hx : (bf.origCols l).avail (u G q) x := mem_mainLabels.mp (mem_mainLabelsM.mp hv).1
      obtain ⟨-, -, -, -, -, he⟩ := bf.origCol_source l hx
      have hav : bf.occAvail (bf.vtxAt (u G q) x).2.1 (bf.vtxAt (u G q) x).1 := by
        rw [bf.vtxAt_fst]; exact (bf.vtxAt_spec hx.2).1
      change (bf.origCols l).scalar (bf.vtxAt (u G q) x).1 y =
        (if bf.occAvail (bf.vtxAt (u G q) x).2.1 (bf.vtxAt (u G q) x).1 then
          quadraticChartAtom (bf.vchart (bf.vtxAt (u G q) x)).2 else 0) y
      rw [ite_eq_left_of_eq_true _ _ (eq_true hav), bf.vtxAt_fst]
      exact he y hy
    · rfl
  have hfib : ∀ G G' q q', q ∈ T G → q' ∈ T G' → ∀ v ∈ L G q, ∀ v' ∈ L G' q', ∀ y,
      y ∈ dyadicGridCell A.G (u G q).1 (u G q).2 →
      y ∈ dyadicGridCell A.G (u G' q').1 (u G' q').2 →
      bf.vLab fp.Mc (key G q v) = bf.vLab fp.Mc (key G' q' v') → key G q v = key G' q' v' := by
    intro G G' q q' _ _ v hv v' hv' y hy hy' heq
    rw [bf.vLab_vKey, bf.vLab_vKey] at heq
    subst heq
    rcases v with x | n
    · have hx : (bf.origCols l).avail (u G q) x := mem_mainLabels.mp (mem_mainLabelsM.mp hv).1
      have hx' : (bf.origCols l).avail (u G' q') x :=
        mem_mainLabels.mp (mem_mainLabelsM.mp hv').1
      have h1 := (bf.vtxAt_spec hx.2).2 hy
      have h2 := (bf.vtxAt_spec hx'.2).2 hy'
      exact congrArg Sum.inl (bf.vtxAt_eq_of_meet hx.2 hx'.2 ⟨y, h1, h2⟩)
    · rfl
  -- the group vectors as functions
  have hfun : ∀ G, ((∑ q ∈ T G, w G q : ColumnL2 (bf.Lab ⊕ Fin fp.Mc)) :
      ℝ → ColumnHilbert (bf.Lab ⊕ Fin fp.Mc)) =ᵐ[volume] fun y =>
        ∑ v', a G v' y • privateColumnValue (mainScalar fp.Mc (bf.origCols l) s)
          (mainWeight fp.Mc (bf.origCols l)) (bf.vLab fp.Mc v') y := by
    intro G
    have hsum : ∑ q ∈ T G, w G q = ∑ q ∈ T G, ∑ v ∈ L G q,
        β G q v • mainCol A.G fp.Mc (bf.origCols l) s (u G q) v :=
      Finset.sum_congr rfl fun q hq => hβ G q hq
    rw [hsum]
    filter_upwards [bf.sum_mainCols_ae l s (T G) (u G) (rk G) (L G) (hLsub G) (β G)] with y hy
    rw [hy]
    simp_rw [ha, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ => ?_
    by_cases hyq : y ∈ dyadicGridCell A.G (u G q).1 (u G q).2
    · simp only [Set.indicator_of_mem hyq, g, Finset.sum_smul]
      rw [← Finset.sum_fiberwise (L G q) (key G q) (fun v => β G q v •
        privateColumnValue (mainScalar fp.Mc (bf.origCols l) s)
          (mainWeight fp.Mc (bf.origCols l)) v y)]
      refine Finset.sum_congr rfl fun v' _ => Finset.sum_congr rfl fun v hv => ?_
      rw [← (Finset.mem_filter.mp hv).2, bf.vLab_vKey]
    · simp only [Set.indicator_of_notMem hyq, zero_smul, Finset.sum_const_zero]
  -- pointwise norms of the group vectors and of their sum
  expose_names
  exact @mainRange_wholeRanges_stage_1 κ c₀ A bf fp l s hT htag d ι κ' inst grp hgrp k T u hu rk
    hq hqH w hcert ra rb hroot τ hτ hτ1 hHed N hN β hpres hφ hfib hfun

end ActiveSetup.BasicFamilies.FamParams

namespace ActiveSetup.BasicFamilies.FamParams
variable {κ : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ c₀} {bf : A.BasicFamilies}
  (fp : bf.FamParams)

/-- The global depth family of the ball projections of the slot `l` for the group `G`, the ball
level `j` and the pad index `p` (blueprint line 1859). -/
noncomputable def ballFamT (l : Fin 4) (s : List (CatCol bf.Vtx)) (mb : bf.MainBudget s)
    (G : bf.Grp) (j : ℕ) (p : Fin fp.P) : ColumnDepthFamily (bf.RLab fp.Mc s) :=
  (bf.mainBase fp.Mc s mb).withMask (fp.ballMaskT l s mb G j p)

theorem gBall_eq (l : Fin 4) (s : List (CatCol bf.Vtx)) (mb : bf.MainBudget s) (G : bf.Grp)
    (j : ℕ) (h : ℤ) :
    fp.gBall l s mb G j h = opAvg fun p : Fin fp.P => (fp.ballFamT l s mb G j p).proj h := rfl

theorem mainTree_mem (s : List (CatCol bf.Vtx)) (mb : bf.MainBudget s) {I : ℤ × ℤ}
    (hI : I ∈ A.cells) : I ∈ (bf.mainTree fp.Mc s mb).cells := A.cells_mem_tree hI

/-- At an active cell the ball depth projection after the restriction to the cell is the cell
projection of the main tree. -/
theorem ballFamT_cell (l : Fin 4) (s : List (CatCol bf.Vtx)) (mb : bf.MainBudget s)
    (G : bf.Grp) (j : ℕ) (p : Fin fp.P) {I : ℤ × ℤ} (hI : I ∈ A.cells) :
    ((fp.ballFamT l s mb G j p).proj I.1).comp
      (columnL2Restriction (dyadicGridCell A.G I.1 I.2) (dyadicGridCell_measurable A.G I.1 I.2)) =
      cellColumnProjection (bf.mainTree fp.Mc s mb) (fp.ballMaskT l s mb G j p)
        (fp.mainTree_mem s mb hI) :=
  ((fp.ballFamT l s mb G j p).restrict_proj I.1 (bf.mem_partition_mainBase fp.Mc s mb hI)).2

/-- The relabeled ball cell projection is the main ball projection of the cell. -/
theorem relabel_ballCell (l : Fin 4) (s : List (CatCol bf.Vtx)) (mb : bf.MainBudget s)
    (G : bf.Grp) (j : ℕ) (p : Fin fp.P) {I : ℤ × ℤ} (hI : I ∈ A.cells)
    (z : ColumnL2 (bf.RLab fp.Mc s)) :
    colRelabel (bf.rv fp.Mc s) (cellColumnProjection (bf.mainTree fp.Mc s mb)
      (fp.ballMaskT l s mb G j p) (fp.mainTree_mem s mb hI) z) =
      mainProj A.G fp.Mc (bf.origCols l) s I (fp.brank j) (fp.bmask I G j (p + 1))
        (colRelabel (bf.rv fp.Mc s) z) :=
  bf.relabel_cellProj l fp.Mc s mb (fp.brank j) (fun c => fp.bmask c G j (p + 1))
    (fun _ hc _ hd hcd x hx => fp.bmask_mono hc hd hcd G j (p + 1) x hx) hI z

/-- The relabeled ball rows of one interval on a union of active right-endpoint cells: the sum
over the cells of the main ball projection at the cell minus the main ball projection at its
left-endpoint ancestor applied to the cell restriction. -/
theorem ballFamT_interval_decomp (l : Fin 4) (s : List (CatCol bf.Vtx)) (mb : bf.MainBudget s)
    (hanc : A.AncClosed) (G : bf.Grp) (j : ℕ) (p : Fin fp.P) {hr ht : ℤ} (hR1 : A.R.1 ≤ hr)
    (hrt : hr ≤ ht) (Ec : Finset (ℤ × ℤ)) (hEc : ∀ I ∈ Ec, I ∈ A.cells ∧ I.1 = ht)
    (y : ColumnL2 (bf.RLab fp.Mc s)) :
    colRelabel (bf.rv fp.Mc s)
      (((fp.ballFamT l s mb G j p).proj ht - (fp.ballFamT l s mb G j p).proj hr)
        (columnL2Restriction (⋃ I ∈ Ec, dyadicGridCell A.G I.1 I.2)
          (Finset.measurableSet_biUnion Ec fun I _ => dyadicGridCell_measurable A.G I.1 I.2) y)) =
      ∑ I ∈ Ec, (mainProj A.G fp.Mc (bf.origCols l) s I (fp.brank j) (fp.bmask I G j (p + 1))
          (colRelabel (bf.rv fp.Mc s) y) -
        mainProj A.G fp.Mc (bf.origCols l) s (ancAt A.G I hr) (fp.brank j)
          (fp.bmask (ancAt A.G I hr) G j (p + 1))
          (colRelabel (bf.rv fp.Mc s) (columnL2Restriction (dyadicGridCell A.G I.1 I.2)
            (dyadicGridCell_measurable A.G I.1 I.2) y))) := by
  set Ψ := fp.ballFamT l s mb G j p
  rw [columnL2Restriction_biUnion Ec (fun I => dyadicGridCell A.G I.1 I.2)
    (fun I => dyadicGridCell_measurable A.G I.1 I.2)
    (cells_pairwiseDisjoint_of_depth A.G Ec fun I hI => (hEc I hI).2),
    sum_apply, map_sum, map_sum]
  refine Finset.sum_congr rfl fun I hI => ?_
  obtain ⟨hIc, hId⟩ := hEc I hI
  set rI := columnL2Restriction (V := bf.RLab fp.Mc s) (dyadicGridCell A.G I.1 I.2)
    (dyadicGridCell_measurable A.G I.1 I.2)
  have hIJ : dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G (ancAt A.G I hr).1
      (ancAt A.G I hr).2 := subset_ancAt A.G I (by omega)
  have hJc : ancAt A.G I hr ∈ A.cells :=
    hanc I hIc _ hIJ (ancAt_subset (A.sub I hIc) hR1)
  set! rJ := columnL2Restriction (V := bf.RLab fp.Mc s) (dyadicGridCell A.G (ancAt A.G I hr).1
    (ancAt A.G I hr).2) (dyadicGridCell_measurable A.G (ancAt A.G I hr).1 (ancAt A.G I hr).2)
  have h1 : (Ψ.proj ht).comp rI = cellColumnProjection (bf.mainTree fp.Mc s mb)
      (fp.ballMaskT l s mb G j p) (fp.mainTree_mem s mb hIc) := by
    rw [← hId]; exact fp.ballFamT_cell l s mb G j p hIc
  have h2 : (Ψ.proj hr).comp rI = (cellColumnProjection (bf.mainTree fp.Mc s mb)
      (fp.ballMaskT l s mb G j p) (fp.mainTree_mem s mb hJc)).comp rI := by
    calc (Ψ.proj hr).comp rI = (Ψ.proj hr).comp (rJ.comp rI) := by
          rw [columnL2Restriction_comp_of_subset' _ _ hIJ]
      _ = ((Ψ.proj hr).comp rJ).comp rI := (ContinuousLinearMap.comp_assoc _ _ _).symm
      _ = _ := congrArg (fun T => T.comp rI) (fp.ballFamT_cell l s mb G j p hJc)
  rw [sub_apply, ← ContinuousLinearMap.comp_apply (Ψ.proj ht) rI, h1,
    ← ContinuousLinearMap.comp_apply (Ψ.proj hr) rI, h2, ContinuousLinearMap.comp_apply, map_sub,
    fp.relabel_ballCell l s mb G j p hIc, fp.relabel_ballCell l s mb G j p hJc]

/-- The relabeled right-endpoint ball rows on a union of active cells of their depth. -/
theorem ballFamT_right_decomp (l : Fin 4) (s : List (CatCol bf.Vtx)) (mb : bf.MainBudget s)
    (G : bf.Grp) (j : ℕ) (p : Fin fp.P) {ht : ℤ} (Ec : Finset (ℤ × ℤ))
    (hEc : ∀ I ∈ Ec, I ∈ A.cells ∧ I.1 = ht) (y : ColumnL2 (bf.RLab fp.Mc s)) :
    colRelabel (bf.rv fp.Mc s) ((fp.ballFamT l s mb G j p).proj ht
      (columnL2Restriction (⋃ I ∈ Ec, dyadicGridCell A.G I.1 I.2)
        (Finset.measurableSet_biUnion Ec fun I _ => dyadicGridCell_measurable A.G I.1 I.2) y)) =
      ∑ I ∈ Ec, mainProj A.G fp.Mc (bf.origCols l) s I (fp.brank j) (fp.bmask I G j (p + 1))
        (colRelabel (bf.rv fp.Mc s) y) := by
  rw [columnL2Restriction_biUnion Ec (fun I => dyadicGridCell A.G I.1 I.2)
    (fun I => dyadicGridCell_measurable A.G I.1 I.2)
    (cells_pairwiseDisjoint_of_depth A.G Ec fun I hI => (hEc I hI).2), sum_apply, map_sum,
    map_sum]
  refine Finset.sum_congr rfl fun I hI => ?_
  obtain ⟨hIc, hId⟩ := hEc I hI
  have h1 := fp.ballFamT_cell l s mb G j p hIc
  rw [← hId, ← ContinuousLinearMap.comp_apply ((fp.ballFamT l s mb G j p).proj I.1), h1,
    fp.relabel_ballCell l s mb G j p hIc]

end ActiveSetup.BasicFamilies.FamParams

namespace ActiveSetup.BasicFamilies.FamParams
variable {κ : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ c₀} {bf : A.BasicFamilies}
  (fp : bf.FamParams)

open Classical in
/-- `eq:whole-ranges` for the interval rows of the variation on the main columns (blueprint lines
1875: "their adjoints lie in sums of whole ball ranges at the two endpoints; a right certificate
certifies every needed earlier endpoint ... Lemma whole-ranges makes the rows jointly Bessel across
groups"). -/
theorem main_wr1 (l : Fin 4) (s : List (CatCol bf.Vtx))
    (hT : ∀ e ∈ s, ∃ R ∈ residueBox (bf.vtag e.tag).dim 9, ∃ γ : ℝ,
      e = templateCol (bf.vtag e.tag) l R γ e.birth e.rank e.tag)
    (htag : ∀ e ∈ s, bf.occAvail e.tag.2.1 e.tag.1) (d : bf.Vtx) (mb : bf.MainBudget s)
    (hanc : A.AncClosed) {ι ι' : Type*} [Fintype ι] [Fintype ι'] (grp : ι → bf.Grp)
    (hgrp : Function.Injective grp) (k j : ℕ) (hPH : fp.bbase j + fp.P ≤ fp.Hmax)
    (r t : ι' → ℕ) (hrt : ∀ i, r i ≤ t i) (Ec : ι → ι' → Finset (ℤ × ℤ))
    (hEc : ∀ G i, ∀ I ∈ Ec G i, I ∈ A.cells ∧ I.1 = A.R.1 + t i)
    (hcert : ∀ G i, ∀ I ∈ Ec G i, fp.Cert k (grp G) I)
    {ra rb : ℝ} (hroot : ∀ I ∈ A.cells, dyadicGridCell A.G I.1 I.2 ⊆ Set.Icc ra rb)
    {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hHed : Real.exp (A.Dg * (1 + Real.log A.Hsrc + Real.log τ⁻¹) ^ A.Dg) ≤ fp.Hed)
    {N : ℕ} (hN : ∀ y, ((Finset.univ : Finset (ι × (bf.Lab ⊕ Fin fp.Mc))).filter fun q =>
      ∃ I ∈ A.cells, (∃ k', fp.Cert k' (grp q.1) I) ∧
        ∃ p : Fin fp.P, y ∈ dyadicGridCell A.G I.1 I.2 ∧
        q.2 ∈ mainLabelsM A.G fp.Mc (bf.origCols l) s I (fp.brank j)
          (fp.bmask I (grp q.1) j (p + 1)) d).card ≤ N)
    (p : Fin fp.P) (x : ι × ι' → ColumnL2 (bf.RLab fp.Mc s)) :
    ‖∑ q : ι × ι', ContinuousLinearMap.adjoint
        ((columnL2Restriction (⋃ I ∈ Ec q.1 q.2, dyadicGridCell A.G I.1 I.2)
          (Finset.measurableSet_biUnion _ fun I _ => dyadicGridCell_measurable A.G I.1 I.2)).comp
          ((fp.ballFamT l s mb (grp q.1) j p).proj (A.R.1 + t q.2) -
            (fp.ballFamT l s mb (grp q.1) j p).proj (A.R.1 + r q.2))) (x q)‖ ^ 2 ≤
      (1 + τ * N * A.colBudget ^ 2) * ∑ G, ‖∑ q ∈ (Finset.univ : Finset (ι × ι')).filter
        (fun q => q.1 = G), ContinuousLinearMap.adjoint
          ((columnL2Restriction (⋃ I ∈ Ec q.1 q.2, dyadicGridCell A.G I.1 I.2)
            (Finset.measurableSet_biUnion _ fun I _ =>
              dyadicGridCell_measurable A.G I.1 I.2)).comp
            ((fp.ballFamT l s mb (grp q.1) j p).proj (A.R.1 + t q.2) -
              (fp.ballFamT l s mb (grp q.1) j p).proj (A.R.1 + r q.2))) (x q)‖ ^ 2 := by
  set! ι₀ := colRelabel (bf.rv fp.Mc s)
  have hiso : ∀ z, ‖ι₀ z‖ = ‖z‖ := norm_colRelabel (bf.rv_injective fp.Mc s)
  set F : ι × ι' → ColumnL2 (bf.RLab fp.Mc s) := fun q => ContinuousLinearMap.adjoint
    ((columnL2Restriction (⋃ I ∈ Ec q.1 q.2, dyadicGridCell A.G I.1 I.2)
      (Finset.measurableSet_biUnion _ fun I _ => dyadicGridCell_measurable A.G I.1 I.2)).comp
      ((fp.ballFamT l s mb (grp q.1) j p).proj (A.R.1 + t q.2) -
        (fp.ballFamT l s mb (grp q.1) j p).proj (A.R.1 + r q.2))) (x q) with hF
  -- the index of the main vectors
  set! T : ι → Finset ((Σ _ : ι', ℤ × ℤ) × Bool) := fun G =>
    ((Finset.univ : Finset ι').sigma (Ec G)) ×ˢ Finset.univ
  set! u : ι → (Σ _ : ι', ℤ × ℤ) × Bool → ℤ × ℤ := fun _ q =>
    if q.2 then q.1.2 else ancAt A.G q.1.2 (A.R.1 + r q.1.1)
  set! w : ι → (Σ _ : ι', ℤ × ℤ) × Bool → ColumnL2 (bf.Lab ⊕ Fin fp.Mc) := fun G q =>
    if q.2 then mainProj A.G fp.Mc (bf.origCols l) s q.1.2 (fp.brank j)
      (fp.bmask q.1.2 (grp G) j (p + 1)) (ι₀ (x (G, q.1.1)))
    else -mainProj A.G fp.Mc (bf.origCols l) s (ancAt A.G q.1.2 (A.R.1 + r q.1.1)) (fp.brank j)
      (fp.bmask (ancAt A.G q.1.2 (A.R.1 + r q.1.1)) (grp G) j (p + 1))
        (ι₀ (columnL2Restriction (dyadicGridCell A.G q.1.2.1 q.1.2.2)
          (dyadicGridCell_measurable A.G q.1.2.1 q.1.2.2) (x (G, q.1.1))))
  -- each relabeled group term is the sum of its main vectors
  have hFG : ∀ G i, ι₀ (F (G, i)) = ∑ I ∈ Ec G i, (w G ⟨⟨i, I⟩, true⟩ + w G ⟨⟨i, I⟩, false⟩) := by
    intro G i
    simp only [hF, ContinuousLinearMap.adjoint_comp, map_sub, ColumnDepthFamily.proj_adjoint,
      columnL2Restriction_adjoint, ContinuousLinearMap.comp_apply]
    rw [fp.ballFamT_interval_decomp l s mb hanc (grp G) j p (by omega)
      (by have := hrt i; omega) (Ec G i) (hEc G i) (x (G, i))]
    refine Finset.sum_congr rfl fun I _ => ?_
    simp only [w, ↓reduceIte, sub_eq_add_neg, Bool.false_eq_true]
    rfl
  have hTsum : ∀ G, ∑ q ∈ T G, w G q =
      ∑ i, ∑ I ∈ Ec G i, (w G ⟨⟨i, I⟩, true⟩ + w G ⟨⟨i, I⟩, false⟩) := by
    intro G
    simp only [T, Finset.sum_product, Finset.sum_sigma, Fintype.sum_bool]
  have hgroup : ∀ G, ι₀ (∑ q ∈ (Finset.univ : Finset (ι × ι')).filter (fun q => q.1 = G), F q) =
      ∑ q ∈ T G, w G q := by
    intro G
    rw [sum_filter_fst_eq F G, map_sum, hTsum]
    exact Finset.sum_congr rfl fun i _ => hFG G i
  have htotal : ι₀ (∑ q : ι × ι', F q) = ∑ G, ∑ q ∈ T G, w G q := by
    rw [map_sum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun G _ => ?_
    rw [hTsum]
    exact Finset.sum_congr rfl fun i _ => hFG G i
  change ‖∑ q : ι × ι', F q‖ ^ 2 ≤ (1 + τ * N * A.colBudget ^ 2) * ∑ G,
    ‖∑ q ∈ (Finset.univ : Finset (ι × ι')).filter (fun q => q.1 = G), F q‖ ^ 2
  rw [← hiso, htotal]
  simp only [← hiso, hgroup]
  -- the cells of the vectors are active and certified
  have hu : ∀ G, ∀ q ∈ T G, u G q ∈ A.cells ∧
      dyadicGridCell A.G q.1.2.1 q.1.2.2 ⊆ dyadicGridCell A.G (u G q).1 (u G q).2 := by
    intro G q hq
    obtain ⟨hq1, -⟩ := Finset.mem_product.mp hq
    obtain ⟨-, hI⟩ := Finset.mem_sigma.mp hq1
    obtain ⟨hIc, hId⟩ := hEc G q.1.1 q.1.2 hI
    rcases q with ⟨⟨i, I⟩, b⟩
    cases b
    · have hIJ := subset_ancAt A.G I (d := A.R.1 + r i) (by
        have := hrt i; simp only at hId; omega)
      exact ⟨hanc I hIc _ hIJ (ancAt_subset (A.sub I hIc) (by omega)), hIJ⟩
    · exact ⟨hIc, subset_rfl⟩
  have hcu : ∀ G, ∀ q ∈ T G, fp.Cert k (grp G) (u G q) := by
    intro G q hq
    obtain ⟨hq1, -⟩ := Finset.mem_product.mp hq
    obtain ⟨-, hI⟩ := Finset.mem_sigma.mp hq1
    exact (hcert G q.1.1 q.1.2 hI).mono fp (hu G q hq).2
  refine fp.mainRange_wholeRanges l s hT htag d grp hgrp k T u (fun G q hq => (hu G q hq).1)
    (fun _ _ => fp.brank j) (fun _ _ => fp.bbase j + (p + 1)) (fun _ _ => by have := p.2; omega)
    w ?_ hcu hroot hτ hτ1 hHed ?_
  · intro G q _
    rcases q with ⟨⟨i, I⟩, b⟩
    cases b
    · exact Submodule.neg_mem _ (Submodule.starProjection_apply_mem _ _)
    · exact Submodule.starProjection_apply_mem _ _
  · intro y
    refine le_trans (Finset.card_le_card fun q hq => ?_) (hN y)
    obtain ⟨-, e, he, hy, hv⟩ := Finset.mem_filter.mp hq
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, u q.1 e, (hu q.1 e he).1, ⟨k, hcu q.1 e he⟩,
      p, hy, hv⟩

open Classical in
/-- `eq:whole-ranges` for the outer ball rows at a common right endpoint on the main columns
(blueprint line 1877: "sum the outer ball rows at each common right endpoint using
eq:whole-ranges"). -/
theorem main_wr2 (l : Fin 4) (s : List (CatCol bf.Vtx))
    (hT : ∀ e ∈ s, ∃ R ∈ residueBox (bf.vtag e.tag).dim 9, ∃ γ : ℝ,
      e = templateCol (bf.vtag e.tag) l R γ e.birth e.rank e.tag)
    (htag : ∀ e ∈ s, bf.occAvail e.tag.2.1 e.tag.1) (d : bf.Vtx) (mb : bf.MainBudget s)
    {ι : Type*} [Fintype ι] (grp : ι → bf.Grp)
    (hgrp : Function.Injective grp) (k j : ℕ) (hPH : fp.bbase j + fp.P ≤ fp.Hmax)
    (ht : ℤ) (Ec : ι → Finset (ℤ × ℤ)) (hEc : ∀ G, ∀ I ∈ Ec G, I ∈ A.cells ∧ I.1 = ht)
    (hcert : ∀ G, ∀ I ∈ Ec G, fp.Cert k (grp G) I)
    {ra rb : ℝ} (hroot : ∀ I ∈ A.cells, dyadicGridCell A.G I.1 I.2 ⊆ Set.Icc ra rb)
    {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hHed : Real.exp (A.Dg * (1 + Real.log A.Hsrc + Real.log τ⁻¹) ^ A.Dg) ≤ fp.Hed)
    {N : ℕ} (hN : ∀ y, ((Finset.univ : Finset (ι × (bf.Lab ⊕ Fin fp.Mc))).filter fun q =>
      ∃ I ∈ A.cells, (∃ k', fp.Cert k' (grp q.1) I) ∧
        ∃ p : Fin fp.P, y ∈ dyadicGridCell A.G I.1 I.2 ∧
        q.2 ∈ mainLabelsM A.G fp.Mc (bf.origCols l) s I (fp.brank j)
          (fp.bmask I (grp q.1) j (p + 1)) d).card ≤ N)
    (p : Fin fp.P) (x : ι → ColumnL2 (bf.RLab fp.Mc s)) :
    ‖∑ G, ContinuousLinearMap.adjoint
        ((columnL2Restriction (⋃ I ∈ Ec G, dyadicGridCell A.G I.1 I.2)
          (Finset.measurableSet_biUnion _ fun I _ => dyadicGridCell_measurable A.G I.1 I.2)).comp
          ((fp.ballFamT l s mb (grp G) j p).proj ht)) (x G)‖ ^ 2 ≤
      (1 + τ * N * A.colBudget ^ 2) * ∑ G, ‖∑ G' ∈ (Finset.univ : Finset ι).filter
        (fun G' => G' = G), ContinuousLinearMap.adjoint
          ((columnL2Restriction (⋃ I ∈ Ec G', dyadicGridCell A.G I.1 I.2)
            (Finset.measurableSet_biUnion _ fun I _ =>
              dyadicGridCell_measurable A.G I.1 I.2)).comp
            ((fp.ballFamT l s mb (grp G') j p).proj ht)) (x G')‖ ^ 2 := by
  set! ι₀ := colRelabel (bf.rv fp.Mc s)
  have hiso : ∀ z, ‖ι₀ z‖ = ‖z‖ := norm_colRelabel (bf.rv_injective fp.Mc s)
  have hFG : ∀ G, ι₀ (ContinuousLinearMap.adjoint
      ((columnL2Restriction (⋃ I ∈ Ec G, dyadicGridCell A.G I.1 I.2)
        (Finset.measurableSet_biUnion _ fun I _ => dyadicGridCell_measurable A.G I.1 I.2)).comp
        ((fp.ballFamT l s mb (grp G) j p).proj ht)) (x G)) =
      ∑ I ∈ Ec G, mainProj A.G fp.Mc (bf.origCols l) s I (fp.brank j)
        (fp.bmask I (grp G) j (p + 1)) (ι₀ (x G)) := by
    intro G
    rw [ContinuousLinearMap.adjoint_comp, ColumnDepthFamily.proj_adjoint,
      columnL2Restriction_adjoint, ContinuousLinearMap.comp_apply]
    exact fp.ballFamT_right_decomp l s mb (grp G) j p (Ec G) (hEc G) (x G)
  have hsingle : ∀ G, (Finset.univ : Finset ι).filter (fun G' => G' = G) = {G} := by
    intro G; ext G'; simp
  simp only [hsingle, Finset.sum_singleton]
  rw [← hiso, map_sum]
  simp only [← hiso, hFG]
  refine fp.mainRange_wholeRanges l s hT htag d grp hgrp k Ec (fun _ I => I)
    (fun G I hI => (hEc G I hI).1) (fun _ _ => fp.brank j) (fun _ _ => fp.bbase j + (p + 1))
    (fun _ _ => by have := p.2; omega)
    (fun G I => mainProj A.G fp.Mc (bf.origCols l) s I (fp.brank j)
      (fp.bmask I (grp G) j (p + 1)) (ι₀ (x G)))
    (fun _ _ _ => Submodule.starProjection_apply_mem _ _) hcert hroot hτ hτ1 hHed ?_
  intro y
  refine le_trans (Finset.card_le_card fun q hq => ?_) (hN y)
  obtain ⟨-, e, he, hy, hv⟩ := Finset.mem_filter.mp hq
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, e, (hEc q.1 e he).1, ⟨k, hcert q.1 e he⟩, p, hy,
    hv⟩

end ActiveSetup.BasicFamilies.FamParams

namespace ActiveSetup
variable {κ : LocalKernelClass} {c₀ : ℕ} (A : ActiveSetup κ c₀)

/-- The restriction to a union of cells of the setup vanishes off the root. -/
theorem restrict_union_vanish' {V : Type*} [Fintype V] (Ec : Finset (ℤ × ℤ))
    (hEc : ∀ I ∈ Ec, I ∈ A.cells) (v : ColumnL2 V) :
    ∀ᵐ y ∂volume, y ∉ dyadicGridCell A.G A.R.1 A.R.2 →
      (columnL2Restriction (⋃ I ∈ Ec, dyadicGridCell A.G I.1 I.2)
        (Finset.measurableSet_biUnion Ec fun I _ => dyadicGridCell_measurable A.G I.1 I.2) v :
          ℝ → ColumnHilbert V) y = 0 := by
  filter_upwards [columnL2Indicator_coeFn _ (Finset.measurableSet_biUnion Ec fun I _ =>
    dyadicGridCell_measurable A.G I.1 I.2) v] with y hy hyR
  change (columnL2Indicator _ (Finset.measurableSet_biUnion Ec fun I _ =>
    dyadicGridCell_measurable A.G I.1 I.2) v : ℝ → ColumnHilbert V) y = 0
  rw [hy, Set.indicator_of_notMem]
  intro hmem
  obtain ⟨I, hI, hyI⟩ := Set.mem_iUnion₂.mp hmem
  exact hyR (A.sub I (hEc I hI) hyI)

end ActiveSetup

namespace ActiveSetup.BasicFamilies.FamParams
variable {κ : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ c₀} {bf : A.BasicFamilies}
  (fp : bf.FamParams)

/-- The interval rows of the variation split orthogonally over the depth partition of the main
tree at the left depth. -/
theorem main_blk (l : Fin 4) (s : List (CatCol bf.Vtx)) (mb : bf.MainBudget s) (G : bf.Grp)
    (j : ℕ) (p : Fin fp.P) {hr ht : ℤ} (hrt : hr ≤ ht) (Ec : Finset (ℤ × ℤ))
    (hEc : ∀ I ∈ Ec, I ∈ A.cells) (x : ColumnL2 (bf.RLab fp.Mc s)) :
    ‖((columnL2Restriction (⋃ I ∈ Ec, dyadicGridCell A.G I.1 I.2)
        (Finset.measurableSet_biUnion _ fun I _ => dyadicGridCell_measurable A.G I.1 I.2)).comp
        ((fp.ballFamT l s mb G j p).proj ht - (fp.ballFamT l s mb G j p).proj hr)) x‖ ^ 2
      = ∑ Q : {Q // Q ∈ ((bf.mainBase fp.Mc s mb).partition hr).cells},
        ‖((columnL2Restriction (⋃ I ∈ Ec, dyadicGridCell A.G I.1 I.2)
          (Finset.measurableSet_biUnion _ fun I _ => dyadicGridCell_measurable A.G I.1 I.2)).comp
          ((fp.ballFamT l s mb G j p).proj ht - (fp.ballFamT l s mb G j p).proj hr))
          (columnL2Restriction (dyadicGridCell A.G Q.1.1 Q.1.2)
            (dyadicGridCell_measurable A.G Q.1.1 Q.1.2) x)‖ ^ 2 := by
  set Ψ := fp.ballFamT l s mb G j p
  set Ψ0 := bf.mainBase fp.Mc s mb
  set E := columnL2Restriction (V := bf.RLab fp.Mc s) (⋃ I ∈ Ec, dyadicGridCell A.G I.1 I.2)
    (Finset.measurableSet_biUnion _ fun I _ => dyadicGridCell_measurable A.G I.1 I.2)
  have hv := A.restrict_union_vanish' Ec hEc ((Ψ.proj ht - Ψ.proj hr) x)
  rw [ContinuousLinearMap.comp_apply, Ψ0.norm_sq_partition hr _ hv]
  refine Finset.sum_congr rfl fun Q _ => ?_
  have h1 := Ψ.proj_comm_restrict (h' := hr) (h := ht) hrt Q.2
  have h2 := Ψ.proj_comm_restrict (h' := hr) (h := hr) le_rfl Q.2
  have h3 := columnL2Restriction_comm (V := bf.RLab fp.Mc s)
    (dyadicGridCell_measurable A.G Q.1.1 Q.1.2)
    (Finset.measurableSet_biUnion Ec fun I _ => dyadicGridCell_measurable A.G I.1 I.2)
  congr 2
  rw [ContinuousLinearMap.comp_apply, sub_apply, sub_apply, map_sub, map_sub]
  change (columnL2Restriction _ (dyadicGridCell_measurable A.G Q.1.1 Q.1.2)).comp E
      (Ψ.proj ht x) - (columnL2Restriction _ (dyadicGridCell_measurable A.G Q.1.1 Q.1.2)).comp E
      (Ψ.proj hr x) = _
  rw [h3, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ← ContinuousLinearMap.comp_apply _ (Ψ.proj ht), ← ContinuousLinearMap.comp_apply _ (Ψ.proj hr)]
  change E (((columnL2Restriction _ (dyadicGridCell_measurable Ψ.D.grid Q.1.1 Q.1.2)).comp
    (Ψ.proj ht)) x) - E (((columnL2Restriction _
      (dyadicGridCell_measurable Ψ.D.grid Q.1.1 Q.1.2)).comp (Ψ.proj hr)) x) = _
  rw [← h1, ← h2, ← map_sub]
  rfl

open Classical in
/-- Blueprint lem:variation (`eq:variation`, lines 1861-1877) on the main columns for one ball
level and color of the attempt, with a common input `z`: the global ball outputs
`Z_{G,s} = L_{G,s} B'_s z` of the groups, restricted at the right endpoints to unions of certified
active cells, have square-summable variation over disjoint depth intervals,
`Σ_{G,[r,t]} ‖1_E (Z_{G,t} - Z_{G,r})‖² ≤ 2 (1 + τ N colBudget²) (C_{|ls|}² + |ls| Σ_m C_m²) ‖z‖²`
with the complement compression constants `C_m` of the main tree. -/
theorem main_variation (l : Fin 4) (s : List (CatCol bf.Vtx))
    (hT : ∀ e ∈ s, ∃ R ∈ residueBox (bf.vtag e.tag).dim 9, ∃ γ : ℝ,
      e = templateCol (bf.vtag e.tag) l R γ e.birth e.rank e.tag)
    (htag : ∀ e ∈ s, bf.occAvail e.tag.2.1 e.tag.1) (d : bf.Vtx) (mb : bf.MainBudget s)
    (hanc : A.AncClosed) {ι ι' : Type*} [Fintype ι] [Fintype ι'] (grp : ι → bf.Grp)
    (hgrp : Function.Injective grp) (k j : ℕ) (hPH : fp.bbase j + fp.P ≤ fp.Hmax)
    (ls : List (ℕ × Bool)) (r t : ι' → ℕ) (hrt : ∀ i, r i ≤ t i)
    (hdis : ∀ i i', i ≠ i' → Disjoint (Finset.Ioc (r i) (t i)) (Finset.Ioc (r i') (t i')))
    (Ec : ι → ι' → Finset (ℤ × ℤ))
    (hEc : ∀ G i, ∀ I ∈ Ec G i, I ∈ A.cells ∧ I.1 = A.R.1 + t i)
    (hcert : ∀ G i, ∀ I ∈ Ec G i, fp.Cert k (grp G) I)
    {ra rb : ℝ} (hroot : ∀ I ∈ A.cells, dyadicGridCell A.G I.1 I.2 ⊆ Set.Icc ra rb)
    {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hHed : Real.exp (A.Dg * (1 + Real.log A.Hsrc + Real.log τ⁻¹) ^ A.Dg) ≤ fp.Hed)
    {N : ℕ} (hN : ∀ y, ((Finset.univ : Finset (ι × (bf.Lab ⊕ Fin fp.Mc))).filter fun q =>
      ∃ I ∈ A.cells, (∃ k', fp.Cert k' (grp q.1) I) ∧
        ∃ p : Fin fp.P, y ∈ dyadicGridCell A.G I.1 I.2 ∧
        q.2 ∈ mainLabelsM A.G fp.Mc (bf.origCols l) s I (fp.brank j)
          (fp.bmask I (grp q.1) j (p + 1)) d).card ≤ N)
    (z : ColumnL2 (bf.RLab fp.Mc s)) :
    ∑ q : ι × ι', ‖columnL2Restriction (⋃ I ∈ Ec q.1 q.2, dyadicGridCell A.G I.1 I.2)
        (Finset.measurableSet_biUnion _ fun I _ => dyadicGridCell_measurable A.G I.1 I.2)
        (fp.gBall l s mb (grp q.1) j (A.R.1 + t q.2) (fp.gHist l s mb ls (A.R.1 + t q.2) z) -
          fp.gBall l s mb (grp q.1) j (A.R.1 + r q.2) (fp.gHist l s mb ls (A.R.1 + r q.2) z))‖ ^ 2
      ≤ 2 * (1 + τ * N * A.colBudget ^ 2) *
        (compressionC (bf.mainTree fp.Mc s mb) ls.length ^ 2 * ‖z‖ ^ 2 +
          ls.length * (∑ m ∈ Finset.range ls.length,
            compressionC (bf.mainTree fp.Mc s mb) m ^ 2) * ‖z‖ ^ 2) := by
  set! Ψ0 := bf.mainBase fp.Mc s mb
  set! Am := fp.cumMaskT l s mb
  set! T := Finset.univ.sup t
  have ht : ∀ i, t i ≤ T := fun i => Finset.le_sup (f := t) (Finset.mem_univ i)
  have hCw : (0 : ℝ) ≤ 1 + τ * N * A.colBudget ^ 2 := by positivity
  have key := certifiedVariation_avg T fp.hP
    (fun p G n => (fp.ballFamT l s mb (grp G) j p).proj (A.R.1 + n))
    (fun p G n _ => ColumnDepthFamily.isStarProjection_proj _ _)
    (fun p G a _ b _ hab => ColumnDepthFamily.proj_nested _ (by omega))
    (fun G i => columnL2Restriction (⋃ I ∈ Ec G i, dyadicGridCell A.G I.1 I.2)
      (Finset.measurableSet_biUnion _ fun I _ => dyadicGridCell_measurable A.G I.1 I.2))
    (fun G i y => columnL2Indicator_norm_le _ (Finset.measurableSet_biUnion _ fun I _ =>
      dyadicGridCell_measurable A.G I.1 I.2) y) r t hrt ht hdis
    (fun i => globHist Ψ0 Am ls (A.R.1 + t i) z) (fun i => globHist Ψ0 Am ls (A.R.1 + r i) z) z
    (G₀ := compressionC Ψ0.D ls.length ^ 2)
    (J := ls.length * (∑ m ∈ Finset.range ls.length, compressionC Ψ0.D m ^ 2) * ‖z‖ ^ 2) hCw
    (fun p x => fp.main_wr1 l s hT htag d mb hanc grp hgrp k j hPH r t hrt Ec hEc hcert hroot hτ
      hτ1 hHed hN p x)
    ?_
    (fun p i x => fp.main_wr2 l s hT htag d mb grp hgrp k j hPH (A.R.1 + t i) (fun G => Ec G i)
      (fun G => hEc G i) (fun G => hcert G i) hroot hτ hτ1 hHed hN p x)
    (globHist_jump Ψ0 fp.hP Am ls r t hrt hdis z)
  · have hD : Ψ0.D = bf.mainTree fp.Mc s mb := rfl
    rw [hD] at key
    refine le_trans (le_of_eq ?_) (key.trans (le_of_eq (by ring)))
    rfl
  · intro p c hc hB
    have h := globHist_compression Ψ0 fp.hP Am ls (fun q : ι × ι' => A.R.1 + r q.2)
      (fun q => (columnL2Restriction (⋃ I ∈ Ec q.1 q.2, dyadicGridCell A.G I.1 I.2)
        (Finset.measurableSet_biUnion _ fun I _ => dyadicGridCell_measurable A.G I.1 I.2)).comp
        ((fp.ballFamT l s mb (grp q.1) j p).proj (A.R.1 + t q.2) -
          (fp.ballFamT l s mb (grp q.1) j p).proj (A.R.1 + r q.2))) hc hB
      (fun q x => fp.main_blk l s mb (grp q.1) j p (by have := hrt q.2; omega)
        (Ec q.1 q.2) (fun I hI => (hEc q.1 q.2 I hI).1) x) z
    refine h.trans (le_of_eq ?_)
    ring

end ActiveSetup.BasicFamilies.FamParams

section EmbeddedBasic
variable {V W : Type*} [Fintype V] [Fintype W]

/-- Blueprint lines 1859, 1879 for a rank-zero innermost factor: rows that are Bessel for all
inputs and split orthogonally over the cells of the depth partition of a basic column family remain
Bessel after inserting its depth projection through a contraction commuting with restrictions, at
the cost of one compression constant. -/
theorem emb_insert {ι F : Type*} [Fintype ι] [NormedAddCommGroup F] [NormedSpace ℂ F]
    (Ψ : ColumnDepthFamily V) (E : ColumnL2 V →L[ℂ] ColumnL2 W) (hE : ∀ x, ‖E x‖ ≤ ‖x‖)
    (hEr : ∀ (s : Set ℝ) (hs : MeasurableSet s) (x : ColumnL2 V),
      E (columnL2Restriction s hs x) = columnL2Restriction s hs (E x))
    (d : ι → ℤ) (R : ι → ColumnL2 W →L[ℂ] F) {B : ℝ} (hB : 0 ≤ B)
    (hR : ∀ x, ∑ i, ‖R i x‖ ^ 2 ≤ B * ‖x‖ ^ 2)
    (hblk : ∀ i x, ‖R i x‖ ^ 2 = ∑ Q : {Q // Q ∈ (Ψ.partition (d i)).cells},
      ‖R i (columnL2Restriction (dyadicGridCell Ψ.D.grid Q.1.1 Q.1.2)
        (dyadicGridCell_measurable Ψ.D.grid Q.1.1 Q.1.2) x)‖ ^ 2) (Z : ColumnL2 V) :
    ∑ i, ‖R i (E (Ψ.proj (d i) Z))‖ ^ 2 ≤ B * compressionC Ψ.D 1 ^ 2 * ‖Z‖ ^ 2 := by
  have h := globHist_compression Ψ (P := 1) Nat.one_pos (fun _ _ => Ψ.A) [(0, false)] d
    (fun i => (R i).comp E) hB
    (fun x => by
      refine le_trans ?_ (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) (hE x) 2) hB)
      exact hR _)
    (fun i x => by
      simp only [ContinuousLinearMap.comp_apply]
      rw [hblk i]
      simp_rw [hEr])
    Z
  refine le_trans (le_of_eq ?_) h
  refine Finset.sum_congr rfl fun i _ => ?_
  have e : globHist Ψ (P := 1) (fun _ _ => Ψ.A) [(0, false)] (d i) = Ψ.proj (d i) := by
    unfold globHist
    rw [show ([(0, false)] : List (ℕ × Bool)) = [] ++ [(0, false)] from rfl, layerOp_append,
      layerOp_nil]
    ext1 x
    simp [opAvg]
    rfl
  rw [e]
  rfl

/-- Blueprint lem:variation (`eq:variation`) for histories acting on a rank-zero basic projection
through a contraction commuting with restrictions: if the history rows `S_i (T_i(t_i) -
T_i(r_i))` are Bessel for all inputs and split over the basic partition at the left depths, then
the variation of the outputs `T_i(h) (E P_h Z)` is bounded by the compressed row constant plus the
joint size `J` of the outputs on the jumps of the basic projections. -/
theorem emb_variation {ι : Type*} [Fintype ι] (Ψ : ColumnDepthFamily V)
    (E : ColumnL2 V →L[ℂ] ColumnL2 W) (hE : ∀ x, ‖E x‖ ≤ ‖x‖)
    (hEr : ∀ (s : Set ℝ) (hs : MeasurableSet s) (x : ColumnL2 V),
      E (columnL2Restriction s hs x) = columnL2Restriction s hs (E x))
    (S : ι → ColumnL2 W →L[ℂ] ColumnL2 W) (T : ι → ℤ → ColumnL2 W →L[ℂ] ColumnL2 W)
    (r t : ι → ℤ) {B : ℝ} (hB : 0 ≤ B)
    (hrows : ∀ x, ∑ i, ‖S i ((T i (t i) - T i (r i)) x)‖ ^ 2 ≤ B * ‖x‖ ^ 2)
    (hblk : ∀ i x, ‖S i ((T i (t i) - T i (r i)) x)‖ ^ 2 =
      ∑ Q : {Q // Q ∈ (Ψ.partition (r i)).cells},
        ‖S i ((T i (t i) - T i (r i)) (columnL2Restriction (dyadicGridCell Ψ.D.grid Q.1.1 Q.1.2)
          (dyadicGridCell_measurable Ψ.D.grid Q.1.1 Q.1.2) x))‖ ^ 2)
    (Z : ColumnL2 V) {J : ℝ}
    (hjoint : ∑ i, ‖S i (T i (t i) (E ((Ψ.proj (t i) - Ψ.proj (r i)) Z)))‖ ^ 2 ≤ J) :
    ∑ i, ‖S i (T i (t i) (E (Ψ.proj (t i) Z)) - T i (r i) (E (Ψ.proj (r i) Z)))‖ ^ 2 ≤
      2 * (B * compressionC Ψ.D 1 ^ 2 * ‖Z‖ ^ 2) + 2 * J := by
  have hins := emb_insert Ψ E hE hEr r (fun i => (S i).comp (T i (t i) - T i (r i))) hB
    (fun x => hrows x) (fun i x => hblk i x) Z
  have hsplit : ∀ i, S i (T i (t i) (E (Ψ.proj (t i) Z)) - T i (r i) (E (Ψ.proj (r i) Z))) =
      S i ((T i (t i) - T i (r i)) (E (Ψ.proj (r i) Z))) +
        S i (T i (t i) (E ((Ψ.proj (t i) - Ψ.proj (r i)) Z))) := by
    intro i
    simp only [sub_apply, map_sub]
    abel
  calc ∑ i, ‖S i (T i (t i) (E (Ψ.proj (t i) Z)) - T i (r i) (E (Ψ.proj (r i) Z)))‖ ^ 2
      ≤ ∑ i, (2 * ‖S i ((T i (t i) - T i (r i)) (E (Ψ.proj (r i) Z)))‖ ^ 2 +
          2 * ‖S i (T i (t i) (E ((Ψ.proj (t i) - Ψ.proj (r i)) Z)))‖ ^ 2) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [hsplit i]
        set a := S i ((T i (t i) - T i (r i)) (E (Ψ.proj (r i) Z)))
        set b := S i (T i (t i) (E ((Ψ.proj (t i) - Ψ.proj (r i)) Z)))
        calc ‖a + b‖ ^ 2 ≤ (‖a‖ + ‖b‖) ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) (norm_add_le a b) 2
          _ ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by nlinarith [sq_nonneg (‖a‖ - ‖b‖)]
    _ = 2 * ∑ i, ‖S i ((T i (t i) - T i (r i)) (E (Ψ.proj (r i) Z)))‖ ^ 2 +
          2 * ∑ i, ‖S i (T i (t i) (E ((Ψ.proj (t i) - Ψ.proj (r i)) Z)))‖ ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ _ := by
        have := hins
        simp only [ContinuousLinearMap.comp_apply] at this
        gcongr

end EmbeddedBasic

namespace ActiveSetup.BasicFamilies
variable {κ : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ c₀} (bf : A.BasicFamilies)

/-- The embedding of the basic family `(l, j)` into the relevant main labels: the basic column
embedding followed by the adjoint of the relabeling. -/
noncomputable def famEmbR (Mc : ℕ) (s : List (CatCol bf.Vtx)) (l : Fin 4) (j : Fin 2) :
    ColumnL2 (bf.P l j).V →L[ℂ] ColumnL2 (bf.RLab Mc s) :=
  (ContinuousLinearMap.adjoint (colRelabel (bf.rv Mc s))).comp (bf.famEmb Mc l j)

theorem norm_famEmbR_le (Mc : ℕ) (s : List (CatCol bf.Vtx)) (l : Fin 4) (j : Fin 2)
    (x : ColumnL2 (bf.P l j).V) : ‖bf.famEmbR Mc s l j x‖ ≤ ‖x‖ :=
  (norm_colRelabel_adjoint_le (bf.rv_injective Mc s) _).trans
    (norm_colRelabel (bf.famEmb_injective Mc l j) x).le

theorem famEmbR_restrict (Mc : ℕ) (s : List (CatCol bf.Vtx)) (l : Fin 4) (j : Fin 2)
    (S : Set ℝ) (hS : MeasurableSet S) (x : ColumnL2 (bf.P l j).V) :
    bf.famEmbR Mc s l j (columnL2Restriction S hS x) =
      columnL2Restriction S hS (bf.famEmbR Mc s l j x) := by
  unfold famEmbR famEmb
  rw [ContinuousLinearMap.comp_apply, colRelabel_restrict, colRelabel_adjoint_restrict]
  rfl

end ActiveSetup.BasicFamilies

namespace ActiveSetup.BasicFamilies.FamParams
variable {κ : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ c₀} {bf : A.BasicFamilies}
  (fp : bf.FamParams)

/-- The global ball output of the slot `l` for the group `G` at the ball level `j` and the depth
`h`: the global ball filter after the global shared history (blueprint lines 1859, 1871:
`Z_{G,h} = L_{G,h} B'_h`). -/
noncomputable def gOut (l : Fin 4) (s : List (CatCol bf.Vtx)) (mb : bf.MainBudget s)
    (G : bf.Grp) (j : ℕ) (ls : List (ℕ × Bool)) (h : ℤ) :
    ColumnL2 (bf.RLab fp.Mc s) →L[ℂ] ColumnL2 (bf.RLab fp.Mc s) :=
  (fp.gBall l s mb G j h).comp (fp.gHist l s mb ls h)

/-- The global ball outputs at depth `h` commute with the restriction to every dyadic cell of
depth at most the clamped depth `h`. -/
theorem gOut_commute (l : Fin 4) (s : List (CatCol bf.Vtx)) (mb : bf.MainBudget s)
    (G : bf.Grp) (j : ℕ) (ls : List (ℕ × Bool)) (h : ℤ) {Q : ℤ × ℤ}
    (hQ : Q.1 ≤ (bf.mainBase fp.Mc s mb).depth h) :
    (columnL2Restriction (dyadicGridCell A.G Q.1 Q.2)
      (dyadicGridCell_measurable A.G Q.1 Q.2)).comp (fp.gOut l s mb G j ls h) =
    (fp.gOut l s mb G j ls h).comp (columnL2Restriction (dyadicGridCell A.G Q.1 Q.2)
      (dyadicGridCell_measurable A.G Q.1 Q.2)) := by
  set rQ := columnL2Restriction (V := bf.RLab fp.Mc s) (dyadicGridCell A.G Q.1 Q.2)
    (dyadicGridCell_measurable A.G Q.1 Q.2)
  have hball : ∀ p : Fin fp.P, ((fp.ballFamT l s mb G j p).proj h).comp rQ =
      rQ.comp ((fp.ballFamT l s mb G j p).proj h) := fun p =>
    ((fp.ballFamT l s mb G j p).proj_commute_restrict h hQ).symm
  have hcum : ∀ m, (opAvg fun p : Fin fp.P =>
      ((bf.mainBase fp.Mc s mb).withMask (fp.cumMaskT l s mb m p)).proj h).comp rQ =
      rQ.comp (opAvg fun p : Fin fp.P =>
        ((bf.mainBase fp.Mc s mb).withMask (fp.cumMaskT l s mb m p)).proj h) := fun m =>
    opAvg_commute _ _ fun p =>
      (((bf.mainBase fp.Mc s mb).withMask (fp.cumMaskT l s mb m p)).proj_commute_restrict h
        hQ).symm
  have hhist := layerOp_commute _ rQ hcum ls
  have hb2 := opAvg_commute _ _ hball
  unfold gOut gHist gBall globHist
  refine ContinuousLinearMap.ext fun x => ?_
  simp only [ContinuousLinearMap.comp_apply]
  have e1 := DFunLike.congr_fun hhist x
  simp only [ContinuousLinearMap.comp_apply] at e1
  rw [e1]
  have e2 := DFunLike.congr_fun hb2 (layerOp (fun m => opAvg fun p : Fin fp.P =>
    ((bf.mainBase fp.Mc s mb).withMask (fp.cumMaskT l s mb m p)).proj h) ls x)
  simp only [ContinuousLinearMap.comp_apply] at e2
  exact e2.symm ▸ rfl

/-- The restricted jump rows of the global ball outputs between two depths split orthogonally
over the depth partition of a basic family at the left depth. -/
theorem gOut_rows_blk (l : Fin 4) (s : List (CatCol bf.Vtx)) (mb : bf.MainBudget s)
    (G : bf.Grp) (j : ℕ) (ls : List (ℕ × Bool)) {hr ht : ℤ} (hrt : hr ≤ ht)
    (htd : ht ≤ A.R.1 + A.treeDepth) (E : Finset (ℤ × ℤ)) (hE : ∀ I ∈ E, I ∈ A.cells)
    {V : Type*} [Fintype V] (Ψ : ColumnDepthFamily V) (hΨG : Ψ.D.grid = A.G)
    (hΨR : dyadicGridCell A.G A.R.1 A.R.2 ⊆ dyadicGridCell A.G Ψ.D.root.1 Ψ.D.root.2)
    (hΨr : Ψ.D.root.1 ≤ A.R.1) (hRr : A.R.1 ≤ hr) (x : ColumnL2 (bf.RLab fp.Mc s)) :
    ‖((columnL2Restriction (⋃ I ∈ E, dyadicGridCell A.G I.1 I.2)
        (Finset.measurableSet_biUnion _ fun I _ => dyadicGridCell_measurable A.G I.1 I.2)).comp
        (fp.gOut l s mb G j ls ht - fp.gOut l s mb G j ls hr)) x‖ ^ 2 =
      ∑ Q : {Q // Q ∈ (Ψ.partition hr).cells},
        ‖((columnL2Restriction (⋃ I ∈ E, dyadicGridCell A.G I.1 I.2)
          (Finset.measurableSet_biUnion _ fun I _ => dyadicGridCell_measurable A.G I.1 I.2)).comp
          (fp.gOut l s mb G j ls ht - fp.gOut l s mb G j ls hr))
          (columnL2Restriction (dyadicGridCell Ψ.D.grid Q.1.1 Q.1.2)
            (dyadicGridCell_measurable Ψ.D.grid Q.1.1 Q.1.2) x)‖ ^ 2 := by
  have hEm : MeasurableSet (⋃ I ∈ E, dyadicGridCell A.G I.1 I.2) :=
    Finset.measurableSet_biUnion _ fun I _ => dyadicGridCell_measurable A.G I.1 I.2
  have hdepth : ∀ Q ∈ (Ψ.partition hr).cells, ∀ h : ℤ, hr ≤ h → h ≤ ht →
      Q.1 ≤ (bf.mainBase fp.Mc s mb).depth h := by
    intro Q hQ h h1 h2
    have hQ1 := ((Ψ.mem_partition _ Q).mp hQ).1
    have hle : Ψ.depth hr ≤ hr := by
      unfold ColumnDepthFamily.depth
      exact max_le (by omega) (min_le_left _ _)
    change Q.1 ≤ max A.R.1 (min h (A.R.1 + A.treeDepth))
    rw [hQ1]
    exact le_trans hle (le_trans (le_min h1 (by omega)) (le_max_right _ _))
  refine Ψ.blk_of_commute hr _ (fun y => ?_) (fun Q hQ => ?_) x
  · filter_upwards [columnL2Restriction_vanish _ hEm
      ((fp.gOut l s mb G j ls ht - fp.gOut l s mb G j ls hr) y)] with z hz hzR
    refine hz fun hzE => hzR ?_
    rw [Set.mem_iUnion₂] at hzE
    obtain ⟨I, hI, hzI⟩ := hzE
    rw [hΨG]
    exact hΨR (A.sub I (hE I hI) hzI)
  · have h1 := fp.gOut_commute l s mb G j ls ht (Q := Q) (hdepth Q hQ ht hrt le_rfl)
    have h2 := fp.gOut_commute l s mb G j ls hr (Q := Q) (hdepth Q hQ hr le_rfl hrt)
    have hc := columnL2Restriction_comm (V := bf.RLab fp.Mc s) hEm
      (dyadicGridCell_measurable A.G Q.1 Q.2)
    rw [hΨG, ContinuousLinearMap.comp_assoc, ContinuousLinearMap.sub_comp, ← h1, ← h2,
      ← ContinuousLinearMap.comp_sub,
      ← ContinuousLinearMap.comp_assoc, ← ContinuousLinearMap.comp_assoc, hc]

open Classical in
/-- Blueprint `eq:whole-ranges` (line 1875) for the global ball outputs of one depth: the
outputs of the groups, restricted to unions of certified cells of that depth, are jointly Bessel
with constant `1 + τ N colBudget²`. -/
theorem main_joint (l : Fin 4) (s : List (CatCol bf.Vtx))
    (hT : ∀ e ∈ s, ∃ R ∈ residueBox (bf.vtag e.tag).dim 9, ∃ γ : ℝ,
      e = templateCol (bf.vtag e.tag) l R γ e.birth e.rank e.tag)
    (htag : ∀ e ∈ s, bf.occAvail e.tag.2.1 e.tag.1) (d : bf.Vtx) (mb : bf.MainBudget s)
    {ι : Type*} [Fintype ι] (grp : ι → bf.Grp)
    (hgrp : Function.Injective grp) (k j : ℕ) (hPH : fp.bbase j + fp.P ≤ fp.Hmax)
    (ls : List (ℕ × Bool)) (ht : ℤ) (Ec : ι → Finset (ℤ × ℤ))
    (hEc : ∀ G, ∀ I ∈ Ec G, I ∈ A.cells ∧ I.1 = ht)
    (hcert : ∀ G, ∀ I ∈ Ec G, fp.Cert k (grp G) I)
    {ra rb : ℝ} (hroot : ∀ I ∈ A.cells, dyadicGridCell A.G I.1 I.2 ⊆ Set.Icc ra rb)
    {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hHed : Real.exp (A.Dg * (1 + Real.log A.Hsrc + Real.log τ⁻¹) ^ A.Dg) ≤ fp.Hed)
    {N : ℕ} (hN : ∀ y, ((Finset.univ : Finset (ι × (bf.Lab ⊕ Fin fp.Mc))).filter fun q =>
      ∃ I ∈ A.cells, (∃ k', fp.Cert k' (grp q.1) I) ∧
        ∃ p : Fin fp.P, y ∈ dyadicGridCell A.G I.1 I.2 ∧
        q.2 ∈ mainLabelsM A.G fp.Mc (bf.origCols l) s I (fp.brank j)
          (fp.bmask I (grp q.1) j (p + 1)) d).card ≤ N)
    (w : ColumnL2 (bf.RLab fp.Mc s)) :
    ∑ G, ‖columnL2Restriction (⋃ I ∈ Ec G, dyadicGridCell A.G I.1 I.2)
        (Finset.measurableSet_biUnion _ fun I _ => dyadicGridCell_measurable A.G I.1 I.2)
        (fp.gOut l s mb (grp G) j ls ht w)‖ ^ 2 ≤ (1 + τ * N * A.colBudget ^ 2) * ‖w‖ ^ 2 := by
  have hp := fp.hP
  have : Nonempty (Fin fp.P) := ⟨⟨0, hp⟩⟩
  set! H := fp.gHist l s mb ls ht w
  set! rE : ι → ColumnL2 (bf.RLab fp.Mc s) →L[ℂ] ColumnL2 (bf.RLab fp.Mc s) := fun G =>
    columnL2Restriction (⋃ I ∈ Ec G, dyadicGridCell A.G I.1 I.2)
      (Finset.measurableSet_biUnion _ fun I _ => dyadicGridCell_measurable A.G I.1 I.2)
  have hC : (0 : ℝ) ≤ 1 + τ * N * A.colBudget ^ 2 := by positivity
  have hpad : ∀ p : Fin fp.P, ∑ G, ‖rE G ((fp.ballFamT l s mb (grp G) j p).proj ht H)‖ ^ 2 ≤
      (1 + τ * N * A.colBudget ^ 2) * ‖w‖ ^ 2 := by
    intro p
    have hj := joint_bessel_of_wholeRanges (Finset.univ : Finset ι) (fun G => G)
      (fun G => (rE G).comp ((fp.ballFamT l s mb (grp G) j p).proj ht))
      (fun G h' => by
        rw [Finset.sum_eq_single_of_mem G (by simp) (fun b hb hne => by
          exact absurd (Finset.mem_filter.mp hb).2 hne)]
        have h1 : ‖((rE G).comp ((fp.ballFamT l s mb (grp G) j p).proj ht)) h'‖ ≤ ‖h'‖ := by
          simp only [ContinuousLinearMap.comp_apply, rE]
          exact (columnL2Indicator_norm_le _ (Finset.measurableSet_biUnion _ fun I _ =>
            dyadicGridCell_measurable A.G I.1 I.2) _).trans (starProjection_norm_apply_le _
              ((fp.ballFamT l s mb (grp G) j p).isStarProjection_proj ht) h')
        exact pow_le_pow_left₀ (norm_nonneg _) h1 2)
      hC (fun x => fp.main_wr2 l s hT htag d mb grp hgrp k j hPH ht Ec hEc hcert hroot hτ
        hτ1 hHed hN p x) H
    refine hj.trans (mul_le_mul_of_nonneg_left ?_ hC)
    exact pow_le_pow_left₀ (norm_nonneg _) (globHist_norm_le _ hp _ ls ht w) 2
  have h := rows_uniformAvg_le rE
    (fun G (p : Fin fp.P) => (fp.ballFamT l s mb (grp G) j p).proj ht H)
    hpad
  refine le_trans (le_of_eq ?_) h
  refine Finset.sum_congr rfl fun G _ => ?_
  simp only [gOut, gBall_eq, ContinuousLinearMap.comp_apply, opAvg, Fintype.card_fin, smul_apply,
    FunLike.coe_sum, Finset.sum_apply, rE, H]

end ActiveSetup.BasicFamilies.FamParams

namespace ActiveSetup.BasicFamilies.FamParams
variable {κ : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ c₀} {bf : A.BasicFamilies}
  (fp : bf.FamParams)

open Classical in
/-- Blueprint lem:variation (`eq:variation`, lines 1861-1877) on the main columns for a basic slot
and one of its basic families `j_b`: the histories act on the basic depth projection
`P_{l,j_b,h} F` (the input of the cells of depth `h`), and the certified variation of the global
ball outputs over disjoint depth intervals is bounded by
`2 (B C₁² + (1 + τ N colBudget²)) ‖F‖²`, with `B` the constant of `main_variation` and `C₁` the
one-factor compression constant of the basic tree. -/
theorem main_variation_basic (l : Fin 4) (s : List (CatCol bf.Vtx))
    (hT : ∀ e ∈ s, ∃ R ∈ residueBox (bf.vtag e.tag).dim 9, ∃ γ : ℝ,
      e = templateCol (bf.vtag e.tag) l R γ e.birth e.rank e.tag)
    (htag : ∀ e ∈ s, bf.occAvail e.tag.2.1 e.tag.1) (d : bf.Vtx) (mb : bf.MainBudget s)
    (hanc : A.AncClosed) {ι ι' : Type*} [Fintype ι] [Fintype ι'] (grp : ι → bf.Grp)
    (hgrp : Function.Injective grp) (k j : ℕ) (hPH : fp.bbase j + fp.P ≤ fp.Hmax)
    (ls : List (ℕ × Bool)) (r t : ι' → ℕ) (hrt : ∀ i, r i ≤ t i)
    (hdis : ∀ i i', i ≠ i' → Disjoint (Finset.Ioc (r i) (t i)) (Finset.Ioc (r i') (t i')))
    (htd : ∀ i, t i ≤ A.treeDepth) (Ec : ι → ι' → Finset (ℤ × ℤ))
    (hEc : ∀ G i, ∀ I ∈ Ec G i, I ∈ A.cells ∧ I.1 = A.R.1 + t i)
    (hcert : ∀ G i, ∀ I ∈ Ec G i, fp.Cert k (grp G) I)
    {ra rb : ℝ} (hroot : ∀ I ∈ A.cells, dyadicGridCell A.G I.1 I.2 ⊆ Set.Icc ra rb)
    {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hHed : Real.exp (A.Dg * (1 + Real.log A.Hsrc + Real.log τ⁻¹) ^ A.Dg) ≤ fp.Hed)
    {N : ℕ} (hN : ∀ y, ((Finset.univ : Finset (ι × (bf.Lab ⊕ Fin fp.Mc))).filter fun q =>
      ∃ I ∈ A.cells, (∃ k', fp.Cert k' (grp q.1) I) ∧
        ∃ p : Fin fp.P, y ∈ dyadicGridCell A.G I.1 I.2 ∧
        q.2 ∈ mainLabelsM A.G fp.Mc (bf.origCols l) s I (fp.brank j)
          (fp.bmask I (grp q.1) j (p + 1)) d).card ≤ N)
    (jb : Fin 2) (Z : ColumnL2 (bf.P l jb).V) :
    ∑ q : ι × ι', ‖columnL2Restriction (⋃ I ∈ Ec q.1 q.2, dyadicGridCell A.G I.1 I.2)
        (Finset.measurableSet_biUnion _ fun I _ => dyadicGridCell_measurable A.G I.1 I.2)
        (fp.gOut l s mb (grp q.1) j ls (A.R.1 + t q.2)
            (bf.famEmbR fp.Mc s l jb ((bf.P l jb).Ψ.proj (A.R.1 + t q.2) Z)) -
          fp.gOut l s mb (grp q.1) j ls (A.R.1 + r q.2)
            (bf.famEmbR fp.Mc s l jb ((bf.P l jb).Ψ.proj (A.R.1 + r q.2) Z)))‖ ^ 2 ≤
      2 * ((2 * (1 + τ * N * A.colBudget ^ 2) *
          (compressionC (bf.mainTree fp.Mc s mb) ls.length ^ 2 +
            ls.length * (∑ m ∈ Finset.range ls.length,
              compressionC (bf.mainTree fp.Mc s mb) m ^ 2))) *
          compressionC (bf.P l jb).Ψ.D 1 ^ 2 * ‖Z‖ ^ 2) +
        2 * ((1 + τ * N * A.colBudget ^ 2) * ‖Z‖ ^ 2) := by
  set Ψ := (bf.P l jb).Ψ
  have hΨG : Ψ.D.grid = A.G := (bf.P l jb).grid
  have hΨR : dyadicGridCell A.G A.R.1 A.R.2 ⊆ dyadicGridCell A.G Ψ.D.root.1 Ψ.D.root.2 := by
    have h := (bf.P l jb).root_sub
    exact h
  have hΨr : Ψ.D.root.1 ≤ A.R.1 := dyadicGridCell_depth_le_of_subset A.G A.R Ψ.D.root hΨR
  have hC : (0 : ℝ) ≤ 1 + τ * N * A.colBudget ^ 2 := by positivity
  have hBv : 0 ≤ 2 * (1 + τ * N * A.colBudget ^ 2) *
      (compressionC (bf.mainTree fp.Mc s mb) ls.length ^ 2 +
        ls.length * (∑ m ∈ Finset.range ls.length,
          compressionC (bf.mainTree fp.Mc s mb) m ^ 2)) := by
    have : 0 ≤ ∑ m ∈ Finset.range ls.length, compressionC (bf.mainTree fp.Mc s mb) m ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    positivity
  have hrows : ∀ x, ∑ q : ι × ι', ‖((columnL2Restriction (⋃ I ∈ Ec q.1 q.2,
      dyadicGridCell A.G I.1 I.2) (Finset.measurableSet_biUnion _ fun I _ =>
        dyadicGridCell_measurable A.G I.1 I.2)).comp
      (fp.gOut l s mb (grp q.1) j ls (A.R.1 + t q.2) -
        fp.gOut l s mb (grp q.1) j ls (A.R.1 + r q.2))) x‖ ^ 2 ≤
      (2 * (1 + τ * N * A.colBudget ^ 2) *
        (compressionC (bf.mainTree fp.Mc s mb) ls.length ^ 2 +
          ls.length * (∑ m ∈ Finset.range ls.length,
            compressionC (bf.mainTree fp.Mc s mb) m ^ 2))) * ‖x‖ ^ 2 := by
    intro x
    have h := fp.main_variation l s hT htag d mb hanc grp hgrp k j hPH ls r t hrt hdis Ec hEc
      hcert hroot hτ hτ1 hHed hN x
    exact le_trans (le_of_eq rfl) (h.trans (le_of_eq (by ring)))
  have hjoint : ∑ q : ι × ι', ‖((columnL2Restriction (⋃ I ∈ Ec q.1 q.2,
      dyadicGridCell A.G I.1 I.2) (Finset.measurableSet_biUnion _ fun I _ =>
        dyadicGridCell_measurable A.G I.1 I.2)))
      (fp.gOut l s mb (grp q.1) j ls (A.R.1 + t q.2) (bf.famEmbR fp.Mc s l jb
        ((Ψ.proj (A.R.1 + t q.2) - Ψ.proj (A.R.1 + r q.2)) Z)))‖ ^ 2 ≤
      (1 + τ * N * A.colBudget ^ 2) * ‖Z‖ ^ 2 := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    calc _ ≤ ∑ i : ι', (1 + τ * N * A.colBudget ^ 2) *
            ‖bf.famEmbR fp.Mc s l jb ((Ψ.proj (A.R.1 + t i) - Ψ.proj (A.R.1 + r i)) Z)‖ ^ 2 :=
          Finset.sum_le_sum fun i _ => fp.main_joint l s hT htag d mb grp hgrp k j hPH ls
            (A.R.1 + t i) (fun G => Ec G i) (fun G => hEc G i) (fun G => hcert G i) hroot hτ
            hτ1 hHed hN _
      _ ≤ ∑ i : ι', (1 + τ * N * A.colBudget ^ 2) *
            ‖(Ψ.proj (A.R.1 + t i) - Ψ.proj (A.R.1 + r i)) Z‖ ^ 2 :=
          Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (norm_nonneg _) (bf.norm_famEmbR_le fp.Mc s l jb _) 2) hC
      _ ≤ _ := by
          rw [← Finset.mul_sum]
          exact mul_le_mul_of_nonneg_left (Ψ.jumps_from_le hΨr r t hrt hdis Z) hC
  have h := emb_variation Ψ (bf.famEmbR fp.Mc s l jb) (bf.norm_famEmbR_le fp.Mc s l jb)
    (bf.famEmbR_restrict fp.Mc s l jb)
    (fun q : ι × ι' => columnL2Restriction (⋃ I ∈ Ec q.1 q.2, dyadicGridCell A.G I.1 I.2)
      (Finset.measurableSet_biUnion _ fun I _ => dyadicGridCell_measurable A.G I.1 I.2))
    (fun q h => fp.gOut l s mb (grp q.1) j ls h)
    (fun q => A.R.1 + r q.2) (fun q => A.R.1 + t q.2) hBv (fun x => hrows x)
    (fun q x => fp.gOut_rows_blk l s mb (grp q.1) j ls (by have := hrt q.2; omega)
      (by have := htd q.2; omega) (Ec q.1 q.2) (fun I hI => (hEc q.1 q.2 I hI).1) Ψ hΨG hΨR
      hΨr (by omega) x) Z hjoint
  exact h

end ActiveSetup.BasicFamilies.FamParams

section VariationLoss
variable {V W : Type*} [Fintype V] [Fintype W]

/-- The complement compression constants increase with the number of factors. -/
theorem compressionC_mono (D : ColumnTreeData V) {m n : ℕ} (hmn : m ≤ n) :
    compressionC D m ≤ compressionC D n := by
  have hL1 : 1 ≤ Real.log (2 * D.budget) := columnBudget_log_one_le D
  obtain ⟨L, hLe⟩ : ∃ L : ℝ, L = Real.log (2 * D.budget) := ⟨_, rfl⟩
  have hm1 : (1 : ℝ) ≤ (m : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) m; linarith
  have hmn0 : (m : ℝ) ≤ n := by exact_mod_cast hmn
  have hmn' : (m : ℝ) + 1 ≤ (n : ℝ) + 1 := by linarith
  obtain ⟨tm, tn, htm1, htmn, hCm, hCn⟩ : ∃ tm tn : ℝ, 1 ≤ tm ∧ tm ≤ tn ∧
      compressionC D m = (1024 * tm * L) ^ (1024 * (m + 1)) ∧
      compressionC D n = (1024 * tn * L) ^ (1024 * (n + 1)) :=
    ⟨_, _, one_le_pow₀ hm1, pow_le_pow_left₀ (by linarith) hmn' _, by rw [hLe]; rfl,
      by rw [hLe]; rfl⟩
  rw [← hLe] at hL1
  rw [hCm, hCn]
  have hb1 : (1 : ℝ) ≤ 1024 * tm * L := by nlinarith
  have hbb : 1024 * tm * L ≤ 1024 * tn * L := by nlinarith
  calc (1024 * tm * L) ^ (1024 * (m + 1)) ≤ (1024 * tn * L) ^ (1024 * (m + 1)) :=
        pow_le_pow_left₀ (by linarith) hbb _
    _ ≤ (1024 * tn * L) ^ (1024 * (n + 1)) :=
        pow_le_pow_right₀ (hb1.trans hbb) (by omega)

/-- `compression_loss_le` with the basic projection inserted as a one-layer history. -/
theorem compression_loss_le' (D : ColumnTreeData V) (D' : ColumnTreeData W)
    (n c : ℕ) (hc : 1 ≤ c) {k : ℝ} (hk : 1 ≤ k) (hD : Real.log (2 * D.budget) ≤ k ^ c)
    (hD' : Real.log (2 * D'.budget) ≤ k ^ c) (hn : (n : ℝ) ≤ c * (Real.log k + 1)) :
    compressionC D n ^ 2 * compressionC D' 1 ^ 2 ≤
      Real.exp (4096 * (c + 1) * (1024 * (c + 1) + c + 7) * (1 + Real.log (2 * k)) ^ 2) := by
  have h1 := compressionC_le_overhead D n c hk hD hn
  have hn1 : ((1 : ℕ) : ℝ) ≤ c * (Real.log k + 1) := by
    have := Real.log_nonneg hk
    have hc' : (1 : ℝ) ≤ c := by exact_mod_cast hc
    push_cast; nlinarith
  have h2 := compressionC_le_overhead D' 1 c hk hD' hn1
  have h0 := compressionC_nonneg D n
  have h0' := compressionC_nonneg D' 1
  obtain ⟨K, hKe⟩ : ∃ K : ℝ, K = 1024 * (c + 1) * (1024 * (c + 1) + c + 7) *
      (1 + Real.log (2 * k)) ^ 2 := ⟨_, rfl⟩
  rw [← hKe] at h1 h2
  have h3 : compressionC D n ^ 2 * compressionC D' 1 ^ 2 ≤
      Real.exp K ^ 2 * Real.exp K ^ 2 :=
    mul_le_mul (pow_le_pow_left₀ h0 h1 2) (pow_le_pow_left₀ h0' h2 2) (sq_nonneg _) (sq_nonneg _)
  refine h3.trans (le_of_eq ?_)
  rw [← pow_add, ← Real.exp_nat_mul, hKe]
  congr 1
  push_cast
  ring

/-- Blueprint lem:variation, "the compression loss is `G₀`" (lines 1859, 1877: "the `O(log L)`
terms, signed expansions and averages are absorbed in `G₀`"): the constant of
`main_variation_basic` for histories of length `n ≤ c (log k + 1)`, column budgets with
`log (2 budget) ≤ k^c` and a whole-range constant at most `2` is at most
`G₀ = exp(C_q (1 + log 2k)^2)`, `C_q = 4096 (c+1) (1024 (c+1) + c + 7) + c² + 3`. -/
theorem variation_loss_le (D : ColumnTreeData V) (D' : ColumnTreeData W) (n c : ℕ) (hc : 1 ≤ c)
    {k : ℝ} (hk : 1 ≤ k) (hD : Real.log (2 * D.budget) ≤ k ^ c)
    (hD' : Real.log (2 * D'.budget) ≤ k ^ c) (hn : (n : ℝ) ≤ c * (Real.log k + 1)) {Cw : ℝ}
    (hCw : Cw ≤ 2) :
    2 * ((2 * Cw * (compressionC D n ^ 2 + n * (∑ m ∈ Finset.range n, compressionC D m ^ 2))) *
        compressionC D' 1 ^ 2) + 2 * Cw ≤
      Real.exp ((4096 * (c + 1) * (1024 * (c + 1) + c + 7) + c ^ 2 + 3) *
        (1 + Real.log (2 * k)) ^ 2) := by
  have hloss := compression_loss_le' D D' n c hc hk hD hD' hn
  obtain ⟨X, hXe⟩ : ∃ X : ℝ, X = 1 + Real.log (2 * k) := ⟨_, rfl⟩
  obtain ⟨K, hKe⟩ : ∃ K : ℝ, K = 4096 * (c + 1) * (1024 * (c + 1) + c + 7) := ⟨_, rfl⟩
  rw [← hXe, ← hKe] at hloss
  rw [← hXe, ← hKe]
  have hlogk : 0 ≤ Real.log k := Real.log_nonneg hk
  have hlog2k : Real.log (2 * k) = Real.log 2 + Real.log k :=
    Real.log_mul (by norm_num) (by linarith)
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hX1 : 1 ≤ X := by rw [hXe, hlog2k]; linarith
  have hkX : Real.log k + 1 ≤ X := by rw [hXe, hlog2k]; linarith
  have hnX : (n : ℝ) ≤ c * X := hn.trans (mul_le_mul_of_nonneg_left hkX (Nat.cast_nonneg c))
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  obtain ⟨Cn, hCne⟩ : ∃ Cn : ℝ, Cn = compressionC D n := ⟨_, rfl⟩
  obtain ⟨C1, hC1e⟩ : ∃ C1 : ℝ, C1 = compressionC D' 1 := ⟨_, rfl⟩
  have hCn0 : 0 ≤ Cn := hCne ▸ compressionC_nonneg D n
  have hC10 : 0 ≤ C1 := hC1e ▸ compressionC_nonneg D' 1
  have hsum : ∑ m ∈ Finset.range n, compressionC D m ^ 2 ≤ n * Cn ^ 2 := by
    calc ∑ m ∈ Finset.range n, compressionC D m ^ 2 ≤ ∑ _m ∈ Finset.range n, Cn ^ 2 :=
          Finset.sum_le_sum fun m hm => by
            rw [hCne]
            exact pow_le_pow_left₀ (compressionC_nonneg D m)
              (compressionC_mono D (Finset.mem_range.mp hm).le) 2
      _ = n * Cn ^ 2 := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [← hCne, ← hC1e] at hloss ⊢
  set S := ∑ m ∈ Finset.range n, compressionC D m ^ 2
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hE1 : 1 ≤ Real.exp (K * X ^ 2) := Real.one_le_exp (by
    rw [hKe]; positivity)
  -- the inner constant
  have h1 : 2 * ((2 * Cw * (Cn ^ 2 + n * S)) * C1 ^ 2) + 2 * Cw ≤
      8 * (1 + (n : ℝ) ^ 2) * Real.exp (K * X ^ 2) + 4 := by
    have hA : Cn ^ 2 + n * S ≤ (1 + (n : ℝ) ^ 2) * Cn ^ 2 := by
      have := mul_le_mul_of_nonneg_left hsum hn0
      nlinarith only [hsum]
    have hB : (Cn ^ 2 + n * S) * C1 ^ 2 ≤ (1 + (n : ℝ) ^ 2) * Real.exp (K * X ^ 2) := by
      calc (Cn ^ 2 + n * S) * C1 ^ 2 ≤ ((1 + (n : ℝ) ^ 2) * Cn ^ 2) * C1 ^ 2 :=
            mul_le_mul_of_nonneg_right hA (sq_nonneg _)
        _ = (1 + (n : ℝ) ^ 2) * (Cn ^ 2 * C1 ^ 2) := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hloss (by positivity)
    have hP0 : 0 ≤ (Cn ^ 2 + n * S) * C1 ^ 2 :=
      mul_nonneg (add_nonneg (sq_nonneg _) (mul_nonneg hn0 hS0)) (sq_nonneg _)
    nlinarith only [hCw, hloss, hA, hP0]
  refine h1.trans ?_
  -- absorbing `1 + n²` and the numerical factors
  have hn2 : 1 + (n : ℝ) ^ 2 ≤ Real.exp ((c : ℝ) ^ 2 * X ^ 2) := by
    have h := Real.add_one_le_exp ((n : ℝ) ^ 2)
    have : (n : ℝ) ^ 2 ≤ (c : ℝ) ^ 2 * X ^ 2 := by
      have := pow_le_pow_left₀ hn0 hnX 2
      nlinarith only [hnX]
    linarith [Real.exp_le_exp.mpr this]
  have h12 : (12 : ℝ) ≤ Real.exp (3 * X ^ 2) := by
    have h3 : Real.exp 3 ≤ Real.exp (3 * X ^ 2) := Real.exp_le_exp.mpr (by nlinarith only [hX1])
    have he := Real.exp_one_gt_d9
    have : Real.exp 3 = Real.exp 1 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
    have h12' : (12 : ℝ) ≤ Real.exp 3 := by rw [this]; nlinarith only [sq_nonneg (Real.exp 1), he]
    linarith
  have hprod : Real.exp (3 * X ^ 2) * Real.exp ((c : ℝ) ^ 2 * X ^ 2) * Real.exp (K * X ^ 2) =
      Real.exp ((K + c ^ 2 + 3) * X ^ 2) := by
    rw [← Real.exp_add, ← Real.exp_add]; ring_nf
  have hE0 := Real.exp_pos (K * X ^ 2)
  calc 8 * (1 + (n : ℝ) ^ 2) * Real.exp (K * X ^ 2) + 4 ≤
      12 * (1 + (n : ℝ) ^ 2) * Real.exp (K * X ^ 2) := by nlinarith only [hE1]
    _ ≤ Real.exp (3 * X ^ 2) * Real.exp ((c : ℝ) ^ 2 * X ^ 2) * Real.exp (K * X ^ 2) := by
        gcongr
    _ = _ := hprod

end VariationLoss

namespace ActiveSetup.BasicFamilies.FamParams
variable {κ : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ c₀} {bf : A.BasicFamilies}
  (fp : bf.FamParams)

/-- The global coarse output of a basic slot (blueprint eq:localized, lines 1841, 1859): the
global ball output of the group at the depth `h` acting on the global basic input, in the main
column space. Its restriction to an active cell of depth `h` is the leaf output
(`basic_leaf_out`). -/
noncomputable def basicOut (l : Fin 4) (s : List (CatCol bf.Vtx)) (mb : bf.MainBudget s)
    (G : bf.Grp) (j : ℕ) (ls : List (ℕ × Bool)) (h : ℤ) : ColumnL2 (bf.Lab ⊕ Fin fp.Mc) :=
  colRelabel (bf.rv fp.Mc s) (fp.gOut l s mb G j ls h
    (ContinuousLinearMap.adjoint (colRelabel (bf.rv fp.Mc s)) (bf.gBasic fp.Mc l h)))

theorem basicOut_eq (l : Fin 4) (s : List (CatCol bf.Vtx)) (mb : bf.MainBudget s)
    (G : bf.Grp) (j : ℕ) (ls : List (ℕ × Bool)) (h : ℤ) :
    fp.basicOut l s mb G j ls h = colRelabel (bf.rv fp.Mc s)
      (fp.gOut l s mb G j ls h (bf.famEmbR fp.Mc s l 0 ((bf.P l 0).Ψ.proj h (bf.P l 0).Z)) -
        fp.gOut l s mb G j ls h (bf.famEmbR fp.Mc s l 1 ((bf.P l 1).Ψ.proj h (bf.P l 1).Z))) := by
  unfold basicOut ActiveSetup.BasicFamilies.gBasic ActiveSetup.BasicFamilies.famEmbR
  rw [map_sub, map_sub]
  rfl

/-- The restriction of the basic coarse output to an active cell of its depth is the leaf output
`L_{l,G,s} B_{l,s} B_l` of the cell (blueprint eq:localized and line 1859). -/
theorem basicOut_restrict (l : Fin 4) (s : List (CatCol bf.Vtx)) (mb : bf.MainBudget s)
    (G : bf.Grp) (j : ℕ) (ls : List (ℕ × Bool)) {I : ℤ × ℤ} (hI : I ∈ A.cells) :
    columnL2Restriction (dyadicGridCell A.G I.1 I.2) (dyadicGridCell_measurable A.G I.1 I.2)
        (fp.basicOut l s mb G j ls I.1) =
      fp.ballFilt l s I G j (layerOp (fun m => fp.cumFilt l s I m) ls (bf.basicIn fp.Mc l I)) :=
  (fp.basic_leaf_out l s mb ls G j hI).symm

end ActiveSetup.BasicFamilies.FamParams

namespace ActiveSetup.BasicFamilies.FamParams
variable {κ : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ c₀} {bf : A.BasicFamilies}
  (fp : bf.FamParams)

/-- The basic families reach the depth of the attempt root. -/
theorem famN_ge (hne : A.cells.Nonempty) (l : Fin 4) (jb : Fin 2) :
    A.R.1 ≤ (bf.P l jb).Ψ.N := by
  obtain ⟨c, hc⟩ := hne
  obtain ⟨-, hcN, -⟩ := bf.charts l jb c hc
  have := dyadicGridCell_depth_le_of_subset A.G c A.R (A.sub c hc)
  omega

/-- On unions of active cells, the global ball outputs of a basic family depend only on the
restriction of the family input to the attempt root (blueprint line 1865: `‖1_R F‖`). -/
theorem out_restrictR (hne : A.cells.Nonempty) (l : Fin 4) (s : List (CatCol bf.Vtx))
    (mb : bf.MainBudget s) (G : bf.Grp) (j : ℕ) (ls : List (ℕ × Bool)) (jb : Fin 2) {h : ℤ}
    (hRh : A.R.1 ≤ h) (E : Finset (ℤ × ℤ)) (hE : ∀ I ∈ E, I ∈ A.cells)
    (Z : ColumnL2 (bf.P l jb).V) :
    columnL2Restriction (⋃ I ∈ E, dyadicGridCell A.G I.1 I.2)
        (Finset.measurableSet_biUnion _ fun I _ => dyadicGridCell_measurable A.G I.1 I.2)
        (fp.gOut l s mb G j ls h (bf.famEmbR fp.Mc s l jb ((bf.P l jb).Ψ.proj h Z))) =
      columnL2Restriction (⋃ I ∈ E, dyadicGridCell A.G I.1 I.2)
        (Finset.measurableSet_biUnion _ fun I _ => dyadicGridCell_measurable A.G I.1 I.2)
        (fp.gOut l s mb G j ls h (bf.famEmbR fp.Mc s l jb ((bf.P l jb).Ψ.proj h
          (columnL2Restriction (dyadicGridCell A.G A.R.1 A.R.2)
            (dyadicGridCell_measurable A.G A.R.1 A.R.2) Z)))) := by
  set Ψ := (bf.P l jb).Ψ
  have hΨG : Ψ.D.grid = A.G := (bf.P l jb).grid
  have hΨR : dyadicGridCell A.G A.R.1 A.R.2 ⊆ dyadicGridCell A.G Ψ.D.root.1 Ψ.D.root.2 :=
    (bf.P l jb).root_sub
  have hΨr : Ψ.D.root.1 ≤ A.R.1 := dyadicGridCell_depth_le_of_subset A.G A.R Ψ.D.root hΨR
  have hN := famN_ge (bf := bf) hne l jb
  set! rR := columnL2Restriction (V := bf.RLab fp.Mc s) (dyadicGridCell A.G A.R.1 A.R.2)
    (dyadicGridCell_measurable A.G A.R.1 A.R.2)
  set rE := columnL2Restriction (V := bf.RLab fp.Mc s) (⋃ I ∈ E, dyadicGridCell A.G I.1 I.2)
    (Finset.measurableSet_biUnion _ fun I _ => dyadicGridCell_measurable A.G I.1 I.2)
  -- the basic projection commutes with the restriction to the root
  have h1 : Ψ.proj h (columnL2Restriction (dyadicGridCell A.G A.R.1 A.R.2)
      (dyadicGridCell_measurable A.G A.R.1 A.R.2) Z) =
      columnL2Restriction (dyadicGridCell A.G A.R.1 A.R.2)
        (dyadicGridCell_measurable A.G A.R.1 A.R.2) (Ψ.proj h Z) := by
    have hd : A.R.1 ≤ Ψ.depth h := by
      unfold ColumnDepthFamily.depth
      exact le_trans (le_min hRh hN) (le_max_right _ _)
    have h' := Ψ.proj_commute_restrict h (Q := A.R) hd
    rw [hΨG] at h'
    exact (DFunLike.congr_fun h' Z).symm
  -- the ball output commutes with the restriction to the root
  have h2 : (fp.gOut l s mb G j ls h).comp rR = rR.comp (fp.gOut l s mb G j ls h) :=
    (fp.gOut_commute l s mb G j ls h (Q := A.R) (by
      change A.R.1 ≤ max A.R.1 (min h (A.R.1 + A.treeDepth)); exact le_max_left _ _)).symm
  have h3 : rE.comp rR = rE := by
    refine columnL2Restriction_comp_of_subset _ _ ?_
    intro y hy
    obtain ⟨I, hI, hyI⟩ := Set.mem_iUnion₂.mp hy
    exact A.sub I (hE I hI) hyI
  rw [h1, bf.famEmbR_restrict]
  change rE _ = rE (fp.gOut l s mb G j ls h (rR _))
  rw [← ContinuousLinearMap.comp_apply (fp.gOut l s mb G j ls h) rR, h2,
    ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.comp_apply rE rR, h3]

open Classical in
/-- Blueprint lem:variation (`eq:variation`, lines 1861-1877) on the main columns for a basic
coarse output: for depth intervals `[r_i, t_i]` (offsets below the attempt root) that are
disjoint, and unions `E_{G,i}` of active cells of depth `t_i` carrying downstream actual-use
certificates of `G`,
`Σ_{G,i} ‖1_E (Z_{G,t_i} - Z_{G,r_i})‖² ≤ Σ_{j_b} 2 V_{j_b} ‖1_R F_{l,j_b}‖²`, where
`Z_{G,h} = L_{G,h} B'_h B_l` is the global coarse output (`basicOut`) and
`V_{j_b} = 2 (2 C_w S) C_{1,j_b}² + 2 C_w` with the whole-range constant
`C_w = 1 + τ N colBudget²`, the history compression sum `S` and the one-factor compression
constant `C_{1,j_b}` of the basic tree. -/
theorem basic_variation (l : Fin 4) (s : List (CatCol bf.Vtx))
    (hT : ∀ e ∈ s, ∃ R ∈ residueBox (bf.vtag e.tag).dim 9, ∃ γ : ℝ,
      e = templateCol (bf.vtag e.tag) l R γ e.birth e.rank e.tag)
    (htag : ∀ e ∈ s, bf.occAvail e.tag.2.1 e.tag.1) (d : bf.Vtx) (mb : bf.MainBudget s)
    (hanc : A.AncClosed) (hne : A.cells.Nonempty) {ι ι' : Type*} [Fintype ι] [Fintype ι']
    (grp : ι → bf.Grp) (hgrp : Function.Injective grp) (k j : ℕ)
    (hPH : fp.bbase j + fp.P ≤ fp.Hmax) (ls : List (ℕ × Bool)) (r t : ι' → ℕ)
    (hrt : ∀ i, r i ≤ t i)
    (hdis : ∀ i i', i ≠ i' → Disjoint (Finset.Ioc (r i) (t i)) (Finset.Ioc (r i') (t i')))
    (htd : ∀ i, t i ≤ A.treeDepth) (Ec : ι → ι' → Finset (ℤ × ℤ))
    (hEc : ∀ G i, ∀ I ∈ Ec G i, I ∈ A.cells ∧ I.1 = A.R.1 + t i)
    (hcert : ∀ G i, ∀ I ∈ Ec G i, fp.Cert k (grp G) I)
    {ra rb : ℝ} (hroot : ∀ I ∈ A.cells, dyadicGridCell A.G I.1 I.2 ⊆ Set.Icc ra rb)
    {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hHed : Real.exp (A.Dg * (1 + Real.log A.Hsrc + Real.log τ⁻¹) ^ A.Dg) ≤ fp.Hed)
    {N : ℕ} (hN : ∀ y, ((Finset.univ : Finset (ι × (bf.Lab ⊕ Fin fp.Mc))).filter fun q =>
      ∃ I ∈ A.cells, (∃ k', fp.Cert k' (grp q.1) I) ∧
        ∃ p : Fin fp.P, y ∈ dyadicGridCell A.G I.1 I.2 ∧
        q.2 ∈ mainLabelsM A.G fp.Mc (bf.origCols l) s I (fp.brank j)
          (fp.bmask I (grp q.1) j (p + 1)) d).card ≤ N) :
    ∑ q : ι × ι', ‖columnL2Restriction (⋃ I ∈ Ec q.1 q.2, dyadicGridCell A.G I.1 I.2)
        (Finset.measurableSet_biUnion _ fun I _ => dyadicGridCell_measurable A.G I.1 I.2)
        (fp.basicOut l s mb (grp q.1) j ls (A.R.1 + t q.2) -
          fp.basicOut l s mb (grp q.1) j ls (A.R.1 + r q.2))‖ ^ 2 ≤
      ∑ jb : Fin 2, 2 * (2 * ((2 * (1 + τ * N * A.colBudget ^ 2) *
          (compressionC (bf.mainTree fp.Mc s mb) ls.length ^ 2 +
            ls.length * (∑ m ∈ Finset.range ls.length,
              compressionC (bf.mainTree fp.Mc s mb) m ^ 2))) *
          compressionC (bf.P l jb).Ψ.D 1 ^ 2) + 2 * (1 + τ * N * A.colBudget ^ 2)) *
        ‖columnL2Restriction (dyadicGridCell A.G A.R.1 A.R.2)
          (dyadicGridCell_measurable A.G A.R.1 A.R.2) (bf.P l jb).Z‖ ^ 2 := by
  set! rR := fun jb : Fin 2 => columnL2Restriction (V := (bf.P l jb).V)
    (dyadicGridCell A.G A.R.1 A.R.2) (dyadicGridCell_measurable A.G A.R.1 A.R.2)
  set! X : Fin 2 → ι × ι' → ℤ → ColumnL2 (bf.RLab fp.Mc s) := fun jb q h =>
    fp.gOut l s mb (grp q.1) j ls h (bf.famEmbR fp.Mc s l jb ((bf.P l jb).Ψ.proj h
      (rR jb (bf.P l jb).Z)))
  set! rE : ι × ι' → ColumnL2 (bf.RLab fp.Mc s) →L[ℂ] ColumnL2 (bf.RLab fp.Mc s) := fun q =>
    columnL2Restriction (⋃ I ∈ Ec q.1 q.2, dyadicGridCell A.G I.1 I.2)
      (Finset.measurableSet_biUnion _ fun I _ => dyadicGridCell_measurable A.G I.1 I.2)
  -- the outputs of the two families on the certified cells
  have hsplit : ∀ q : ι × ι', ‖columnL2Restriction (⋃ I ∈ Ec q.1 q.2, dyadicGridCell A.G I.1 I.2)
      (Finset.measurableSet_biUnion _ fun I _ => dyadicGridCell_measurable A.G I.1 I.2)
      (fp.basicOut l s mb (grp q.1) j ls (A.R.1 + t q.2) -
        fp.basicOut l s mb (grp q.1) j ls (A.R.1 + r q.2))‖ =
      ‖rE q (X 0 q (A.R.1 + t q.2) - X 0 q (A.R.1 + r q.2)) -
        rE q (X 1 q (A.R.1 + t q.2) - X 1 q (A.R.1 + r q.2))‖ := by
    intro q
    rw [fp.basicOut_eq, fp.basicOut_eq, ← map_sub, ← colRelabel_restrict,
      norm_colRelabel (bf.rv_injective fp.Mc s)]
    have hEc' : ∀ I ∈ Ec q.1 q.2, I ∈ A.cells := fun I hI => (hEc q.1 q.2 I hI).1
    have e : ∀ (jb : Fin 2) (h : ℤ), A.R.1 ≤ h → rE q (fp.gOut l s mb (grp q.1) j ls h
        (bf.famEmbR fp.Mc s l jb ((bf.P l jb).Ψ.proj h (bf.P l jb).Z))) = rE q (X jb q h) :=
      fun jb h hh => fp.out_restrictR hne l s mb (grp q.1) j ls jb hh (Ec q.1 q.2) hEc' _
    simp only [map_sub]
    rw [e 0 _ (by omega), e 1 _ (by omega), e 0 _ (by omega), e 1 _ (by omega)]
    congr 1
    exact sub_sub_sub_comm _ _ _ _
  have hfam : ∀ jb : Fin 2, ∑ q : ι × ι', ‖rE q (X jb q (A.R.1 + t q.2) -
      X jb q (A.R.1 + r q.2))‖ ^ 2 ≤ (2 * ((2 * (1 + τ * N * A.colBudget ^ 2) *
          (compressionC (bf.mainTree fp.Mc s mb) ls.length ^ 2 +
            ls.length * (∑ m ∈ Finset.range ls.length,
              compressionC (bf.mainTree fp.Mc s mb) m ^ 2))) *
          compressionC (bf.P l jb).Ψ.D 1 ^ 2) + 2 * (1 + τ * N * A.colBudget ^ 2)) *
        ‖rR jb (bf.P l jb).Z‖ ^ 2 := by
    intro jb
    have h := fp.main_variation_basic l s hT htag d mb hanc grp hgrp k j hPH ls r t hrt hdis htd
      Ec hEc hcert hroot hτ hτ1 hHed hN jb (rR jb (bf.P l jb).Z)
    exact h.trans (le_of_eq (by ring))
  calc ∑ q : ι × ι', ‖columnL2Restriction (⋃ I ∈ Ec q.1 q.2, dyadicGridCell A.G I.1 I.2)
        (Finset.measurableSet_biUnion _ fun I _ => dyadicGridCell_measurable A.G I.1 I.2)
        (fp.basicOut l s mb (grp q.1) j ls (A.R.1 + t q.2) -
          fp.basicOut l s mb (grp q.1) j ls (A.R.1 + r q.2))‖ ^ 2
      ≤ ∑ q : ι × ι', (2 * ‖rE q (X 0 q (A.R.1 + t q.2) - X 0 q (A.R.1 + r q.2))‖ ^ 2 +
          2 * ‖rE q (X 1 q (A.R.1 + t q.2) - X 1 q (A.R.1 + r q.2))‖ ^ 2) := by
        refine Finset.sum_le_sum fun q _ => ?_
        rw [hsplit q]
        set a := rE q (X 0 q (A.R.1 + t q.2) - X 0 q (A.R.1 + r q.2))
        set b := rE q (X 1 q (A.R.1 + t q.2) - X 1 q (A.R.1 + r q.2))
        calc ‖a - b‖ ^ 2 ≤ (‖a‖ + ‖b‖) ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le a b) 2
          _ ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by nlinarith [sq_nonneg (‖a‖ - ‖b‖)]
    _ = 2 * ∑ q : ι × ι', ‖rE q (X 0 q (A.R.1 + t q.2) - X 0 q (A.R.1 + r q.2))‖ ^ 2 +
          2 * ∑ q : ι × ι', ‖rE q (X 1 q (A.R.1 + t q.2) - X 1 q (A.R.1 + r q.2))‖ ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ _ := by
        rw [Fin.sum_univ_two]
        have h0 := hfam 0
        have h1 := hfam 1
        nlinarith only [h0, h1]

end ActiveSetup.BasicFamilies.FamParams

/-- Sums over a finite family colored with `M` colors are at most `M` times a bound valid on every
color class (blueprint line 1877: "color the depth intervals to handle bounded overlap"). -/
theorem sum_le_of_coloring {ι' : Type*} [Fintype ι'] {M : ℕ} (col : ι' → Fin M) (f : ι' → ℝ)
    {B : ℝ} (hB : ∀ c, ∑ i ∈ Finset.univ.filter (fun i => col i = c), f i ≤ B) :
    ∑ i, f i ≤ M * B := by
  rw [← Finset.sum_fiberwise (Finset.univ : Finset ι') col f]
  calc ∑ c, ∑ i ∈ Finset.univ.filter (fun i => col i = c), f i ≤ ∑ _c : Fin M, B :=
        Finset.sum_le_sum fun c _ => hB c
    _ = M * B := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

namespace ActiveSetup.BasicFamilies.FamParams
variable {κ : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ c₀} {bf : A.BasicFamilies}
  (fp : bf.FamParams)

/-- The global shared histories commute with the restriction to every dyadic cell of depth at most
the clamped depth. -/
theorem gHist_commute (l : Fin 4) (s : List (CatCol bf.Vtx)) (mb : bf.MainBudget s)
    (ls : List (ℕ × Bool)) (h : ℤ) {Q : ℤ × ℤ} (hQ : Q.1 ≤ (bf.mainBase fp.Mc s mb).depth h) :
    (columnL2Restriction (dyadicGridCell A.G Q.1 Q.2)
      (dyadicGridCell_measurable A.G Q.1 Q.2)).comp (fp.gHist l s mb ls h) =
    (fp.gHist l s mb ls h).comp (columnL2Restriction (dyadicGridCell A.G Q.1 Q.2)
      (dyadicGridCell_measurable A.G Q.1 Q.2)) := by
  set rQ := columnL2Restriction (V := bf.RLab fp.Mc s) (dyadicGridCell A.G Q.1 Q.2)
    (dyadicGridCell_measurable A.G Q.1 Q.2)
  have hcum : ∀ m, (opAvg fun p : Fin fp.P =>
      ((bf.mainBase fp.Mc s mb).withMask (fp.cumMaskT l s mb m p)).proj h).comp rQ =
      rQ.comp (opAvg fun p : Fin fp.P =>
        ((bf.mainBase fp.Mc s mb).withMask (fp.cumMaskT l s mb m p)).proj h) := fun m =>
    opAvg_commute _ _ fun p =>
      (((bf.mainBase fp.Mc s mb).withMask (fp.cumMaskT l s mb m p)).proj_commute_restrict h
        hQ).symm
  exact (layerOp_commute _ rQ hcum ls).symm

/-- The restricted jump rows of the global shared histories split orthogonally over the depth
partition of a basic family at the left depth. -/
theorem gHist_rows_blk (l : Fin 4) (s : List (CatCol bf.Vtx)) (mb : bf.MainBudget s)
    (ls : List (ℕ × Bool)) {hr ht : ℤ} (hrt : hr ≤ ht)
    (htd : ht ≤ A.R.1 + A.treeDepth) (E : Finset (ℤ × ℤ)) (hE : ∀ I ∈ E, I ∈ A.cells)
    {V : Type*} [Fintype V] (Ψ : ColumnDepthFamily V) (hΨG : Ψ.D.grid = A.G)
    (hΨR : dyadicGridCell A.G A.R.1 A.R.2 ⊆ dyadicGridCell A.G Ψ.D.root.1 Ψ.D.root.2)
    (hΨr : Ψ.D.root.1 ≤ A.R.1) (hRr : A.R.1 ≤ hr) (x : ColumnL2 (bf.RLab fp.Mc s)) :
    ‖((columnL2Restriction (⋃ I ∈ E, dyadicGridCell A.G I.1 I.2)
        (Finset.measurableSet_biUnion _ fun I _ => dyadicGridCell_measurable A.G I.1 I.2)).comp
        (fp.gHist l s mb ls ht - fp.gHist l s mb ls hr)) x‖ ^ 2 =
      ∑ Q : {Q // Q ∈ (Ψ.partition hr).cells},
        ‖((columnL2Restriction (⋃ I ∈ E, dyadicGridCell A.G I.1 I.2)
          (Finset.measurableSet_biUnion _ fun I _ => dyadicGridCell_measurable A.G I.1 I.2)).comp
          (fp.gHist l s mb ls ht - fp.gHist l s mb ls hr))
          (columnL2Restriction (dyadicGridCell Ψ.D.grid Q.1.1 Q.1.2)
            (dyadicGridCell_measurable Ψ.D.grid Q.1.1 Q.1.2) x)‖ ^ 2 := by
  have hEm : MeasurableSet (⋃ I ∈ E, dyadicGridCell A.G I.1 I.2) :=
    Finset.measurableSet_biUnion _ fun I _ => dyadicGridCell_measurable A.G I.1 I.2
  have hdepth : ∀ Q ∈ (Ψ.partition hr).cells, ∀ h : ℤ, hr ≤ h → h ≤ ht →
      Q.1 ≤ (bf.mainBase fp.Mc s mb).depth h := by
    intro Q hQ h h1 h2
    have hQ1 := ((Ψ.mem_partition _ Q).mp hQ).1
    have hle : Ψ.depth hr ≤ hr := by
      unfold ColumnDepthFamily.depth
      exact max_le (by omega) (min_le_left _ _)
    change Q.1 ≤ max A.R.1 (min h (A.R.1 + A.treeDepth))
    rw [hQ1]
    exact le_trans hle (le_trans (le_min h1 (by omega)) (le_max_right _ _))
  refine Ψ.blk_of_commute hr _ (fun y => ?_) (fun Q hQ => ?_) x
  · filter_upwards [columnL2Restriction_vanish _ hEm
      ((fp.gHist l s mb ls ht - fp.gHist l s mb ls hr) y)] with z hz hzR
    refine hz fun hzE => hzR ?_
    rw [Set.mem_iUnion₂] at hzE
    obtain ⟨I, hI, hzI⟩ := hzE
    rw [hΨG]
    exact hΨR (A.sub I (hE I hI) hzI)
  · have h1 := fp.gHist_commute l s mb ls ht (Q := Q) (hdepth Q hQ ht hrt le_rfl)
    have h2 := fp.gHist_commute l s mb ls hr (Q := Q) (hdepth Q hQ hr le_rfl hrt)
    have hc := columnL2Restriction_comm (V := bf.RLab fp.Mc s) hEm
      (dyadicGridCell_measurable A.G Q.1 Q.2)
    rw [hΨG, ContinuousLinearMap.comp_assoc, ContinuousLinearMap.sub_comp, ← h1, ← h2,
      ← ContinuousLinearMap.comp_sub,
      ← ContinuousLinearMap.comp_assoc, ← ContinuousLinearMap.comp_assoc, hc]

/-- On unions of active cells, the global shared histories of a basic family depend only on the
restriction of the family input to the attempt root. -/
theorem hist_restrictR (hne : A.cells.Nonempty) (l : Fin 4) (s : List (CatCol bf.Vtx))
    (mb : bf.MainBudget s) (ls : List (ℕ × Bool)) (jb : Fin 2) {h : ℤ}
    (hRh : A.R.1 ≤ h) (E : Finset (ℤ × ℤ)) (hE : ∀ I ∈ E, I ∈ A.cells)
    (Z : ColumnL2 (bf.P l jb).V) :
    columnL2Restriction (⋃ I ∈ E, dyadicGridCell A.G I.1 I.2)
        (Finset.measurableSet_biUnion _ fun I _ => dyadicGridCell_measurable A.G I.1 I.2)
        (fp.gHist l s mb ls h (bf.famEmbR fp.Mc s l jb ((bf.P l jb).Ψ.proj h Z))) =
      columnL2Restriction (⋃ I ∈ E, dyadicGridCell A.G I.1 I.2)
        (Finset.measurableSet_biUnion _ fun I _ => dyadicGridCell_measurable A.G I.1 I.2)
        (fp.gHist l s mb ls h (bf.famEmbR fp.Mc s l jb ((bf.P l jb).Ψ.proj h
          (columnL2Restriction (dyadicGridCell A.G A.R.1 A.R.2)
            (dyadicGridCell_measurable A.G A.R.1 A.R.2) Z)))) := by
  set Ψ := (bf.P l jb).Ψ
  have hΨG : Ψ.D.grid = A.G := (bf.P l jb).grid
  have hN := famN_ge (bf := bf) hne l jb
  set! rR := columnL2Restriction (V := bf.RLab fp.Mc s) (dyadicGridCell A.G A.R.1 A.R.2)
    (dyadicGridCell_measurable A.G A.R.1 A.R.2)
  set rE := columnL2Restriction (V := bf.RLab fp.Mc s) (⋃ I ∈ E, dyadicGridCell A.G I.1 I.2)
    (Finset.measurableSet_biUnion _ fun I _ => dyadicGridCell_measurable A.G I.1 I.2)
  have h1 : Ψ.proj h (columnL2Restriction (dyadicGridCell A.G A.R.1 A.R.2)
      (dyadicGridCell_measurable A.G A.R.1 A.R.2) Z) =
      columnL2Restriction (dyadicGridCell A.G A.R.1 A.R.2)
        (dyadicGridCell_measurable A.G A.R.1 A.R.2) (Ψ.proj h Z) := by
    have hd : A.R.1 ≤ Ψ.depth h := by
      unfold ColumnDepthFamily.depth
      exact le_trans (le_min hRh hN) (le_max_right _ _)
    have h' := Ψ.proj_commute_restrict h (Q := A.R) hd
    rw [hΨG] at h'
    exact (DFunLike.congr_fun h' Z).symm
  have h2 : (fp.gHist l s mb ls h).comp rR = rR.comp (fp.gHist l s mb ls h) :=
    (fp.gHist_commute l s mb ls h (Q := A.R) (by
      change A.R.1 ≤ max A.R.1 (min h (A.R.1 + A.treeDepth)); exact le_max_left _ _)).symm
  have h3 : rE.comp rR = rE := by
    refine columnL2Restriction_comp_of_subset _ _ ?_
    intro y hy
    obtain ⟨I, hI, hyI⟩ := Set.mem_iUnion₂.mp hy
    exact A.sub I (hE I hI) hyI
  rw [h1, bf.famEmbR_restrict]
  change rE _ = rE (fp.gHist l s mb ls h (rR _))
  rw [← ContinuousLinearMap.comp_apply (fp.gHist l s mb ls h) rR, h2,
    ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.comp_apply rE rR, h3]

/-- The global shared history of a basic slot acting on its global basic input, in the main
column space; its restriction to an active cell of depth `h` is `B_{l,s} B_l` (`basic_history`). -/
noncomputable def histOut (l : Fin 4) (s : List (CatCol bf.Vtx)) (mb : bf.MainBudget s)
    (ls : List (ℕ × Bool)) (h : ℤ) : ColumnL2 (bf.Lab ⊕ Fin fp.Mc) :=
  colRelabel (bf.rv fp.Mc s) (fp.gHist l s mb ls h
    (ContinuousLinearMap.adjoint (colRelabel (bf.rv fp.Mc s)) (bf.gBasic fp.Mc l h)))

/-- Blueprint lem:variation, shared-history assertion ("without an outer ball the same assertion
holds for a shared history, omitting `G`"): over disjoint depth intervals and unions `E_i` of
active cells of depth `t_i`,
`Σ_i ‖1_{E_i} (B'_{t_i} B_l - B'_{r_i} B_l)‖² ≤ Σ_{j_b} 2 (2 S C_{1,j_b}² + 2) ‖1_R F_{l,j_b}‖²`
with `S = |ls| Σ_m C_m²` the history jump constant. -/
theorem basic_history_variation (l : Fin 4) (s : List (CatCol bf.Vtx)) (mb : bf.MainBudget s)
    (hne : A.cells.Nonempty) {ι' : Type*} [Fintype ι'] (ls : List (ℕ × Bool))
    (r t : ι' → ℕ) (hrt : ∀ i, r i ≤ t i)
    (hdis : ∀ i i', i ≠ i' → Disjoint (Finset.Ioc (r i) (t i)) (Finset.Ioc (r i') (t i')))
    (htd : ∀ i, t i ≤ A.treeDepth) (Ec : ι' → Finset (ℤ × ℤ))
    (hEc : ∀ i, ∀ I ∈ Ec i, I ∈ A.cells) :
    ∑ i, ‖columnL2Restriction (⋃ I ∈ Ec i, dyadicGridCell A.G I.1 I.2)
        (Finset.measurableSet_biUnion _ fun I _ => dyadicGridCell_measurable A.G I.1 I.2)
        (fp.histOut l s mb ls (A.R.1 + t i) - fp.histOut l s mb ls (A.R.1 + r i))‖ ^ 2 ≤
      ∑ jb : Fin 2, 2 * (2 * ((ls.length * (∑ m ∈ Finset.range ls.length,
          compressionC (bf.mainTree fp.Mc s mb) m ^ 2)) *
          compressionC (bf.P l jb).Ψ.D 1 ^ 2) + 2) *
        ‖columnL2Restriction (dyadicGridCell A.G A.R.1 A.R.2)
          (dyadicGridCell_measurable A.G A.R.1 A.R.2) (bf.P l jb).Z‖ ^ 2 := by
  set! rR := fun jb : Fin 2 => columnL2Restriction (V := (bf.P l jb).V)
    (dyadicGridCell A.G A.R.1 A.R.2) (dyadicGridCell_measurable A.G A.R.1 A.R.2)
  set! X : Fin 2 → ℤ → ColumnL2 (bf.RLab fp.Mc s) := fun jb h =>
    fp.gHist l s mb ls h (bf.famEmbR fp.Mc s l jb ((bf.P l jb).Ψ.proj h (rR jb (bf.P l jb).Z)))
  set! rE : ι' → ColumnL2 (bf.RLab fp.Mc s) →L[ℂ] ColumnL2 (bf.RLab fp.Mc s) := fun i =>
    columnL2Restriction (⋃ I ∈ Ec i, dyadicGridCell A.G I.1 I.2)
      (Finset.measurableSet_biUnion _ fun I _ => dyadicGridCell_measurable A.G I.1 I.2)
  set Sj := (ls.length : ℝ) * (∑ m ∈ Finset.range ls.length,
    compressionC (bf.mainTree fp.Mc s mb) m ^ 2) with hSj
  have hS0 : 0 ≤ Sj := by
    have : 0 ≤ ∑ m ∈ Finset.range ls.length, compressionC (bf.mainTree fp.Mc s mb) m ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    positivity
  have hsplit : ∀ i, ‖columnL2Restriction (⋃ I ∈ Ec i, dyadicGridCell A.G I.1 I.2)
      (Finset.measurableSet_biUnion _ fun I _ => dyadicGridCell_measurable A.G I.1 I.2)
      (fp.histOut l s mb ls (A.R.1 + t i) - fp.histOut l s mb ls (A.R.1 + r i))‖ =
      ‖rE i (X 0 (A.R.1 + t i) - X 0 (A.R.1 + r i)) -
        rE i (X 1 (A.R.1 + t i) - X 1 (A.R.1 + r i))‖ := by
    intro i
    have e0 : ∀ h, fp.histOut l s mb ls h = colRelabel (bf.rv fp.Mc s)
        (fp.gHist l s mb ls h (bf.famEmbR fp.Mc s l 0 ((bf.P l 0).Ψ.proj h (bf.P l 0).Z)) -
          fp.gHist l s mb ls h (bf.famEmbR fp.Mc s l 1 ((bf.P l 1).Ψ.proj h (bf.P l 1).Z))) := by
      intro h
      unfold histOut ActiveSetup.BasicFamilies.gBasic ActiveSetup.BasicFamilies.famEmbR
      rw [map_sub, map_sub]
      rfl
    rw [e0, e0, ← map_sub, ← colRelabel_restrict, norm_colRelabel (bf.rv_injective fp.Mc s)]
    have e : ∀ (jb : Fin 2) (h : ℤ), A.R.1 ≤ h → rE i (fp.gHist l s mb ls h
        (bf.famEmbR fp.Mc s l jb ((bf.P l jb).Ψ.proj h (bf.P l jb).Z))) = rE i (X jb h) :=
      fun jb h hh => fp.hist_restrictR hne l s mb ls jb hh (Ec i) (hEc i) _
    simp only [map_sub]
    rw [e 0 _ (by omega), e 1 _ (by omega), e 0 _ (by omega), e 1 _ (by omega)]
    rw [sub_sub_sub_comm]
  have hfam : ∀ jb : Fin 2, ∑ i, ‖rE i (X jb (A.R.1 + t i) - X jb (A.R.1 + r i))‖ ^ 2 ≤
      (2 * (Sj * compressionC (bf.P l jb).Ψ.D 1 ^ 2) + 2) * ‖rR jb (bf.P l jb).Z‖ ^ 2 := by
    intro jb
    set Ψ := (bf.P l jb).Ψ
    have hΨG : Ψ.D.grid = A.G := (bf.P l jb).grid
    have hΨR : dyadicGridCell A.G A.R.1 A.R.2 ⊆ dyadicGridCell A.G Ψ.D.root.1 Ψ.D.root.2 :=
      (bf.P l jb).root_sub
    have hΨr : Ψ.D.root.1 ≤ A.R.1 := dyadicGridCell_depth_le_of_subset A.G A.R Ψ.D.root hΨR
    have hrows : ∀ x, ∑ i, ‖((rE i).comp
        (fp.gHist l s mb ls (A.R.1 + t i) - fp.gHist l s mb ls (A.R.1 + r i))) x‖ ^ 2 ≤
        Sj * ‖x‖ ^ 2 := by
      intro x
      have hj := globHist_jump (bf.mainBase fp.Mc s mb) fp.hP (fp.cumMaskT l s mb) ls r t hrt
        hdis x
      refine le_trans (Finset.sum_le_sum fun i _ => ?_) (hj.trans (le_of_eq (by rw [hSj]; rfl)))
      refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
      simp only [ContinuousLinearMap.comp_apply, rE]
      exact columnL2Indicator_norm_le _ (Finset.measurableSet_biUnion _ fun I _ =>
        dyadicGridCell_measurable A.G I.1 I.2) _
    have hjoint : ∑ i, ‖rE i (fp.gHist l s mb ls (A.R.1 + t i) (bf.famEmbR fp.Mc s l jb
        ((Ψ.proj (A.R.1 + t i) - Ψ.proj (A.R.1 + r i)) (rR jb (bf.P l jb).Z))))‖ ^ 2 ≤
        ‖rR jb (bf.P l jb).Z‖ ^ 2 := by
      refine le_trans (Finset.sum_le_sum fun i _ => ?_)
        (Ψ.jumps_from_le hΨr r t hrt hdis (rR jb (bf.P l jb).Z))
      refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
      simp only [rE]
      refine (columnL2Indicator_norm_le _ (Finset.measurableSet_biUnion _ fun I _ =>
        dyadicGridCell_measurable A.G I.1 I.2) _).trans ?_
      refine (globHist_norm_le _ fp.hP _ ls _ _).trans ?_
      exact bf.norm_famEmbR_le fp.Mc s l jb _
    have h := emb_variation Ψ (bf.famEmbR fp.Mc s l jb) (bf.norm_famEmbR_le fp.Mc s l jb)
      (bf.famEmbR_restrict fp.Mc s l jb) rE (fun _ h => fp.gHist l s mb ls h)
      (fun i => A.R.1 + r i) (fun i => A.R.1 + t i) hS0 hrows
      (fun i x => fp.gHist_rows_blk l s mb ls (by have := hrt i; omega)
        (by have := htd i; omega) (Ec i) (hEc i) Ψ hΨG hΨR hΨr (by omega) x)
      (rR jb (bf.P l jb).Z) hjoint
    exact h.trans (le_of_eq (by ring))
  calc ∑ i, ‖columnL2Restriction (⋃ I ∈ Ec i, dyadicGridCell A.G I.1 I.2)
        (Finset.measurableSet_biUnion _ fun I _ => dyadicGridCell_measurable A.G I.1 I.2)
        (fp.histOut l s mb ls (A.R.1 + t i) - fp.histOut l s mb ls (A.R.1 + r i))‖ ^ 2
      ≤ ∑ i, (2 * ‖rE i (X 0 (A.R.1 + t i) - X 0 (A.R.1 + r i))‖ ^ 2 +
          2 * ‖rE i (X 1 (A.R.1 + t i) - X 1 (A.R.1 + r i))‖ ^ 2) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [hsplit i]
        set a := rE i (X 0 (A.R.1 + t i) - X 0 (A.R.1 + r i))
        set b := rE i (X 1 (A.R.1 + t i) - X 1 (A.R.1 + r i))
        calc ‖a - b‖ ^ 2 ≤ (‖a‖ + ‖b‖) ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le a b) 2
          _ ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by nlinarith [sq_nonneg (‖a‖ - ‖b‖)]
    _ = 2 * ∑ i, ‖rE i (X 0 (A.R.1 + t i) - X 0 (A.R.1 + r i))‖ ^ 2 +
          2 * ∑ i, ‖rE i (X 1 (A.R.1 + t i) - X 1 (A.R.1 + r i))‖ ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ _ := by
        rw [Fin.sum_univ_two]
        have h0 := hfam 0
        have h1 := hfam 1
        nlinarith only [h0, h1]

end ActiveSetup.BasicFamilies.FamParams

namespace ActiveSetup.BasicFamilies.FamParams
variable {κ : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ c₀} {bf : A.BasicFamilies}
  (fp : bf.FamParams)

/-- The basic inputs have energy at most `|R|` on the root: `‖1_R F_{l,j}‖² ≤ |R|` (blueprint
line 2075: `‖F_l‖₂² ≤ |R|`). -/
theorem famInput_energy (l : Fin 4) (jb : Fin 2) :
    ‖columnL2Restriction (dyadicGridCell A.G A.R.1 A.R.2)
        (dyadicGridCell_measurable A.G A.R.1 A.R.2) (bf.P l jb).Z‖ ^ 2 ≤
      dyadicGridLength A.G A.R.1 := by
  rw [columnL2Restriction_norm_sq]
  have h := (bf.P l jb).energy
  rw [one_mul] at h
  exact h

open Classical in
/-- Blueprint lem:variation, intervals crossing the attempt start: with the zero convention the
outputs before the attempt vanish, so such an interval contributes the one-time projection
estimate at its right endpoint,
`Σ_G ‖1_{E_G} Z_{G,t}‖² ≤ Σ_{j_b} 2 (1 + τ N colBudget²) ‖1_R F_{l,j_b}‖²`. -/
theorem basic_onetime (l : Fin 4) (s : List (CatCol bf.Vtx))
    (hT : ∀ e ∈ s, ∃ R ∈ residueBox (bf.vtag e.tag).dim 9, ∃ γ : ℝ,
      e = templateCol (bf.vtag e.tag) l R γ e.birth e.rank e.tag)
    (htag : ∀ e ∈ s, bf.occAvail e.tag.2.1 e.tag.1) (d : bf.Vtx) (mb : bf.MainBudget s)
    (hne : A.cells.Nonempty) {ι : Type*} [Fintype ι] (grp : ι → bf.Grp)
    (hgrp : Function.Injective grp) (k j : ℕ) (hPH : fp.bbase j + fp.P ≤ fp.Hmax)
    (ls : List (ℕ × Bool)) (t : ℕ) (Ec : ι → Finset (ℤ × ℤ))
    (hEc : ∀ G, ∀ I ∈ Ec G, I ∈ A.cells ∧ I.1 = A.R.1 + t)
    (hcert : ∀ G, ∀ I ∈ Ec G, fp.Cert k (grp G) I)
    {ra rb : ℝ} (hroot : ∀ I ∈ A.cells, dyadicGridCell A.G I.1 I.2 ⊆ Set.Icc ra rb)
    {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hHed : Real.exp (A.Dg * (1 + Real.log A.Hsrc + Real.log τ⁻¹) ^ A.Dg) ≤ fp.Hed)
    {N : ℕ} (hN : ∀ y, ((Finset.univ : Finset (ι × (bf.Lab ⊕ Fin fp.Mc))).filter fun q =>
      ∃ I ∈ A.cells, (∃ k', fp.Cert k' (grp q.1) I) ∧
        ∃ p : Fin fp.P, y ∈ dyadicGridCell A.G I.1 I.2 ∧
        q.2 ∈ mainLabelsM A.G fp.Mc (bf.origCols l) s I (fp.brank j)
          (fp.bmask I (grp q.1) j (p + 1)) d).card ≤ N) :
    ∑ G, ‖columnL2Restriction (⋃ I ∈ Ec G, dyadicGridCell A.G I.1 I.2)
        (Finset.measurableSet_biUnion _ fun I _ => dyadicGridCell_measurable A.G I.1 I.2)
        (fp.basicOut l s mb (grp G) j ls (A.R.1 + t))‖ ^ 2 ≤
      ∑ jb : Fin 2, 2 * (1 + τ * N * A.colBudget ^ 2) *
        ‖columnL2Restriction (dyadicGridCell A.G A.R.1 A.R.2)
          (dyadicGridCell_measurable A.G A.R.1 A.R.2) (bf.P l jb).Z‖ ^ 2 := by
  set! rR := fun jb : Fin 2 => columnL2Restriction (V := (bf.P l jb).V)
    (dyadicGridCell A.G A.R.1 A.R.2) (dyadicGridCell_measurable A.G A.R.1 A.R.2)
  set! rE : ι → ColumnL2 (bf.RLab fp.Mc s) →L[ℂ] ColumnL2 (bf.RLab fp.Mc s) := fun G =>
    columnL2Restriction (⋃ I ∈ Ec G, dyadicGridCell A.G I.1 I.2)
      (Finset.measurableSet_biUnion _ fun I _ => dyadicGridCell_measurable A.G I.1 I.2)
  set! X : Fin 2 → ι → ColumnL2 (bf.RLab fp.Mc s) := fun jb G =>
    fp.gOut l s mb (grp G) j ls (A.R.1 + t) (bf.famEmbR fp.Mc s l jb
      ((bf.P l jb).Ψ.proj (A.R.1 + t) (rR jb (bf.P l jb).Z)))
  have hC : (0 : ℝ) ≤ 1 + τ * N * A.colBudget ^ 2 := by positivity
  have hsplit : ∀ G, ‖columnL2Restriction (⋃ I ∈ Ec G, dyadicGridCell A.G I.1 I.2)
      (Finset.measurableSet_biUnion _ fun I _ => dyadicGridCell_measurable A.G I.1 I.2)
      (fp.basicOut l s mb (grp G) j ls (A.R.1 + t))‖ = ‖rE G (X 0 G) - rE G (X 1 G)‖ := by
    intro G
    rw [fp.basicOut_eq, ← colRelabel_restrict, norm_colRelabel (bf.rv_injective fp.Mc s),
      map_sub]
    have hEc' : ∀ I ∈ Ec G, I ∈ A.cells := fun I hI => (hEc G I hI).1
    rw [fp.out_restrictR hne l s mb (grp G) j ls 0 (by omega) (Ec G) hEc',
      fp.out_restrictR hne l s mb (grp G) j ls 1 (by omega) (Ec G) hEc']
  have hfam : ∀ jb : Fin 2, ∑ G, ‖rE G (X jb G)‖ ^ 2 ≤
      (1 + τ * N * A.colBudget ^ 2) * ‖rR jb (bf.P l jb).Z‖ ^ 2 := by
    intro jb
    refine (fp.main_joint l s hT htag d mb grp hgrp k j hPH ls (A.R.1 + t) Ec hEc hcert hroot hτ
      hτ1 hHed hN _).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) ?_ 2) hC)
    refine (bf.norm_famEmbR_le fp.Mc s l jb _).trans ?_
    exact starProjection_norm_apply_le _ ((bf.P l jb).Ψ.isStarProjection_proj _) _
  calc ∑ G, ‖columnL2Restriction (⋃ I ∈ Ec G, dyadicGridCell A.G I.1 I.2)
        (Finset.measurableSet_biUnion _ fun I _ => dyadicGridCell_measurable A.G I.1 I.2)
        (fp.basicOut l s mb (grp G) j ls (A.R.1 + t))‖ ^ 2
      ≤ ∑ G, (2 * ‖rE G (X 0 G)‖ ^ 2 + 2 * ‖rE G (X 1 G)‖ ^ 2) := by
        refine Finset.sum_le_sum fun G _ => ?_
        rw [hsplit G]
        set a := rE G (X 0 G)
        set b := rE G (X 1 G)
        calc ‖a - b‖ ^ 2 ≤ (‖a‖ + ‖b‖) ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le a b) 2
          _ ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by nlinarith [sq_nonneg (‖a‖ - ‖b‖)]
    _ = 2 * ∑ G, ‖rE G (X 0 G)‖ ^ 2 + 2 * ∑ G, ‖rE G (X 1 G)‖ ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ _ := by
        rw [Fin.sum_univ_two]
        have h0 := hfam 0
        have h1 := hfam 1
        nlinarith only [h0, h1]

open Classical in
/-- Blueprint lem:variation (`eq:variation`, lines 1861-1866) with the compression loss `G₀`:
under `log (2 D_m) ≤ k^c`, `log (2 colBudget) ≤ k^c`, histories of `O(log k)` layers and a pair
threshold with `τ N colBudget² ≤ 1` (chosen after the counts, line 1854),
`Σ_{G,[r,t]} ‖1_E (Z_{G,t} - Z_{G,r})‖² ≤ G₀ Σ_{j_b} 2 ‖1_R F_{l,j_b}‖² ≤ 4 G₀ |R|` with
`G₀ = exp(C_q (1 + log 2k)²)`. -/
theorem basic_variation_G0 (l : Fin 4) (s : List (CatCol bf.Vtx))
    (hT : ∀ e ∈ s, ∃ R ∈ residueBox (bf.vtag e.tag).dim 9, ∃ γ : ℝ,
      e = templateCol (bf.vtag e.tag) l R γ e.birth e.rank e.tag)
    (htag : ∀ e ∈ s, bf.occAvail e.tag.2.1 e.tag.1) (d : bf.Vtx) (mb : bf.MainBudget s)
    (hanc : A.AncClosed) (hne : A.cells.Nonempty) {ι ι' : Type*} [Fintype ι] [Fintype ι']
    (grp : ι → bf.Grp) (hgrp : Function.Injective grp) (k j : ℕ)
    (hPH : fp.bbase j + fp.P ≤ fp.Hmax) (ls : List (ℕ × Bool)) (r t : ι' → ℕ)
    (hrt : ∀ i, r i ≤ t i)
    (hdis : ∀ i i', i ≠ i' → Disjoint (Finset.Ioc (r i) (t i)) (Finset.Ioc (r i') (t i')))
    (htd : ∀ i, t i ≤ A.treeDepth) (Ec : ι → ι' → Finset (ℤ × ℤ))
    (hEc : ∀ G i, ∀ I ∈ Ec G i, I ∈ A.cells ∧ I.1 = A.R.1 + t i)
    (hcert : ∀ G i, ∀ I ∈ Ec G i, fp.Cert k (grp G) I)
    {ra rb : ℝ} (hroot : ∀ I ∈ A.cells, dyadicGridCell A.G I.1 I.2 ⊆ Set.Icc ra rb)
    {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hHed : Real.exp (A.Dg * (1 + Real.log A.Hsrc + Real.log τ⁻¹) ^ A.Dg) ≤ fp.Hed)
    {N : ℕ} (hN : ∀ y, ((Finset.univ : Finset (ι × (bf.Lab ⊕ Fin fp.Mc))).filter fun q =>
      ∃ I ∈ A.cells, (∃ k', fp.Cert k' (grp q.1) I) ∧
        ∃ p : Fin fp.P, y ∈ dyadicGridCell A.G I.1 I.2 ∧
        q.2 ∈ mainLabelsM A.G fp.Mc (bf.origCols l) s I (fp.brank j)
          (fp.bmask I (grp q.1) j (p + 1)) d).card ≤ N)
    (hτN : τ * N * A.colBudget ^ 2 ≤ 1) (c : ℕ) (hc : 1 ≤ c) {kk : ℝ} (hk : 1 ≤ kk)
    (hDm : Real.log (2 * mb.B) ≤ kk ^ c) (hDb : Real.log (2 * A.colBudget) ≤ kk ^ c)
    (hn : (ls.length : ℝ) ≤ c * (Real.log kk + 1)) :
    ∑ q : ι × ι', ‖columnL2Restriction (⋃ I ∈ Ec q.1 q.2, dyadicGridCell A.G I.1 I.2)
        (Finset.measurableSet_biUnion _ fun I _ => dyadicGridCell_measurable A.G I.1 I.2)
        (fp.basicOut l s mb (grp q.1) j ls (A.R.1 + t q.2) -
          fp.basicOut l s mb (grp q.1) j ls (A.R.1 + r q.2))‖ ^ 2 ≤
      Real.exp ((4096 * (c + 1) * (1024 * (c + 1) + c + 7) + c ^ 2 + 3) *
        (1 + Real.log (2 * kk)) ^ 2) * (4 * dyadicGridLength A.G A.R.1) := by
  have h := fp.basic_variation l s hT htag d mb hanc hne grp hgrp k j hPH ls r t hrt hdis htd Ec
    hEc hcert hroot hτ hτ1 hHed hN
  refine h.trans ?_
  set G0 := Real.exp ((4096 * (c + 1) * (1024 * (c + 1) + c + 7) + c ^ 2 + 3) *
    (1 + Real.log (2 * kk)) ^ 2)
  have hCw0 : (0 : ℝ) ≤ 1 + τ * N * A.colBudget ^ 2 := by positivity
  have hCw2 : 1 + τ * N * A.colBudget ^ 2 ≤ 2 := by linarith
  have hV : ∀ jb : Fin 2, 2 * ((2 * (1 + τ * N * A.colBudget ^ 2) *
      (compressionC (bf.mainTree fp.Mc s mb) ls.length ^ 2 +
        ls.length * (∑ m ∈ Finset.range ls.length,
          compressionC (bf.mainTree fp.Mc s mb) m ^ 2))) *
      compressionC (bf.P l jb).Ψ.D 1 ^ 2) + 2 * (1 + τ * N * A.colBudget ^ 2) ≤ G0 := by
    intro jb
    have hDb' : Real.log (2 * (bf.P l jb).Ψ.D.budget) ≤ kk ^ c := by
      have hb := (bf.P l jb).Ψ.D.two_le_budget
      refine le_trans (Real.log_le_log (by linarith) ?_) hDb
      have := bf.budget l jb
      linarith
    exact variation_loss_le (bf.mainTree fp.Mc s mb) (bf.P l jb).Ψ.D ls.length c hc hk hDm hDb'
      hn hCw2
  have hE : ∀ jb : Fin 2, ‖columnL2Restriction (dyadicGridCell A.G A.R.1 A.R.2)
      (dyadicGridCell_measurable A.G A.R.1 A.R.2) (bf.P l jb).Z‖ ^ 2 ≤
      dyadicGridLength A.G A.R.1 := fun jb => famInput_energy (bf := bf) l jb
  have hG0 : 0 ≤ G0 := (Real.exp_pos _).le
  rw [Fin.sum_univ_two]
  have hV0 := hV 0
  have hV1 := hV 1
  have hE0 := hE 0
  have hE1 := hE 1
  have hn0 := sq_nonneg ‖columnL2Restriction (dyadicGridCell A.G A.R.1 A.R.2)
    (dyadicGridCell_measurable A.G A.R.1 A.R.2) (bf.P l 0).Z‖
  have hn1 := sq_nonneg ‖columnL2Restriction (dyadicGridCell A.G A.R.1 A.R.2)
    (dyadicGridCell_measurable A.G A.R.1 A.R.2) (bf.P l 1).Z‖
  have hV0' : 0 ≤ 2 * ((2 * (1 + τ * N * A.colBudget ^ 2) *
      (compressionC (bf.mainTree fp.Mc s mb) ls.length ^ 2 +
        ls.length * (∑ m ∈ Finset.range ls.length,
          compressionC (bf.mainTree fp.Mc s mb) m ^ 2))) *
      compressionC (bf.P l 0).Ψ.D 1 ^ 2) + 2 * (1 + τ * N * A.colBudget ^ 2) := by
    have : 0 ≤ ∑ m ∈ Finset.range ls.length, compressionC (bf.mainTree fp.Mc s mb) m ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    positivity
  have hV1' : 0 ≤ 2 * ((2 * (1 + τ * N * A.colBudget ^ 2) *
      (compressionC (bf.mainTree fp.Mc s mb) ls.length ^ 2 +
        ls.length * (∑ m ∈ Finset.range ls.length,
          compressionC (bf.mainTree fp.Mc s mb) m ^ 2))) *
      compressionC (bf.P l 1).Ψ.D 1 ^ 2) + 2 * (1 + τ * N * A.colBudget ^ 2) := by
    have : 0 ≤ ∑ m ∈ Finset.range ls.length, compressionC (bf.mainTree fp.Mc s mb) m ^ 2 :=
      Finset.sum_nonneg fun _ _ => sq_nonneg _
    positivity
  have h0 := mul_le_mul hV0 hE0 hn0 hG0
  have h1 := mul_le_mul hV1 hE1 hn1 hG0
  nlinarith only [hG0, hV0, hV1, hE0, hE1]

end ActiveSetup.BasicFamilies.FamParams

end TrilinearHT.Auto

end
