/-
Copyright (c) 2026 Joris Roos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

/- Adapted for Lean Pool from roos-j/lean-trilinearht at
7b4209609e6a7fb9d9935973ee8541495f943660. Imports, names, proof organization and
Mathlib interfaces have been updated; original authorship is retained above. -/

public import LeanPool.TrilinearHilbertTransform.Auto.Sec124BinaryLocalizationVariation.Setup

/-!
# Trilinear Hilbert transform: leaf_bound
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
private def LeafBoundHballStatement : Prop :=
  ∀ (κ : LocalKernelClass)
    (c₀ : ℕ)
    (A : ActiveSetup κ c₀)
    (bf : A.BasicFamilies)
    (fp : bf.FamParams)
    (cat : Fin (4 : ℕ) → List (CatCol bf.Vtx))
    (I : ℤ × ℤ)
    (_ : I ∈ A.cells)
    (x : Fin (4 : ℕ) → ↥(ColumnL2 (bf.Lab ⊕ Fin fp.Mc)))
    (τ : ℕ → ℝ)
    (_ : ∀ (l : Fin (4 : ℕ)) (w : fp.TestName I Unit), (fp.testOf l I (fun (_ : Unit) => x l)
      w).Pass A.G (bf.origCols l) I A.csrc A.Hsrc bf.vtag (A.w I) (τ (fp.testOf l I (fun
      (_ : Unit) => x l) w).r) fp.mH (cat l))
    (fuel : ℕ)
    (up₀ : Fin (4 : ℕ))
    (s : ℕ),
  let Lf : SearchLeaf :=
    leafAt fuel fp.Lc up₀ s
  ∀ (_ : (1 : ℕ) ≤ Lf.k)
    (_ : Lf.k ≤ fp.Lc)
    (_ : ∀ (l : Fin (4 : ℕ)), (Lf.layers l).length ≤ fp.mH)
    (_ : ∀ (l : Fin (4 : ℕ)), ∀ e ∈ Lf.layers l, e.1 ≤ fp.Lc),
  let xs : Fin (4 : ℕ) → ↥(ColumnL2 (bf.Lab ⊕ Fin fp.Mc)) :=
    fp.inputL cat I x Lf.layers
  let Gs : Finset bf.Grp :=
    fp.groupsAt I Lf.k
  ∀ (gv : (G : bf.Grp) → G ∈ Gs → ↥(bf.admT.X (bf.admAt I)))
    (_ : ∀ (G : bf.Grp) (a : G ∈ Gs), fp.K.grp bf.admT A.famVtxBound (bf.admAt I) (↑(gv G a)
      : bf.Vtx) = G),
  ∀ G ∈ Gs, ∀ (l : Fin (4 : ℕ)) (j : ℕ), (1 : ℕ) ≤ j → j ≤ (4 : ℕ) → ResidOK A.G I
    A.csrc A.Hsrc bf.vtag (A.w I) l (fun (y : bf.Vtx) => ∀ (p : Fin fp.P), fp.bmask I
    G j ((↑p : ℕ) + (1 : ℕ)) y) (xs l - (fp.ballFilt l (cat l) I G j : ↥(ColumnL2
    (bf.Lab ⊕ Fin fp.Mc)) → ↥(ColumnL2 (bf.Lab ⊕ Fin fp.Mc))) (xs l)) (τ (fp.Lc + j) *
    cellNorm A.G I (x l))




private theorem leaf_bound_hball : LeafBoundHballStatement := by
  classical
  intro κ c₀ A bf fp cat I hI x τ hpass fuel up₀ s Lf hk1 hkL hlen hle xs Gs gv hgv G hG l j hj1
    hj4
  have h := fp.layer_residOK' (A.adm I hI) l (cat l) (x l) (Lf.layers l) (hle l) (hlen l)
    ⟨fp.Lc + j - 1, by omega⟩ (rk := fp.brank j) (by unfold brank; simp only; omega)
    (fun p => Sum.inr (gv G hG, ⟨fp.bbase j + p + 1, by
      have := fp.bbase_le (j := j) (p := p) hj4 p.2.le; omega⟩))
    (fun p y => fp.bmask I G j (p + 1) y) (fun p => by
      funext y
      change (y ∈ fp.K.mask bf.admT A.famVtxBound
        (fp.K.grp bf.admT A.famVtxBound (bf.admAt I) (gv G hG).1) (fp.bbase j + p + 1)
          (bf.admAt I)) = _
      rw [hgv G hG]
      rfl) (τ := τ (fp.Lc + j)) (fun pc => by
      have hp := hpass l (fp.layerName I ⟨fp.Lc + j - 1, by omega⟩ (Sum.inr (gv G hG,
        ⟨fp.bbase j + pc.1 + 1, by
          have := fp.bbase_le (j := j) (p := pc.1) hj4 pc.1.2.le; omega⟩))
        (Lf.layers l) (hle l) (hlen l) pc.2)
      have hr : (fp.testOf l I (fun _ => x l) (fp.layerName I ⟨fp.Lc + j - 1, by omega⟩
          (Sum.inr (gv G hG, ⟨fp.bbase j + pc.1 + 1, by
            have := fp.bbase_le (j := j) (p := pc.1) hj4 pc.1.2.le; omega⟩))
          (Lf.layers l) (hle l) (hlen l) pc.2)).r = fp.Lc + j := by
        change fp.Lc + j - 1 + 1 = _; omega
      rw [hr] at hp
      exact hp)
  exact h
-- the leaf error


open Classical in
/-- Blueprint prop:localize at one active cell and one leaf (lines 1848-1853) on the main columns:
given an expansion of the upper guard input in pure bounded charts of vertices of its cumulative
mask, the form of the leaf inputs is the sum over the current groups of the forms of their ball
outputs, up to the old-source (`τ_o`), matching (`τ_m`), separation (`τ₂`) and residual (`τ_r`)
errors; the first ball outputs expand with coefficient sums at most `colBudget √N_t S`. -/
theorem leaf_bound (cat : Fin 4 → List (CatCol bf.Vtx))
    (hT : ∀ l, ∀ e ∈ cat l, ∃ R ∈ residueBox (bf.vtag e.tag).dim 9, ∃ γ : ℝ,
      e = templateCol (bf.vtag e.tag) l R γ e.birth e.rank e.tag)
    (htag : ∀ l, ∀ e ∈ cat l, bf.occAvail e.tag.2.1 e.tag.1)
    {I : ℤ × ℤ} (hI : I ∈ A.cells) (x : Fin 4 → ColumnL2 (bf.Lab ⊕ Fin fp.Mc)) {τ : ℕ → ℝ}
    (hpass : ∀ l (w : fp.TestName I Unit), (fp.testOf l I (fun _ => x l) w).Pass A.G
      (bf.origCols l) I A.csrc A.Hsrc bf.vtag (A.w I) (τ (fp.testOf l I (fun _ => x l) w).r)
        fp.mH (cat l))
    (hsucc : ∀ w ∈ bf.admT.X (bf.admAt I),
      fp.K.Success (fp.K.colorData (bf.admT.st (bf.admAt I)) w))
    {fuel : ℕ} {up₀ : Fin 4} (hL1 : 1 ≤ fp.Lc) (hfuel : fp.Lc - 1 < 2 ^ fuel)
    (hmH : fuel ≤ fp.mH) {s : ℕ} (hs : s < (searchList fuel fp.Lc up₀).length)
    {τo τm τr τ₂ Sz Nt : ℝ} (hτo : 0 ≤ τo) (hτm : 0 ≤ τm) (hτr : 0 ≤ τr) (hτ₂ : 0 < τ₂)
    (hτ₂1 : τ₂ ≤ 1)
    (hHed : Real.exp (A.Dg * (1 + Real.log A.Hsrc + Real.log τ₂⁻¹) ^ A.Dg) ≤ fp.Hed)
    (hτo' : τ (fp.crank ((leafAt fuel fp.Lc up₀ s).k - 1)) ≤ τo) (hτm' : τ (fp.Lc + 1) ≤ τm)
    (hτr' : ∀ j, 2 ≤ j → j ≤ 4 → τ (fp.Lc + j) ≤ τr) (hSz0 : 0 < Sz)
    (hSz : ∀ l, ‖x l‖ / Real.sqrt (dyadicGridLength A.G I.1) ≤ Sz) (d : bf.Vtx)
    {ι : Type} (S : Finset ι) (a : ι → ℂ) (φ : ι → ColumnL2 (bf.Lab ⊕ Fin fp.Mc))
    (hx : fp.inputL cat I x (leafAt fuel fp.Lc up₀ s).layers (leafAt fuel fp.Lc up₀ s).up =
      ∑ v ∈ S, a v • φ v)
    (hsrc : ∀ v ∈ S, ∃ (y : bf.Vtx) (hpad : ℕ),
      hpad ≤ fp.cbase (leafAt fuel fp.Lc up₀ s).k + fp.P + 1 ∧
      y ∈ fp.K.cumMask bf.admT A.famVtxBound (leafAt fuel fp.Lc up₀ s).k hpad (bf.admAt I) ∧
      ∃ Ay : QuadraticChartData (bf.vtag y).dim, QuadraticChartComplexity A.csrc A.Hsrc Ay ∧
        IsBoundedQuadraticChart Ay ∧ Ay.horizontal = (bf.vtag y).θ ∧
        Ay.matrix = (slotCoeff (leafAt fuel fp.Lc up₀ s).up : ℚ) • (bf.vtag y).C ∧
        Ay.quadratic = slotCoeff (leafAt fuel fp.Lc up₀ s).up * (bf.vtag y).lam ∧
        ∀ᵐ z ∂volume, z ∈ dyadicGridCell A.G I.1 I.2 → augPhys (φ v) z = quadraticChartAtom Ay z)
    (hNt : ∀ G ∈ fp.groupsAt I (leafAt fuel fp.Lc up₀ s).k,
      ((mainLabelsM A.G fp.Mc (bf.origCols (thirdSlot (leafAt fuel fp.Lc up₀ s).up
        (leafAt fuel fp.Lc up₀ s).low)) (cat (thirdSlot (leafAt fuel fp.Lc up₀ s).up
          (leafAt fuel fp.Lc up₀ s).low)) I (fp.Lc + 1)
            (fun y => ∃ p : Fin fp.P, fp.bmask I G 1 (p + 1) y) d).card : ℝ) ≤ Nt) :
    ‖cellForm (dyadicGridLength_pos A.G I.1) (A.adm I hI) (bf.Lab ⊕ Fin fp.Mc)
        (fp.inputL cat I x (leafAt fuel fp.Lc up₀ s).layers) -
      ∑ G ∈ fp.groupsAt I (leafAt fuel fp.Lc up₀ s).k,
        cellForm (dyadicGridLength_pos A.G I.1) (A.adm I hI) (bf.Lab ⊕ Fin fp.Mc)
          (fun l => fp.ballFilt l (cat l) I G ((leafAt fuel fp.Lc up₀ s).role l)
            (fp.inputL cat I x (leafAt fuel fp.Lc up₀ s).layers l))‖ ≤
      (∑ v ∈ S, ‖a v‖) * (((fp.groupsAt I (leafAt fuel fp.Lc up₀ s).k).card + 1) *
          (τo * Sz * Sz * Sz) + τm * Sz * Sz * Sz +
          (fp.groupsAt I (leafAt fuel fp.Lc up₀ s).k).card *
            (τ₂ * Sz * Sz * (A.colBudget * Real.sqrt Nt * Sz))) +
        (fp.groupsAt I (leafAt fuel fp.Lc up₀ s).k).card *
          (3 * ((A.colBudget * Real.sqrt Nt * Sz) * (τr * Sz * Sz * Sz))) := by
  obtain ⟨-, hk1, hkL, hinv⟩ := leafAt_facts hL1 hfuel hs
  obtain ⟨hlowup, -, hlow⟩ := hinv
  have hmemL := leafAt_mem hs
  set Lf := leafAt fuel fp.Lc up₀ s with hLf
  set u := Lf.up with hu
  set t := thirdSlot u Lf.low with ht
  obtain ⟨htu, hlt⟩ := thirdSlot_ne u Lf.low
  have hut : u ≠ t := Ne.symm htu
  obtain ⟨hpu, hpt, hqu, hqt, hpq⟩ := otherTwo_spec u t hut
  have hlen : ∀ l, (Lf.layers l).length ≤ fp.mH := fun l => by
    have := searchLeaves_layers_length fuel 1 fp.Lc up₀ none (fun _ => []) Lf hmemL l
    simp only [List.length_nil, zero_add] at this
    omega
  have hle : ∀ l, ∀ e ∈ Lf.layers l, e.1 ≤ fp.Lc := fun l => leafAt_layers_le s l
  set xs := fp.inputL cat I x Lf.layers with hxs
  have hsr : 0 < Real.sqrt (dyadicGridLength A.G I.1) :=
    Real.sqrt_pos.mpr (dyadicGridLength_pos A.G I.1)
  have hSz' : ∀ l, ‖xs l‖ / Real.sqrt (dyadicGridLength A.G I.1) ≤ Sz := fun l =>
    (div_le_div_of_nonneg_right (fp.norm_inputL_le cat I x Lf.layers l) hsr.le).trans (hSz l)
  have hcN : ∀ l, cellNorm A.G I (x l) ≤ Sz := fun l => (cellNorm_le A.G I (x l)).trans (hSz l)
  have hcN0 : ∀ l, 0 ≤ cellNorm A.G I (x l) := fun l => Real.sqrt_nonneg _
  set Gs := fp.groupsAt I Lf.k with hGs
  -- the sources of the upper guard
  have hsrc' : ∀ v : S, ∃ (y : bf.Vtx) (hpad : ℕ), hpad ≤ fp.cbase Lf.k + fp.P + 1 ∧
      y ∈ fp.K.cumMask bf.admT A.famVtxBound Lf.k hpad (bf.admAt I) ∧
      ∃ Ay : QuadraticChartData (bf.vtag y).dim, QuadraticChartComplexity A.csrc A.Hsrc Ay ∧
        IsBoundedQuadraticChart Ay ∧ Ay.horizontal = (bf.vtag y).θ ∧
        Ay.matrix = (slotCoeff u : ℚ) • (bf.vtag y).C ∧
        Ay.quadratic = slotCoeff u * (bf.vtag y).lam ∧
        ∀ᵐ z ∂volume, z ∈ dyadicGridCell A.G I.1 I.2 → augPhys (φ v) z = quadraticChartAtom Ay z :=
    fun v => hsrc v v.2
  choose X hpad hpadle hXm Ax hAx hAb hθ hM hq hae using hsrc'
  -- the groups of the sources
  set! grp : S → Option bf.Grp := fun v =>
    if h : ∃ G ∈ Gs, ∀ p' : ℕ, fp.bmask I G 1 (p' + 1) (X v) then some (Classical.choose h)
    else none with hgrpdef
  have hgrp : ∀ v G₀, grp v = some G₀ → G₀ ∈ Gs ∧ ∀ p' : ℕ, fp.bmask I G₀ 1 (p' + 1) (X v) := by
    intro v G₀ hg
    by_cases h : ∃ G ∈ Gs, ∀ p' : ℕ, fp.bmask I G 1 (p' + 1) (X v)
    · have e : grp v = some (Classical.choose h) := dite_eq_left_of_eq_true (eq_true h)
      rw [e, Option.some_inj] at hg
      subst hg
      exact Classical.choose_spec h
    · have e : grp v = none := dite_eq_right_of_eq_false (eq_false h)
      rw [e] at hg; exact absurd hg (by simp)
  -- a present vertex for every current group
  have hGv : ∀ G ∈ Gs, ∃ w : {w // w ∈ bf.admT.X (bf.admAt I)},
      fp.K.grp bf.admT A.famVtxBound (bf.admAt I) w.1 = G := fun G hG => by
    obtain ⟨w, hw, -, hwG⟩ := fp.mem_groupsAt hG
    exact ⟨⟨w, hw⟩, hwG⟩
  choose gv hgv using hGv
  -- the expansions of the first ball outputs in slot `t`
  set! F : bf.Grp → Finset (bf.Lab ⊕ Fin fp.Mc) := fun G =>
    mainLabelsM A.G fp.Mc (bf.origCols t) (cat t) I (fp.Lc + 1)
      (fun y => ∃ p : Fin fp.P, fp.bmask I G 1 (p + 1) y) d with hF
  have hexp0 := fun G : bf.Grp => bf.avg_expansion t (cat t) I (fp.Lc + 1) fp.hP
    (fun p y => fp.bmask I G 1 (p + 1) y) (fun y => ∃ p : Fin fp.P, fp.bmask I G 1 (p + 1) y)
    (fun p y hy => ⟨p, hy⟩) d (xs t)
  choose c hc hcb using hexp0
  -- the charts of the main labels of the slot `t`
  have hch : ∀ v ∈ mainLabels A.G fp.Mc (bf.origCols t) (cat t) I (fp.Lc + 1),
      ∃ A' : QuadraticChartData (bf.vtag (labelTag (bf.origCols t) (cat t) I d v)).dim,
        QuadraticChartComplexity A.csrc A.Hsrc A' ∧ IsBoundedQuadraticChart A' ∧
        A'.horizontal = (bf.vtag (labelTag (bf.origCols t) (cat t) I d v)).θ ∧
        A'.matrix = (slotCoeff t : ℚ) • (bf.vtag (labelTag (bf.origCols t) (cat t) I d v)).C ∧
        A'.quadratic = slotCoeff t * (bf.vtag (labelTag (bf.origCols t) (cat t) I d v)).lam ∧
        ∀ᵐ y ∂volume, y ∈ dyadicGridCell A.G I.1 I.2 →
          augPhys (mainCol A.G fp.Mc (bf.origCols t) (cat t) I v) y = quadraticChartAtom A' y :=
    fun v hv => (bf.mainLabel_source t (cat t) (hT t) (htag t) I (fp.Lc + 1) (fun _ => True) d
      (mem_mainLabelsM.mpr ⟨hv, trivial⟩)).2
  choose Ach hAch using hch
  set! Y : bf.Lab ⊕ Fin fp.Mc → ℝ → ℂ := fun m =>
    if h : m ∈ mainLabels A.G fp.Mc (bf.origCols t) (cat t) I (fp.Lc + 1) then
      quadraticChartAtom (Ach m h) else 0 with hYdef
  have hY : ∀ m (h : m ∈ mainLabels A.G fp.Mc (bf.origCols t) (cat t) I (fp.Lc + 1)),
      Y m = quadraticChartAtom (Ach m h) := fun m h => dite_eq_left_of_eq_true (eq_true h)
  have hFsub : ∀ G, ∀ m ∈ F G, m ∈ mainLabels A.G fp.Mc (bf.origCols t) (cat t) I (fp.Lc + 1) :=
    fun G m hm => mainLabelsM_subset _ _ _ _ _ hm
  have hP1 : 1 ≤ fp.P := fp.hP
  -- the residual tests of the ball levels
  have hball : ∀ G ∈ Gs, ∀ l (j : ℕ), 1 ≤ j → j ≤ 4 →
      ResidOK A.G I A.csrc A.Hsrc bf.vtag (A.w I) l (fun y => ∀ p : Fin fp.P,
          fp.bmask I G j (p + 1) y)
        (xs l - fp.ballFilt l (cat l) I G j (xs l)) (τ (fp.Lc + j) * cellNorm A.G I (x l)) := by
    expose_names
    exact @leaf_bound_hball κ c₀ A bf fp cat I hI x τ hpass fuel up₀ s hk1 hkL hlen hle gv hgv
  have h := leaf_error_resid (A.adm I hI) xs (fun G l => fp.ballFilt l (cat l) I G (Lf.role l))
    (fun G l y => fp.norm_ballFilt_apply_le l (cat l) I G _ y) hut hpu.symm hqu.symm hpt.symm
    hqt.symm hpq hSz0 hSz' S.attach (fun v => a v) (fun v => φ v) X Ax
    (by rw [Finset.sum_attach S (fun v => a v • φ v)]; exact hx)
    (fun v _ => ⟨hAx v, hθ v, hM v, hq v, hae v⟩) Gs grp F c
    (mainCol A.G fp.Mc (bf.origCols t) (cat t) I) Y
    (labelTag (bf.origCols t) (cat t) I d)
    (βo := τo * Sz) (βm := τm * Sz) (βr := τr * Sz) (τ₂ := τ₂)
    (Ct := A.colBudget * Real.sqrt Nt * Sz) (by positivity) (by positivity) (by positivity)
    hτ₂.le (by have := A.two_le_colBudget; positivity)
    (fun v _ hg => by
      have hnot : ¬ ∃ G ∈ Gs, ∀ p' : ℕ, fp.bmask I G 1 (p' + 1) (X v) := by
        intro hcx
        have e : grp v = some (Classical.choose hcx) := dite_eq_left_of_eq_true (eq_true hcx)
        rw [e] at hg; exact absurd hg (by simp)
      rcases fp.classify I hsucc hk1 hkL (hpadle v) (hXm v) with hold | hcur
      · rcases hlow with ⟨-, hℓ⟩ | ⟨g, ls', hg', hlg, -⟩
        · exfalso
          obtain ⟨-, w, hw, hc, -⟩ := hold 0
          have := (fp.K.color_mem bf.admT bf.admT_X_card_le hw).1
          have : Lf.k = 1 := hℓ
          omega
        · have hgu : g ≠ u := fun he => hlowup (hg'.trans (congrArg some he))
          have hgt : g ≠ t := fun he => hlt (hg'.trans (congrArg some he))
          obtain ⟨b', hbu, hbt, hgb⟩ := fin4_fourth u t g hut hgu hgt
          have hls' : ∀ e ∈ ls', e.1 ≤ fp.Lc := fun e he =>
            hle g e (by rw [hlg]; exact List.mem_append_left _ he)
          have hlen' : ls'.length ≤ fp.mH := by
            have := hlen g; rw [hlg, List.length_append] at this; omega
          have hcr : 1 ≤ fp.crank (Lf.k - 1) := by unfold crank; omega
          have hcrL : fp.crank (Lf.k - 1) - 1 < fp.Lc + 5 := by unfold crank; omega
          have hR := fp.layer_residOK' (A.adm I hI) g (cat g) (x g) ls' hls' hlen'
            ⟨fp.crank (Lf.k - 1) - 1, hcrL⟩ (rk := fp.crank (Lf.k - 1))
            (by simp only; omega)
            (fun p => Sum.inl (⟨Lf.k - 1, by omega⟩, ⟨fp.cbase (Lf.k - 1) + p + 1, by
              have := fp.cbase_le (m := Lf.k - 1) (p := p) p.2.le; omega⟩))
            (fun p y => fp.cmask I (Lf.k - 1) (p + 1) y) (fun p => rfl)
            (τ := τ (fp.crank (Lf.k - 1))) (fun pc => by
              have hp := hpass g (fp.layerName I ⟨fp.crank (Lf.k - 1) - 1, hcrL⟩
                (Sum.inl (⟨Lf.k - 1, by omega⟩, ⟨fp.cbase (Lf.k - 1) + pc.1 + 1, by
                  have := fp.cbase_le (m := Lf.k - 1) (p := pc.1) pc.1.2.le; omega⟩))
                ls' hls' hlen' pc.2)
              have hr : (fp.testOf g I (fun _ => x g) (fp.layerName I
                  ⟨fp.crank (Lf.k - 1) - 1, hcrL⟩
                  (Sum.inl (⟨Lf.k - 1, by omega⟩, ⟨fp.cbase (Lf.k - 1) + pc.1 + 1, by
                    have := fp.cbase_le (m := Lf.k - 1) (p := pc.1) pc.1.2.le; omega⟩))
                  ls' hls' hlen' pc.2)).r = fp.crank (Lf.k - 1) := by
                change fp.crank (Lf.k - 1) - 1 + 1 = _; omega
              rw [hr] at hp
              exact hp)
          have hxg : xs g = layerOp (fun m => fp.cumFilt g (cat g) I m) ls' (x g) -
              opAvg (fun p : Fin fp.P => mainProj A.G fp.Mc (bf.origCols g) (cat g) I
                (fp.crank (Lf.k - 1)) (fp.cmask I (Lf.k - 1) (p + 1)))
                (layerOp (fun m => fp.cumFilt g (cat g) I m) ls' (x g)) := by
            change layerOp (fun m => fp.cumFilt g (cat g) I m) (Lf.layers g) (x g) = _
            rw [hlg, layerOp_append]
            simp only [↓reduceIte, ContinuousLinearMap.comp_apply, sub_apply]
            rfl
          refine ⟨g, b', hgu, hgt, hbu, hbt, hgb, fun y => ∀ p : Fin fp.P,
            fp.cmask I (Lf.k - 1) (p + 1) y, fun p => hold p, ?_⟩
          rw [hxg]
          exact hR.mono (fun _ h => h) (level_le hτo' (hcN0 g) (hcN g) hτo)
      · exact absurd hcur hnot)
    (fun v _ G₀ hg => by
      obtain ⟨hG₀, hxG₀⟩ := hgrp v G₀ hg
      refine ⟨hG₀, fun y => ∀ p : Fin fp.P, fp.bmask I G₀ 1 (p + 1) y, fun p => hxG₀ p, ?_⟩
      have hR := hball G₀ hG₀ t 1 le_rfl (by omega)
      have hrt : Lf.role t = 1 := Lf.role_t
      change ResidOK A.G I A.csrc A.Hsrc bf.vtag (A.w I) t _
        (xs t - fp.ballFilt t (cat t) I G₀ (Lf.role t) (xs t)) (τm * Sz)
      rw [hrt]
      exact hR.mono (fun _ h => h) (level_le hτm' (hcN0 t) (hcN t) hτm))
    (fun G hG => by
      have hrt : Lf.role t = 1 := Lf.role_t
      refine ⟨?_, ?_⟩
      · rw [hrt]
        exact hc G
      · refine (hcb G).trans ?_
        rw [div_le_iff₀ hsr]
        have hN := Real.sqrt_le_sqrt (hNt G hG)
        have h1 : ‖xs t‖ ≤ Sz * Real.sqrt (dyadicGridLength A.G I.1) := by
          have := hSz' t; rwa [div_le_iff₀ hsr] at this
        have hcb0 : 0 ≤ A.colBudget := by have := A.two_le_colBudget; linarith
        calc A.colBudget * Real.sqrt (F G).card * ‖xs t‖
            ≤ A.colBudget * Real.sqrt Nt * (Sz * Real.sqrt (dyadicGridLength A.G I.1)) := by
              gcongr
          _ = A.colBudget * Real.sqrt Nt * Sz * Real.sqrt (dyadicGridLength A.G I.1) := by ring)
    (fun G _ m hm => by rw [hY m (hFsub G m hm)]; exact (hAch m (hFsub G m hm)).2.2.2.2.2)
    (fun v _ G₀ hg G hG hne m hm => by
      obtain ⟨hG₀, hxG₀⟩ := hgrp v G₀ hg
      obtain ⟨p', hp'⟩ := (mem_mainLabelsM.mp hm).2
      obtain ⟨hc', hb', hθ', hM', hq', -⟩ := hAch m (hFsub G m hm)
      rw [hY m (hFsub G m hm)]
      exact fp.sep_pair hI hsucc hG₀ hG hne hτ₂ hτ₂1 hHed hut (p₀ := 0 + 1) (by omega)
        (hxG₀ 0) (Ax v) (hAx v) (hAb v) (hθ v) (hM v) (hq v) (p := p' + 1) (by have := p'.2; omega)
        hp' (Ach m (hFsub G m hm)) hc' hb' hθ' hM' hq' (A.adm I hI))
    (fun G hG l hl => by
      have hj2 := Lf.role_ge hl
      have hj4 := Lf.role_le l
      refine ⟨fun y => ∀ p : Fin fp.P, fp.bmask I G (Lf.role l) (p + 1) y, fun m hm p => ?_, ?_⟩
      · obtain ⟨p', hp'⟩ := (mem_mainLabelsM.mp hm).2
        have h1 := fp.bbase_one_le hj2
        have h2 := p'.2
        exact ColorSetup.mask_pad_mono _ _ _
          (show fp.bbase 1 + (p' + 1) ≤ fp.bbase (Lf.role l) + (p + 1) by omega) hp'
      · exact (hball G hG l (Lf.role l) (by omega) hj4).mono (fun _ h => h)
          (level_le (hτr' _ hj2 hj4) (hcN0 l) (hcN l) hτr))
    (fun G _ m hm => by
      obtain ⟨hc', -, hθ', hM', hq', hae'⟩ := hAch m (hFsub G m hm)
      exact ⟨Ach m (hFsub G m hm), hc', hθ', hM', hq', hae'⟩)
  rw [Finset.sum_attach S (fun v => ‖a v‖)] at h
  refine h.trans (le_of_eq ?_)
  ring

end ActiveSetup.BasicFamilies.FamParams

namespace ActiveSetup.BasicFamilies.FamParams
variable {κ : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ c₀} {bf : A.BasicFamilies}
  (fp : bf.FamParams)

open Classical in
/-- Blueprint prop:localize at one active cell and one leaf (lines 1848-1853), with the expansion
of the upper guard (line 1850: "expand only this outer primal"): a cumulative main filter
(coefficient sum at most `colBudget √N_u S` over its `N_u` main labels, blueprint line 1835) or
the basic slot, whose input is a combination of its available original columns (coefficient sum
at most `colBudget √(2 colBudget) S`). -/
theorem leaf_main (cat : Fin 4 → List (CatCol bf.Vtx))
    (hT : ∀ l, ∀ e ∈ cat l, ∃ R ∈ residueBox (bf.vtag e.tag).dim 9, ∃ γ : ℝ,
      e = templateCol (bf.vtag e.tag) l R γ e.birth e.rank e.tag)
    (htag : ∀ l, ∀ e ∈ cat l, bf.occAvail e.tag.2.1 e.tag.1)
    {I : ℤ × ℤ} (hI : I ∈ A.cells) (x : Fin 4 → ColumnL2 (bf.Lab ⊕ Fin fp.Mc)) {τ : ℕ → ℝ}
    (hpass : ∀ l (w : fp.TestName I Unit), (fp.testOf l I (fun _ => x l) w).Pass A.G
      (bf.origCols l) I A.csrc A.Hsrc bf.vtag (A.w I) (τ (fp.testOf l I (fun _ => x l) w).r)
        fp.mH (cat l))
    (hsucc : ∀ w ∈ bf.admT.X (bf.admAt I),
      fp.K.Success (fp.K.colorData (bf.admT.st (bf.admAt I)) w))
    (hLcol : ∀ w ∈ bf.admT.X (bf.admAt I),
      fp.K.color bf.admT A.famVtxBound (bf.admAt I) w ≤ fp.Lc)
    {fuel : ℕ} {up₀ : Fin 4}
    (hbasic : ∃ cb : bf.Lab → ℂ, x up₀ = ∑ v ∈ Finset.univ.filter
      (fun v => (bf.origCols up₀).avail I v), cb v •
        mainCol A.G fp.Mc (bf.origCols up₀) (cat up₀) I (Sum.inl v))
    (hL1 : 1 ≤ fp.Lc) (hfuel : fp.Lc - 1 < 2 ^ fuel) (hmH : fuel ≤ fp.mH) {s : ℕ}
    (hs : s < (searchList fuel fp.Lc up₀).length)
    {τo τm τr τ₂ Sz Nt Nu : ℝ} (hτo : 0 ≤ τo) (hτm : 0 ≤ τm) (hτr : 0 ≤ τr) (hτ₂ : 0 < τ₂)
    (hτ₂1 : τ₂ ≤ 1)
    (hHed : Real.exp (A.Dg * (1 + Real.log A.Hsrc + Real.log τ₂⁻¹) ^ A.Dg) ≤ fp.Hed)
    (hτo' : τ (fp.crank ((leafAt fuel fp.Lc up₀ s).k - 1)) ≤ τo) (hτm' : τ (fp.Lc + 1) ≤ τm)
    (hτr' : ∀ j, 2 ≤ j → j ≤ 4 → τ (fp.Lc + j) ≤ τr) (hSz0 : 0 < Sz)
    (hSz : ∀ l, ‖x l‖ / Real.sqrt (dyadicGridLength A.G I.1) ≤ Sz) (d : bf.Vtx)
    (hNu : ((mainLabelsM A.G fp.Mc (bf.origCols (leafAt fuel fp.Lc up₀ s).up)
      (cat (leafAt fuel fp.Lc up₀ s).up) I (fp.crank (leafAt fuel fp.Lc up₀ s).k)
        (fun y => ∃ p : Fin fp.P, fp.cmask I (leafAt fuel fp.Lc up₀ s).k (p + 1) y) d).card : ℝ) ≤
      Nu)
    (hNt : ∀ G ∈ fp.groupsAt I (leafAt fuel fp.Lc up₀ s).k,
      ((mainLabelsM A.G fp.Mc (bf.origCols (thirdSlot (leafAt fuel fp.Lc up₀ s).up
        (leafAt fuel fp.Lc up₀ s).low)) (cat (thirdSlot (leafAt fuel fp.Lc up₀ s).up
          (leafAt fuel fp.Lc up₀ s).low)) I (fp.Lc + 1)
            (fun y => ∃ p : Fin fp.P, fp.bmask I G 1 (p + 1) y) d).card : ℝ) ≤ Nt) :
    ‖cellForm (dyadicGridLength_pos A.G I.1) (A.adm I hI) (bf.Lab ⊕ Fin fp.Mc)
        (fp.inputL cat I x (leafAt fuel fp.Lc up₀ s).layers) -
      ∑ G ∈ fp.groupsAt I (leafAt fuel fp.Lc up₀ s).k,
        cellForm (dyadicGridLength_pos A.G I.1) (A.adm I hI) (bf.Lab ⊕ Fin fp.Mc)
          (fun l => fp.ballFilt l (cat l) I G ((leafAt fuel fp.Lc up₀ s).role l)
            (fp.inputL cat I x (leafAt fuel fp.Lc up₀ s).layers l))‖ ≤
      (A.colBudget * (Real.sqrt Nu + Real.sqrt (2 * A.colBudget)) * Sz) *
          (((fp.groupsAt I (leafAt fuel fp.Lc up₀ s).k).card + 1) * (τo * Sz * Sz * Sz) +
          τm * Sz * Sz * Sz + (fp.groupsAt I (leafAt fuel fp.Lc up₀ s).k).card *
            (τ₂ * Sz * Sz * (A.colBudget * Real.sqrt Nt * Sz))) +
        (fp.groupsAt I (leafAt fuel fp.Lc up₀ s).k).card *
          (3 * ((A.colBudget * Real.sqrt Nt * Sz) * (τr * Sz * Sz * Sz))) := by
  obtain ⟨hkhi, hk1, hkL, hinv⟩ := leafAt_facts hL1 hfuel hs
  set Lf := leafAt fuel fp.Lc up₀ s with hLf
  have hsr : 0 < Real.sqrt (dyadicGridLength A.G I.1) :=
    Real.sqrt_pos.mpr (dyadicGridLength_pos A.G I.1)
  have hcb := A.two_le_colBudget
  have hE : 0 ≤ ((fp.groupsAt I Lf.k).card + 1) * (τo * Sz * Sz * Sz) + τm * Sz * Sz * Sz +
      (fp.groupsAt I Lf.k).card * (τ₂ * Sz * Sz * (A.colBudget * Real.sqrt Nt * Sz)) := by
    have := hτ₂.le; positivity
  have hNu0 : (0 : ℝ) ≤ Nu := le_trans (Nat.cast_nonneg _) hNu
  have hxu : ∀ l, ‖x l‖ ≤ Sz * Real.sqrt (dyadicGridLength A.G I.1) := fun l => by
    have := hSz l; rwa [div_le_iff₀ hsr] at this
  rcases hinv.2.1 with ⟨ls', hls'⟩ | ⟨hup, hnil, hhi⟩
  · -- the catalog case: the upper guard is a cumulative main filter at the color `k`
    rw [← hkhi] at hls'
    set! z := layerOp (fun m => fp.cumFilt Lf.up (cat Lf.up) I m) ls' (x Lf.up) with hz
    obtain ⟨a, hxa, hab⟩ := bf.avg_expansion Lf.up (cat Lf.up) I (fp.crank Lf.k) fp.hP
      (fun p y => fp.cmask I Lf.k (p + 1) y) (fun y => ∃ p : Fin fp.P, fp.cmask I Lf.k (p + 1) y)
      (fun p y hy => ⟨p, hy⟩) d z
    set F := mainLabelsM A.G fp.Mc (bf.origCols Lf.up) (cat Lf.up) I (fp.crank Lf.k)
      (fun y => ∃ p : Fin fp.P, fp.cmask I Lf.k (p + 1) y) d
    have hx : fp.inputL cat I x Lf.layers Lf.up = ∑ v ∈ F, a v •
        mainCol A.G fp.Mc (bf.origCols Lf.up) (cat Lf.up) I v := by
      rw [← hxa]
      change layerOp (fun m => fp.cumFilt Lf.up (cat Lf.up) I m) (Lf.layers Lf.up) (x Lf.up) = _
      rw [hls', layerOp_append]
      rfl
    have h := fp.leaf_bound cat hT htag hI x hpass hsucc hL1 hfuel hmH hs hτo hτm hτr hτ₂ hτ₂1
      hHed hτo' hτm' hτr' hSz0 hSz d F a
      (mainCol A.G fp.Mc (bf.origCols Lf.up) (cat Lf.up) I) hx
      (fun v hv => by
        obtain ⟨⟨p, hp⟩, A', hA', hAb, hθ, hM, hq, he⟩ :=
          bf.mainLabel_source Lf.up (cat Lf.up) (hT _) (htag _) I (fp.crank Lf.k) _ d hv
        refine ⟨_, fp.cbase Lf.k + (p + 1), by rw [← hLf]; have := p.2; omega, hp, A', hA', hAb, hθ,
          hM, hq, he⟩)
      hNt
    refine h.trans ?_
    have hsum : ∑ v ∈ F, ‖a v‖ ≤
        A.colBudget * (Real.sqrt Nu + Real.sqrt (2 * A.colBudget)) * Sz := by
      refine hab.trans ?_
      rw [div_le_iff₀ hsr]
      have hz' : ‖z‖ ≤ ‖x Lf.up‖ :=
        norm_layerOp_apply_le _ (fun m y => (fp.norm_cumFilt_apply_le Lf.up (cat Lf.up) I m y).1)
          (fun m y => (fp.norm_cumFilt_apply_le Lf.up (cat Lf.up) I m y).2) _ _
      have hN := Real.sqrt_le_sqrt hNu
      have h2 := Real.sqrt_nonneg (2 * A.colBudget)
      calc A.colBudget * Real.sqrt F.card * ‖z‖
          ≤ A.colBudget * (Real.sqrt Nu + Real.sqrt (2 * A.colBudget)) *
            (Sz * Real.sqrt (dyadicGridLength A.G I.1)) := by
            gcongr
            · linarith
            · exact hz'.trans (hxu _)
        _ = _ := by ring
    gcongr
  · -- the basic case: the upper guard is the basic slot, expanded in its original columns
    obtain ⟨cb, hcbx⟩ := hbasic
    have hk : Lf.k = fp.Lc := hkhi.trans hhi
    set Fb := Finset.univ.filter fun v => (bf.origCols up₀).avail I v with hFb
    have hx : fp.inputL cat I x Lf.layers Lf.up = ∑ v ∈ Fb, cb v •
        mainCol A.G fp.Mc (bf.origCols Lf.up) (cat Lf.up) I (Sum.inl v) := by
      change layerOp (fun m => fp.cumFilt Lf.up (cat Lf.up) I m) (Lf.layers Lf.up) (x Lf.up) = _
      rw [hnil, layerOp_nil, ContinuousLinearMap.id_apply, hup]
      exact hcbx
    have h := fp.leaf_bound cat hT htag hI x hpass hsucc hL1 hfuel hmH hs hτo hτm hτr hτ₂ hτ₂1
      hHed hτo' hτm' hτr' hSz0 hSz d Fb cb
      (fun v => mainCol A.G fp.Mc (bf.origCols Lf.up) (cat Lf.up) I (Sum.inl v)) hx
      (fun v hv => by
        have hav : (bf.origCols up₀).avail I v := (Finset.mem_filter.mp hv).2
        have hav' : (bf.origCols Lf.up).avail I v := by rw [hup]; exact hav
        have hmem : (Sum.inl v : bf.Lab ⊕ Fin fp.Mc) ∈ mainLabelsM A.G fp.Mc (bf.origCols Lf.up)
            (cat Lf.up) I 0 (fun _ => True) d :=
          mem_mainLabelsM.mpr ⟨mem_mainLabels.mpr hav', trivial⟩
        obtain ⟨-, A', hA', hAb, hθ, hM, hq, he⟩ :=
          bf.mainLabel_source Lf.up (cat Lf.up) (hT _) (htag _) I 0 _ d hmem
        have hX : bf.vtxAt I v ∈ bf.admT.X (bf.admAt I) := bf.vtxAt_mem hav.2
        refine ⟨bf.vtxAt I v, 0, Nat.zero_le _, ⟨hX, bf.vtxAt I v, hX, ?_, ?_⟩,
          A', hA', hAb, hθ, hM, hq, he⟩
        · rw [hk]; exact hLcol _ hX
        · rw [fp.K.dist.self]; simp)
      hNt
    refine h.trans ?_
    have hsum : ∑ v ∈ Fb, ‖cb v‖ ≤
        A.colBudget * (Real.sqrt Nu + Real.sqrt (2 * A.colBudget)) * Sz := by
      set! F' : Finset (bf.Lab ⊕ Fin fp.Mc) := Fb.map ⟨Sum.inl, Sum.inl_injective⟩
      set! c' : bf.Lab ⊕ Fin fp.Mc → ℂ := Sum.elim cb 0
      have hmemF : ∀ v ∈ F', v ∈ mainLabels A.G fp.Mc (bf.origCols up₀) (cat up₀) I 0 := by
        intro w hw
        obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hw
        have hv' : (bf.origCols up₀).avail I v := (Finset.mem_filter.mp hv).2
        exact mem_mainLabels.mpr hv'
      have hc := mainCoeff_sum_le (cat up₀) I F' c'
        (fun v hv => bf.mainLabel_memLp up₀ (cat up₀) I 0 (hmemF v hv)) (by linarith)
        (fun v _ => bf.inv_mainWeight_le up₀ v)
      have e1 : ∑ v ∈ F', ‖c' v‖ = ∑ v ∈ Fb, ‖cb v‖ := by
        rw [Finset.sum_map]; rfl
      have e2 : ∑ v ∈ F', c' v • mainCol A.G fp.Mc (bf.origCols up₀) (cat up₀) I v = x up₀ := by
        rw [Finset.sum_map, hcbx]; rfl
      have e3 : F'.card = Fb.card := Finset.card_map _
      rw [e1, e2, e3] at hc
      refine hc.trans ?_
      rw [div_le_iff₀ hsr]
      have hFb : (Fb.card : ℝ) ≤ 2 * A.colBudget := bf.card_avail_le up₀ I
      have hN := Real.sqrt_le_sqrt hFb
      have hN0 := Real.sqrt_nonneg Nu
      calc Real.sqrt Fb.card * A.colBudget * ‖x up₀‖
          ≤ Real.sqrt (2 * A.colBudget) * A.colBudget *
            (Sz * Real.sqrt (dyadicGridLength A.G I.1)) := by
            gcongr
            exact hxu _
        _ ≤ A.colBudget * (Real.sqrt Nu + Real.sqrt (2 * A.colBudget)) * Sz *
            Real.sqrt (dyadicGridLength A.G I.1) := by
            have : 0 ≤ A.colBudget * Sz * Real.sqrt (dyadicGridLength A.G I.1) := by positivity
            nlinarith only [hN0, this]
    gcongr

end ActiveSetup.BasicFamilies.FamParams

namespace ActiveSetup
variable {κ : LocalKernelClass} {c₀ : ℕ} (A : ActiveSetup κ c₀)

/-- The error of one leaf of `leaf_main` with at most `D` current groups. -/
noncomputable def leafErrM (Sz Nu Nt τo τm τr τ₂ : ℝ) : ℝ :=
  (A.colBudget * (Real.sqrt Nu + Real.sqrt (2 * A.colBudget)) * Sz) *
      (((A.famVtxBound : ℝ) + 1) * (τo * Sz * Sz * Sz) + τm * Sz * Sz * Sz +
        (A.famVtxBound : ℝ) * (τ₂ * Sz * Sz * (A.colBudget * Real.sqrt Nt * Sz))) +
    (A.famVtxBound : ℝ) * (3 * ((A.colBudget * Real.sqrt Nt * Sz) * (τr * Sz * Sz * Sz)))

end ActiveSetup

namespace ActiveSetup.BasicFamilies.FamParams
variable {κ : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ c₀} {bf : A.BasicFamilies}
  (fp : bf.FamParams)

/-- The cell form of an attempt on the main columns (zero off the active cells). -/
noncomputable def Λc (I : ℤ × ℤ) :
    MultilinearMap ℂ (fun _ : Fin 4 => ColumnL2 (bf.Lab ⊕ Fin fp.Mc)) ℂ :=
  if h : I ∈ A.cells then
    cellForm (dyadicGridLength_pos A.G I.1) (A.adm I h) (bf.Lab ⊕ Fin fp.Mc) else 0

theorem Λc_of_mem {I : ℤ × ℤ} (h : I ∈ A.cells) :
    fp.Λc I = cellForm (dyadicGridLength_pos A.G I.1) (A.adm I h) (bf.Lab ⊕ Fin fp.Mc) :=
  dite_eq_left_of_eq_true (eq_true h)

/-- On an active cell the cell form is the local form of the physical parts (blueprint line 1841:
`H_I(Z_0, Z_1, Z_2, Z_3)`). -/
theorem Λc_apply {I : ℤ × ℤ} (h : I ∈ A.cells) (z : Fin 4 → ColumnL2 (bf.Lab ⊕ Fin fp.Mc)) :
    fp.Λc I z =
      localProgressionForm (dyadicGridLength A.G I.1) (A.w I) (fun l => augPhys (z l)) := by
  rw [fp.Λc_of_mem h, cellForm_apply]

open Classical in
/-- Blueprint prop:localize (lines 1838-1856) for an attempt on the main columns, summed over a
set of active cells without failed vertices: the weighted cell minima of the forms of the slot
inputs are at most the weighted minima, over the leaves of the guarded color search, of the sums
over the current groups of the forms of their ball outputs
`Z_{l,G,s} = L_{l,G,s} B_{l,s} z_l`, plus the weighted leaf errors (the cell minimum distributes
over the leaves by eq:min-subadd). -/
theorem localized_sum (cat : Fin 4 → List (CatCol bf.Vtx))
    (hT : ∀ l, ∀ e ∈ cat l, ∃ R ∈ residueBox (bf.vtag e.tag).dim 9, ∃ γ : ℝ,
      e = templateCol (bf.vtag e.tag) l R γ e.birth e.rank e.tag)
    (htag : ∀ l, ∀ e ∈ cat l, bf.occAvail e.tag.2.1 e.tag.1)
    (cs : Finset (ℤ × ℤ)) (hcs : cs ⊆ A.cells)
    (x : ℤ × ℤ → Fin 4 → ColumnL2 (bf.Lab ⊕ Fin fp.Mc)) {τ : ℕ → ℝ}
    (hpass : ∀ I ∈ cs, ∀ l (w : fp.TestName I Unit), (fp.testOf l I (fun _ => x I l) w).Pass
      A.G (bf.origCols l) I A.csrc A.Hsrc bf.vtag (A.w I)
        (τ (fp.testOf l I (fun _ => x I l) w).r) fp.mH (cat l))
    (hsucc : ∀ I ∈ cs, ∀ w ∈ bf.admT.X (bf.admAt I),
      fp.K.Success (fp.K.colorData (bf.admT.st (bf.admAt I)) w))
    (hLcol : ∀ I ∈ cs, ∀ w ∈ bf.admT.X (bf.admAt I),
      fp.K.color bf.admT A.famVtxBound (bf.admAt I) w ≤ fp.Lc)
    {fuel : ℕ} {up₀ : Fin 4}
    (hbasic : ∀ I ∈ cs, ∃ cb : bf.Lab → ℂ, x I up₀ = ∑ v ∈ Finset.univ.filter
      (fun v => (bf.origCols up₀).avail I v), cb v •
        mainCol A.G fp.Mc (bf.origCols up₀) (cat up₀) I (Sum.inl v))
    (hL1 : 1 ≤ fp.Lc) (hfuel : fp.Lc - 1 < 2 ^ fuel) (hmH : fuel ≤ fp.mH)
    {τo Nu : ℕ → ℝ} {τm τr τ₂ Sz Nt η : ℝ} (hη : 0 ≤ η) (hτo : ∀ k, 0 ≤ τo k) (hτm : 0 ≤ τm)
    (hτr : 0 ≤ τr) (hτ₂ : 0 < τ₂) (hτ₂1 : τ₂ ≤ 1)
    (hHed : Real.exp (A.Dg * (1 + Real.log A.Hsrc + Real.log τ₂⁻¹) ^ A.Dg) ≤ fp.Hed)
    (hτo' : ∀ k, 1 ≤ k → k ≤ fp.Lc → τ (fp.crank (k - 1)) ≤ τo k) (hτm' : τ (fp.Lc + 1) ≤ τm)
    (hτr' : ∀ j, 2 ≤ j → j ≤ 4 → τ (fp.Lc + j) ≤ τr) (hSz0 : 0 < Sz)
    (hSz : ∀ I ∈ cs, ∀ l, ‖x I l‖ / Real.sqrt (dyadicGridLength A.G I.1) ≤ Sz) (d : bf.Vtx)
    (hNu : ∀ I ∈ cs, ∀ s < (searchList fuel fp.Lc up₀).length,
      ((mainLabelsM A.G fp.Mc (bf.origCols (leafAt fuel fp.Lc up₀ s).up)
        (cat (leafAt fuel fp.Lc up₀ s).up) I (fp.crank (leafAt fuel fp.Lc up₀ s).k)
          (fun y => ∃ p : Fin fp.P, fp.cmask I (leafAt fuel fp.Lc up₀ s).k (p + 1) y) d).card :
            ℝ) ≤ Nu (leafAt fuel fp.Lc up₀ s).k)
    (hNt : ∀ I ∈ cs, ∀ s < (searchList fuel fp.Lc up₀).length,
      ∀ G ∈ fp.groupsAt I (leafAt fuel fp.Lc up₀ s).k,
      ((mainLabelsM A.G fp.Mc (bf.origCols (thirdSlot (leafAt fuel fp.Lc up₀ s).up
        (leafAt fuel fp.Lc up₀ s).low)) (cat (thirdSlot (leafAt fuel fp.Lc up₀ s).up
          (leafAt fuel fp.Lc up₀ s).low)) I (fp.Lc + 1)
            (fun y => ∃ p : Fin fp.P, fp.bmask I G 1 (p + 1) y) d).card : ℝ) ≤ Nt) :
    ∑ I ∈ cs, dyadicGridLength A.G I.1 * min η ‖fp.Λc I (x I)‖ ≤
      ∑ s ∈ Finset.range (searchList fuel fp.Lc up₀).length, ∑ I ∈ cs,
          dyadicGridLength A.G I.1 * min η ‖∑ G ∈ fp.groupsAt I (leafAt fuel fp.Lc up₀ s).k,
            fp.Λc I (fun l => fp.ballFilt l (cat l) I G ((leafAt fuel fp.Lc up₀ s).role l)
              (fp.inputL cat I (x I) (leafAt fuel fp.Lc up₀ s).layers l))‖ +
        ∑ I ∈ cs, dyadicGridLength A.G I.1 *
          ∑ s ∈ Finset.range (searchList fuel fp.Lc up₀).length,
            A.leafErrM Sz (Nu (leafAt fuel fp.Lc up₀ s).k) Nt (τo (leafAt fuel fp.Lc up₀ s).k)
              τm τr τ₂ := by
  refine search_cell_min cs (fun I => dyadicGridLength A.G I.1)
    (fun I => (dyadicGridLength_pos A.G I.1).le) hη fp.Λc
    (fun I l m => fp.cumFilt l (cat l) I m) x fuel fp.Lc up₀
    (fun I s => ∑ G ∈ fp.groupsAt I (leafAt fuel fp.Lc up₀ s).k,
      fp.Λc I (fun l => fp.ballFilt l (cat l) I G ((leafAt fuel fp.Lc up₀ s).role l)
        (fp.inputL cat I (x I) (leafAt fuel fp.Lc up₀ s).layers l)))
    (fun _ s => A.leafErrM Sz (Nu (leafAt fuel fp.Lc up₀ s).k) Nt
      (τo (leafAt fuel fp.Lc up₀ s).k) τm τr τ₂) (fun I hI s hs => ?_)
  have hsL : s < (searchList fuel fp.Lc up₀).length := Finset.mem_range.mp hs
  have hIc := hcs hI
  obtain ⟨-, hk1, hkL, -⟩ := leafAt_facts (up₀ := up₀) hL1 hfuel hsL
  have hm := fp.leaf_main cat hT htag hIc (x I) (hpass I hI) (hsucc I hI) (hLcol I hI)
    (hbasic I hI) hL1 hfuel hmH hsL (hτo _) hτm hτr hτ₂ hτ₂1 hHed (hτo' _ hk1 hkL) hτm' hτr'
    hSz0 (hSz I hI) d (hNu I hI s hsL) (hNt I hI s hsL)
  simp only [fp.Λc_of_mem hIc]
  refine hm.trans ?_
  have hGc : ((fp.groupsAt I (leafAt fuel fp.Lc up₀ s).k).card : ℝ) ≤ A.famVtxBound := by
    exact_mod_cast fp.card_groupsAt_le I _
  have := hτ₂.le
  have := hτo (leafAt fuel fp.Lc up₀ s).k
  have hcb := A.two_le_colBudget
  have hNu0 := Real.sqrt_nonneg (Nu (leafAt fuel fp.Lc up₀ s).k)
  have hNt0 := Real.sqrt_nonneg Nt
  unfold ActiveSetup.leafErrM
  gcongr

end ActiveSetup.BasicFamilies.FamParams

/-! ### The localized sum of an attempt on the main columns (blueprint prop:localize, line 1854) -/

/-- The arithmetic of the leaf error (blueprint line 1854): with the coefficient sum of the upper
guard at most `2 C a S`, the thresholds `τ₃ / (D a)`, `τ₃ / (D b)`, `τ₃ / (D c)` of
eq:catalog-test for path counts `a² ≤ b² ≤ c²`, the pair threshold `τ₂ = τ₃ / (D² c²)` and
`C ≤ D`, each expansion cost is canceled and the leaf error is at most `9 (D + 1) τ₃ S⁴`. -/
theorem leafErr_core {Cs D a b c cc τ₃ Sz ColSum : ℝ} (hCs : 0 < Cs) (hCD : Cs ≤ D) (ha : 0 < a)
    (hab : a ≤ b) (hbc : b ≤ c) (hcc : cc = c ^ 2) (hτ₃ : 0 < τ₃) (hSz : 0 < Sz)
    (hCol : ColSum ≤ 2 * Cs * a * Sz) :
    ColSum * ((D + 1) * (τ₃ / (D * a) * Sz * Sz * Sz) + τ₃ / (D * b) * Sz * Sz * Sz +
        D * (τ₃ / (D ^ 2 * cc) * Sz * Sz * (Cs * c * Sz))) +
      D * (3 * ((Cs * c * Sz) * (τ₃ / (D * c) * Sz * Sz * Sz))) ≤ 9 * (D + 1) * τ₃ * Sz ^ 4 := by
  subst hcc
  have hD : 0 < D := lt_of_lt_of_le hCs hCD
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hc : 0 < c := lt_of_lt_of_le hb hbc
  have hCD' : Cs / D ≤ 1 := (div_le_one hD).mpr hCD
  have hab' : a / b ≤ 1 := (div_le_one hb).mpr hab
  have hac' : a / c ≤ 1 := (div_le_one hc).mpr (hab.trans hbc)
  have hCs0 : 0 ≤ Cs / D := by positivity
  have h1 : ColSum * ((D + 1) * (τ₃ / (D * a) * Sz * Sz * Sz)) ≤ 2 * (D + 1) * τ₃ * Sz ^ 4 := by
    calc ColSum * ((D + 1) * (τ₃ / (D * a) * Sz * Sz * Sz))
        ≤ (2 * Cs * a * Sz) * ((D + 1) * (τ₃ / (D * a) * Sz * Sz * Sz)) :=
          mul_le_mul_of_nonneg_right hCol (by positivity)
      _ = 2 * (Cs / D) * ((D + 1) * τ₃ * Sz ^ 4) := by field_simp
      _ ≤ 2 * 1 * ((D + 1) * τ₃ * Sz ^ 4) := by gcongr
      _ = 2 * (D + 1) * τ₃ * Sz ^ 4 := by ring
  have h2 : ColSum * (τ₃ / (D * b) * Sz * Sz * Sz) ≤ 2 * τ₃ * Sz ^ 4 := by
    calc ColSum * (τ₃ / (D * b) * Sz * Sz * Sz)
        ≤ (2 * Cs * a * Sz) * (τ₃ / (D * b) * Sz * Sz * Sz) :=
          mul_le_mul_of_nonneg_right hCol (by positivity)
      _ = 2 * (Cs / D) * (a / b) * (τ₃ * Sz ^ 4) := by field_simp
      _ ≤ 2 * 1 * 1 * (τ₃ * Sz ^ 4) := by gcongr
      _ = 2 * τ₃ * Sz ^ 4 := by ring
  have h3 : ColSum * (D * (τ₃ / (D ^ 2 * c ^ 2) * Sz * Sz * (Cs * c * Sz))) ≤
      2 * D * τ₃ * Sz ^ 4 := by
    calc ColSum * (D * (τ₃ / (D ^ 2 * c ^ 2) * Sz * Sz * (Cs * c * Sz)))
        ≤ (2 * Cs * a * Sz) * (D * (τ₃ / (D ^ 2 * c ^ 2) * Sz * Sz * (Cs * c * Sz))) :=
          mul_le_mul_of_nonneg_right hCol (by positivity)
      _ = 2 * D * ((Cs / D) * (Cs / D)) * (a / c) * (τ₃ * Sz ^ 4) := by field_simp
      _ ≤ 2 * D * (1 * 1) * 1 * (τ₃ * Sz ^ 4) := by gcongr
      _ = 2 * D * τ₃ * Sz ^ 4 := by ring
  have h4 : D * (3 * ((Cs * c * Sz) * (τ₃ / (D * c) * Sz * Sz * Sz))) ≤ 3 * D * τ₃ * Sz ^ 4 := by
    calc D * (3 * ((Cs * c * Sz) * (τ₃ / (D * c) * Sz * Sz * Sz)))
        = 3 * D * (Cs / D) * (τ₃ * Sz ^ 4) := by field_simp
      _ ≤ 3 * D * 1 * (τ₃ * Sz ^ 4) := by gcongr
      _ = 3 * D * τ₃ * Sz ^ 4 := by ring
  have e : ColSum * ((D + 1) * (τ₃ / (D * a) * Sz * Sz * Sz) + τ₃ / (D * b) * Sz * Sz * Sz +
        D * (τ₃ / (D ^ 2 * c ^ 2) * Sz * Sz * (Cs * c * Sz))) =
      ColSum * ((D + 1) * (τ₃ / (D * a) * Sz * Sz * Sz)) +
        ColSum * (τ₃ / (D * b) * Sz * Sz * Sz) +
        ColSum * (D * (τ₃ / (D ^ 2 * c ^ 2) * Sz * Sz * (Cs * c * Sz))) := by ring
  rw [e]
  have : 0 ≤ τ₃ * Sz ^ 4 := by positivity
  nlinarith only [hCs, hCD, h1, h2, h3, h4, this]

namespace ActiveSetup.BasicFamilies.FamParams
variable {κ : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ c₀} {bf : A.BasicFamilies}
  (fp : bf.FamParams)

/-- The leaf error with the thresholds of eq:catalog-test at the path counts `n` and the pair
threshold `τ₂ = τ₃ / (D² n_{L+1})` is at most `9 (D + 1) τ₃ S⁴` (blueprint line 1854). -/
theorem leafErrM_le {τ₃ Sz : ℝ} (hτ₃ : 0 < τ₃) (hSz0 : 0 < Sz) {n : ℕ → ℝ}
    (hn0 : 2 * A.colBudget ≤ n 0) (hmono : Monotone n) {k : ℕ} (hk1 : 1 ≤ k) (hkL : k ≤ fp.Lc) :
    A.leafErrM Sz (n (fp.crank k)) (n (fp.Lc + 1))
        (catThreshold A.famVtxBound τ₃ n (fp.crank (k - 1)))
        (catThreshold A.famVtxBound τ₃ n (fp.Lc + 1))
        (catThreshold A.famVtxBound τ₃ n (fp.Lc + 2))
        (τ₃ / ((A.famVtxBound : ℝ) ^ 2 * n (fp.Lc + 1))) ≤
      9 * ((A.famVtxBound : ℝ) + 1) * τ₃ * Sz ^ 4 := by
  have hcb := A.two_le_colBudget
  have hCD := A.colBudget_le_famVtxBound
  have hn0' : 0 < n 0 := by linarith
  have hpos : ∀ r, 0 < n r := fun r => lt_of_lt_of_le hn0' (hmono (Nat.zero_le r))
  have e1 : fp.crank (k - 1) - 1 = fp.crank k := by unfold crank; omega
  have e2 : fp.Lc + 1 - 1 = fp.Lc := by omega
  have e3 : fp.Lc + 2 - 1 = fp.Lc + 1 := by omega
  have ha : 0 < Real.sqrt (n (fp.crank k)) := Real.sqrt_pos.mpr (hpos _)
  have hab : Real.sqrt (n (fp.crank k)) ≤ Real.sqrt (n fp.Lc) :=
    Real.sqrt_le_sqrt (hmono (by unfold crank; omega))
  have hbc : Real.sqrt (n fp.Lc) ≤ Real.sqrt (n (fp.Lc + 1)) := Real.sqrt_le_sqrt (hmono (by omega))
  have hc2 : n (fp.Lc + 1) = Real.sqrt (n (fp.Lc + 1)) ^ 2 := (Real.sq_sqrt (hpos _).le).symm
  have hcol : A.colBudget * (Real.sqrt (n (fp.crank k)) + Real.sqrt (2 * A.colBudget)) * Sz ≤
      2 * A.colBudget * Real.sqrt (n (fp.crank k)) * Sz := by
    have h1 : Real.sqrt (2 * A.colBudget) ≤ Real.sqrt (n (fp.crank k)) :=
      Real.sqrt_le_sqrt (hn0.trans (hmono (Nat.zero_le _)))
    have : 0 ≤ A.colBudget * Sz := by positivity
    nlinarith only [h1, this]
  unfold ActiveSetup.leafErrM catThreshold
  rw [e1, e2, e3]
  exact leafErr_core (by linarith) hCD ha hab hbc hc2 hτ₃ hSz0 hcol

end ActiveSetup.BasicFamilies.FamParams

/-- The original main columns do not depend on the catalog. -/
theorem mainCol_inl_indep {V : Type} [Fintype V] {Tg : Type*} (G : RealDyadicGrid) (Mc : ℕ)
    (O : OrigCols V Tg) (s s' : List (CatCol Tg)) (I : ℤ × ℤ) (v : V) :
    mainCol G Mc O s I (Sum.inl v) = mainCol G Mc O s' I (Sum.inl v) := by
  unfold mainCol
  exact wColumn_congr rfl rfl

namespace ActiveSetup.BasicFamilies.FamParams
variable {κ : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ c₀} {bf : A.BasicFamilies}
  (fp : bf.FamParams)

open Classical in
/-- Blueprint prop:localize (lines 1838-1856) for an attempt on the main columns. For slot inputs
`z_l` that are augmented vectors supported on the active cells without template coordinates, the
catalog closure (lem:closure) at the thresholds `τ₃ / (D √n_{r-1})` of eq:catalog-test gives slot
catalogs of same-tag templates passing all named tests, and then, on every set of active cells of
path multiplicity at most `M_p` without failed vertices whose colors are at most `L` and whose basic
guard slot input is a combination of its original columns, with local input sizes at most `S`:
the weighted cell minima of the forms of the slot inputs are at most the sum over the leaves of
the guarded color search of the weighted minima of the current-group sums
`Σ_G H_I(Z_{0,G,s}, …, Z_{3,G,s})`, `Z_{l,G,s} = L_{l,G,s} B_{l,s} z_l` (one positive smeared ball
filter after a shared product of cumulative filters or complements), plus
`Σ|I| · #leaves · 9 (D + 1) τ₃ S⁴`. The pair threshold is `τ₂ = τ₃ / (D² n_{L+1})`, chosen after
the main count (line 1854), and `H_ed` is large for it (lem:graph). The catalogs also satisfy
the closure counts of lem:closure (ranks at most `L + 5`, at most `n_r` main labels of rank at most
`r` at cells in at most `M_p` active cells, length at most `#cells · T`), which give the main
budget of line 1859. -/
theorem attempt_localization (Tc : Finset (ℤ × ℤ)) (hTc : Tc ⊆ A.cells) {Dst : ℕ}
    (hst : SameTagBound κ A.csrc Dst)
    (x : ℤ × ℤ → Fin 4 → ColumnL2 (bf.Lab ⊕ Fin fp.Mc))
    (hxb : ∀ l, ∀ I ∈ Tc, MainFresh fp.Mc 0 (x I l) ∧
      ∀ᵐ y ∂volume, y ∉ dyadicGridCell A.G I.1 I.2 →
        (x I l : ℝ → ColumnHilbert (bf.Lab ⊕ Fin fp.Mc)) y = 0)
    {Kt : ℕ} (hKt : ∀ I, Fintype.card (fp.TestName I Unit) ≤ Kt) {Mp : ℕ} (hMp : 1 ≤ Mp)
    {τ₃ : ℝ} (hτ₃ : 0 < τ₃) (hτ₃1 : τ₃ ≤ 1) {Tmax : ℕ} (n : ℕ → ℝ)
    (hn0 : 2 * A.colBudget ≤ n 0)
    (hratio : ∀ r, (1 + (fp.Lc + 6) * Mp * closureRatio A.famVtxBound Kt fp.mH Tmax
      (Real.exp (Dst * (1 + Real.log A.Hsrc) ^ Dst)) τ₃) * n r ≤ n (r + 1))
    (hT : n (fp.Lc + 5) ≤ Tmax) (hMc : Tc.card * Tmax ≤ fp.Mc)
    {fuel : ℕ} {up₀ : Fin 4} (hL1 : 1 ≤ fp.Lc) (hfuel : fp.Lc - 1 < 2 ^ fuel)
    (hmH : fuel ≤ fp.mH)
    (hHed : Real.exp (A.Dg * (1 + Real.log A.Hsrc +
      Real.log (τ₃ / ((A.famVtxBound : ℝ) ^ 2 * n (fp.Lc + 1)))⁻¹) ^ A.Dg) ≤ fp.Hed)
    (d : bf.Vtx) :
    ∃ cat : Fin 4 → List (CatCol bf.Vtx),
      (∀ l, (∀ I ∈ Tc, ∀ w : fp.TestName I Unit, (fp.testOf l I (fun _ : Unit => x I l) w).Pass
          A.G (bf.origCols l) I A.csrc A.Hsrc bf.vtag (A.w I)
            (catThreshold A.famVtxBound τ₃ n (fp.testOf l I (fun _ : Unit => x I l) w).r) fp.mH
              (cat l)) ∧
        (∀ e ∈ cat l, e.birth ∈ Tc ∧ e.rank ≤ fp.Lc + 5 ∧
          ∃ R ∈ residueBox (bf.vtag e.tag).dim 9, ∃ γ : ℝ,
            e = templateCol (bf.vtag e.tag) l R γ e.birth e.rank e.tag) ∧
        (∀ e ∈ cat l, bf.occAvail e.tag.2.1 e.tag.1) ∧
        (∀ I, (Tc.filter fun I' : ℤ × ℤ =>
            dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G I'.1 I'.2).card ≤ Mp →
          ∀ r ≤ fp.Lc + 5, ((mainLabels A.G fp.Mc (bf.origCols l) (cat l) I r).card : ℝ) ≤ n r) ∧
        (cat l).length ≤ Tc.card * Tmax) ∧
      ∀ cs ⊆ Tc, (∀ I ∈ cs, (Tc.filter fun I' : ℤ × ℤ =>
          dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G I'.1 I'.2).card ≤ Mp) →
        (∀ I ∈ cs, ∀ w ∈ bf.admT.X (bf.admAt I),
          fp.K.Success (fp.K.colorData (bf.admT.st (bf.admAt I)) w)) →
        (∀ I ∈ cs, ∀ w ∈ bf.admT.X (bf.admAt I),
          fp.K.color bf.admT A.famVtxBound (bf.admAt I) w ≤ fp.Lc) →
        (∀ I ∈ cs, ∃ cb : bf.Lab → ℂ, x I up₀ = ∑ v ∈ Finset.univ.filter
          (fun v => (bf.origCols up₀).avail I v), cb v •
            mainCol A.G fp.Mc (bf.origCols up₀) [] I (Sum.inl v)) →
        ∀ {Sz η : ℝ}, 0 ≤ η → 0 < Sz →
        (∀ I ∈ cs, ∀ l, ‖x I l‖ / Real.sqrt (dyadicGridLength A.G I.1) ≤ Sz) →
        ∑ I ∈ cs, dyadicGridLength A.G I.1 * min η ‖fp.Λc I (x I)‖ ≤
          ∑ s ∈ Finset.range (searchList fuel fp.Lc up₀).length, ∑ I ∈ cs,
              dyadicGridLength A.G I.1 * min η ‖∑ G ∈ fp.groupsAt I (leafAt fuel fp.Lc up₀ s).k,
                fp.Λc I (fun l => fp.ballFilt l (cat l) I G ((leafAt fuel fp.Lc up₀ s).role l)
                  (fp.inputL cat I (x I) (leafAt fuel fp.Lc up₀ s).layers l))‖ +
            (∑ I ∈ cs, dyadicGridLength A.G I.1) * ((searchList fuel fp.Lc up₀).length *
              (9 * ((A.famVtxBound : ℝ) + 1) * τ₃ * Sz ^ 4)) := by
  classical
  obtain ⟨cat, hcat⟩ := fp.main_closure Tc hTc hst A.exp_two_le_Hsrc (fun _ I => fp.TestName I Unit)
    (fun l I => fp.testOf l I (fun _ => x I l)) (fun l I w => fp.testOf_t l I _ w)
    (fun l I w => fp.testOf_r l I _ w) (fun l I hI w => hxb l I hI) (fun _ I => hKt I) hMp hτ₃ n
    hn0 hratio hT hMc
  have htag0 : ∀ l, ∀ e ∈ cat l, bf.occAvail e.tag.2.1 e.tag.1 := by
    intro l e he
    obtain ⟨hb, ⟨w, -, hM⟩, -⟩ := (hcat l).2.1 e he
    refine bf.occAvail_of_mem (c := bf.admAt e.birth) ?_
    rcases hw : w.2.1 with ⟨m, h⟩ | ⟨v, h⟩
    · have hM' : fp.maskOf e.birth w.2.1 e.tag := hM
      rw [hw] at hM'
      exact hM'.1
    · have hM' : fp.maskOf e.birth w.2.1 e.tag := hM
      rw [hw] at hM'
      exact hM'.1
  refine ⟨cat, fun l => ⟨(hcat l).1, fun e he => ⟨((hcat l).2.1 e he).1, ?_,
    ((hcat l).2.1 e he).2.2⟩, htag0 l, (hcat l).2.2.2.1, (hcat l).2.2.2.2⟩, ?_⟩
  · obtain ⟨w, hw, -⟩ := ((hcat l).2.1 e he).2.1
    rw [hw]
    exact (fp.testOf_r l e.birth _ w).2
  intro cs hcs hmult hsucc hLcol hbasic Sz η hη hSz0 hSz
  -- the path counts
  have hcb := A.two_le_colBudget
  have hn0' : 0 < n 0 := by linarith
  set Kc := closureRatio A.famVtxBound Kt fp.mH Tmax
    (Real.exp (Dst * (1 + Real.log A.Hsrc) ^ Dst)) τ₃ with hKc
  have hKc0 : 0 ≤ Kc := closureRatio_nonneg _ _ _ _ _ _
  have hX0 : 0 ≤ (fp.Lc + 6 : ℝ) * Mp * Kc := by positivity
  have hpos : ∀ r, 0 < n r := by
    intro r
    induction r with
    | zero => exact hn0'
    | succ r ih => exact lt_of_lt_of_le (mul_pos (by linarith) ih) (hratio r)
  have hmono : Monotone n := monotone_nat_of_le_succ fun r =>
    le_trans (le_mul_of_one_le_left (hpos r).le (by linarith)) (hratio r)
  have hDv : (0 : ℝ) < A.famVtxBound := by exact_mod_cast A.one_le_famVtxBound
  -- the templates of the catalogs and their tags
  have hT' : ∀ l, ∀ e ∈ cat l, ∃ R ∈ residueBox (bf.vtag e.tag).dim 9, ∃ γ : ℝ,
      e = templateCol (bf.vtag e.tag) l R γ e.birth e.rank e.tag := fun l e he =>
    ((hcat l).2.1 e he).2.2
  have htag : ∀ l, ∀ e ∈ cat l, bf.occAvail e.tag.2.1 e.tag.1 := by
    intro l e he
    obtain ⟨hb, ⟨w, -, hM⟩, -⟩ := (hcat l).2.1 e he
    refine bf.occAvail_of_mem (c := bf.admAt e.birth) ?_
    rcases hw : w.2.1 with ⟨m, h⟩ | ⟨v, h⟩
    · have hM' : fp.maskOf e.birth w.2.1 e.tag := hM
      rw [hw] at hM'
      exact hM'.1
    · have hM' : fp.maskOf e.birth w.2.1 e.tag := hM
      rw [hw] at hM'
      exact hM'.1
  -- the pair threshold
  set τ₂ := τ₃ / ((A.famVtxBound : ℝ) ^ 2 * n (fp.Lc + 1)) with hτ₂def
  have hτ₂ : 0 < τ₂ := div_pos hτ₃ (mul_pos (by positivity) (hpos _))
  have hτ₂1 : τ₂ ≤ 1 := by
    rw [div_le_one (mul_pos (by positivity) (hpos _))]
    have h1 : (1 : ℝ) ≤ (A.famVtxBound : ℝ) ^ 2 :=
      one_le_pow₀ (by exact_mod_cast A.one_le_famVtxBound)
    have h2 : (1 : ℝ) ≤ n (fp.Lc + 1) := by
      have := hmono (Nat.zero_le (fp.Lc + 1)); linarith
    nlinarith only [hτ₃1, h1, h2]
  -- the catalog thresholds are antitone
  have hanti : ∀ {r r' : ℕ}, r ≤ r' → catThreshold A.famVtxBound τ₃ n r' ≤
      catThreshold A.famVtxBound τ₃ n r := fun {r r'} h => by
    unfold catThreshold
    apply div_le_div_of_nonneg_left hτ₃.le (mul_pos hDv (Real.sqrt_pos.mpr (hpos _)))
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hmono (by omega))) hDv.le
  have hτnn : ∀ r, 0 ≤ catThreshold A.famVtxBound τ₃ n r := fun r => by
    unfold catThreshold; positivity
  -- the localized sum
  have h := fp.localized_sum cat hT' htag cs (hcs.trans hTc) x
    (τ := catThreshold A.famVtxBound τ₃ n)
    (fun I hI l w => (hcat l).1 I (hcs hI) w) hsucc hLcol
    (fun I hI => by
      obtain ⟨cb, hcb'⟩ := hbasic I hI
      refine ⟨cb, hcb'.trans (Finset.sum_congr rfl fun v _ => ?_)⟩
      rw [mainCol_inl_indep])
    hL1 hfuel hmH (τo := fun k => catThreshold A.famVtxBound τ₃ n (fp.crank (k - 1)))
    (Nu := fun k => n (fp.crank k)) (τm := catThreshold A.famVtxBound τ₃ n (fp.Lc + 1))
    (τr := catThreshold A.famVtxBound τ₃ n (fp.Lc + 2)) (Nt := n (fp.Lc + 1)) hη
    (fun k => hτnn _) (hτnn _) (hτnn _) hτ₂ hτ₂1 hHed (fun k _ _ => le_rfl) le_rfl
    (fun j hj2 _ => hanti (by omega)) hSz0 hSz d
    (fun I hI s hs => by
      have hk := (leafAt_facts (up₀ := up₀) hL1 hfuel hs).2.2.1
      refine le_trans (Nat.cast_le.mpr (Finset.card_le_card (mainLabelsM_subset _ _ _ _ _)))
        ((hcat _).2.2.2.1 I (hmult I hI) _ ?_)
      unfold crank; omega)
    (fun I hI s hs G _ => le_trans (Nat.cast_le.mpr (Finset.card_le_card
      (mainLabelsM_subset _ _ _ _ _))) ((hcat _).2.2.2.1 I (hmult I hI) _ (by omega)))
  refine h.trans (add_le_add le_rfl ?_)
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun I _ => mul_le_mul_of_nonneg_left ?_
    (dyadicGridLength_pos A.G I.1).le
  refine (Finset.sum_le_card_nsmul _ _ (9 * ((A.famVtxBound : ℝ) + 1) * τ₃ * Sz ^ 4)
    fun s hs => ?_).trans (by rw [Finset.card_range, nsmul_eq_mul])
  obtain ⟨-, hk1, hkL, -⟩ := leafAt_facts (up₀ := up₀) hL1 hfuel (Finset.mem_range.mp hs)
  exact fp.leafErrM_le hτ₃ hSz0 hn0 hmono hk1 hkL

end ActiveSetup.BasicFamilies.FamParams


/-! ## Basic-slot histories on the main columns (blueprint line 1859) -/

/-! ### Generic compression and locality lemmas (moved from Sec13_3) -/

/-- A projection onto vectors fixed by a self-adjoint restriction ignores the restriction. -/
theorem starProjection_restrict_eq {V : Type*} [Fintype V] (K : Submodule ℂ (ColumnL2 V))
    [K.HasOrthogonalProjection] (s : Set ℝ) (hs : MeasurableSet s)
    (hK : ∀ v ∈ K, columnL2Restriction s hs v = v) (w : ColumnL2 V) :
    K.starProjection (columnL2Restriction s hs w) = K.starProjection w := by
  have hperp : w - columnL2Restriction s hs w ∈ Kᗮ := by
    rw [Submodule.mem_orthogonal]
    intro v hv
    rw [inner_sub_right, ← columnL2Restriction_inner, hK v hv, sub_self]
  have h0 : K.starProjection (w - columnL2Restriction s hs w) = 0 := by
    rw [Submodule.starProjection_apply, K.orthogonalProjectionOnto_apply_of_mem_orthogonal hperp]
    rfl
  rw [map_sub, sub_eq_zero] at h0
  exact h0.symm


/-- The span of column functions vanishing off `J` is fixed by the restriction to `J ⊆ s`. -/
theorem span_vanish_restrict {V : Type*} [Fintype V] {J s : Set ℝ} (hJs : J ⊆ s)
    (hs : MeasurableSet s) (S : Set (ColumnL2 V))
    (hS : ∀ v ∈ S, ∀ᵐ y ∂volume, y ∉ J → (v : ℝ → ColumnHilbert V) y = 0) :
    ∀ v ∈ Submodule.span ℂ S, columnL2Restriction s hs v = v := by
  intro v hv
  have hle : Submodule.span ℂ S ≤
      LinearMap.eqLocus (columnL2Restriction s hs).toLinearMap LinearMap.id := by
    rw [Submodule.span_le]
    intro w hw
    change columnL2Restriction s hs w = w
    refine columnL2Restriction_eq_self s hs w ?_
    filter_upwards [hS w hw] with y hy hys
    exact hy fun hyJ => hys (hJs hyJ)
  exact hle hv

section Commute
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem opAvg_commute {P : ℕ} (Q : Fin P → E →L[ℂ] E) (r : E →L[ℂ] E)
    (h : ∀ p, (Q p).comp r = r.comp (Q p)) : (opAvg Q).comp r = r.comp (opAvg Q) := by
  have hp : ∀ p x, Q p (r x) = r (Q p x) := fun p x => DFunLike.congr_fun (h p) x
  refine ContinuousLinearMap.ext fun x => ?_
  simp only [ContinuousLinearMap.comp_apply, opAvg, smul_apply, FunLike.coe_sum,
    Finset.sum_apply, hp, map_smul, map_sum]

theorem layerOp_commute (Cum : ℕ → E →L[ℂ] E) (r : E →L[ℂ] E)
    (h : ∀ m, (Cum m).comp r = r.comp (Cum m)) (ls : List (ℕ × Bool)) :
    (layerOp Cum ls).comp r = r.comp (layerOp Cum ls) := by
  induction ls using List.reverseRecOn with
  | nil => simp [layerOp_nil]
  | append_singleton l a ih =>
    rw [layerOp_append, ContinuousLinearMap.comp_assoc, ih, ← ContinuousLinearMap.comp_assoc,
      ← ContinuousLinearMap.comp_assoc]
    congr 1
    split_ifs
    · rw [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub, h,
        ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id]
    · exact h _

end Commute

/-! ### Compression of the outer main ball projection (blueprint lines 2068-2070) -/

/-- The one-factor compression constant of `columnSpatialCompression`. -/
noncomputable abbrev compression1 {V : Type*} [Fintype V] (D : ColumnTreeData V) : ℝ :=
  compressionOneConst D

theorem compression1_nonneg {V : Type*} [Fintype V] (D : ColumnTreeData V) :
    0 ≤ compression1 D := by
  unfold compression1 compressionOneConst; have := columnBudget_log_one_le D; positivity

/-- Blueprint lines 2068-2070 (`lem:compression` with one factor): rows `Q_k` local to decision
cells `u_k` and Bessel with constant `c` remain Bessel after inserting the inherited projection at
their decision cells, with constant `c · C₁²`. -/
theorem rows_projection_compression {V κ F : Type*} [Fintype V] [NormedAddCommGroup F]
    [NormedSpace ℂ F] (D : ColumnTreeData V) (A : InheritedColumnMask D) (s : Finset κ)
    (u : κ → ℤ × ℤ) (hu : ∀ k, u k ∈ D.cells) (Q : κ → ColumnL2 V →L[ℂ] F) {c : ℝ} (hc : 0 ≤ c)
    (hQ : ∀ x, ∑ k ∈ s, ‖Q k x‖ ^ 2 ≤ c * ‖x‖ ^ 2)
    (hloc : ∀ k ∈ s, (Q k).comp (columnL2Restriction (dyadicGridCell D.grid (u k).1 (u k).2)
      (dyadicGridCell_measurable D.grid (u k).1 (u k).2)) = Q k) (z : ColumnL2 V) :
    ∑ k ∈ s, ‖Q k (cellColumnProjection D A (hu k) z)‖ ^ 2 ≤
      c * compression1 D ^ 2 * ‖z‖ ^ 2 := by
  rcases hc.eq_or_lt with hc0 | hcpos
  · -- vanishing rows
    have h0 : ∀ k ∈ s, ∀ x, Q k x = 0 := by
      intro k hk x
      have h := hQ x
      rw [← hc0, zero_mul] at h
      have hk' := Finset.single_le_sum (f := fun k => ‖Q k x‖ ^ 2)
        (fun _ _ => sq_nonneg _) hk
      have : ‖Q k x‖ ^ 2 ≤ 0 := hk'.trans h
      exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp (le_antisymm this (sq_nonneg _)))
    rw [Finset.sum_eq_zero fun k hk => by rw [h0 k hk, norm_zero, zero_pow two_ne_zero], ← hc0]
    simp
  set! r : ℝ := (Real.sqrt c)⁻¹
  have hr0 : 0 < Real.sqrt c := Real.sqrt_pos.mpr hcpos
  let B : ColumnRowFamily D {k // k ∈ s} F :=
    { decision := fun k => u k.1
      decision_mem := fun k => hu k.1
      row := fun k => (r : ℂ) • Q k.1
      bound := 1
      bound_nonneg := zero_le_one
      square_sum := fun x => by
        have h := hQ x
        rw [← Finset.sum_coe_sort s] at h
        calc ∑ k : {k // k ∈ s}, ‖((r : ℂ) • Q k.1) x‖ ^ 2 =
            r ^ 2 * ∑ k : {k // k ∈ s}, ‖Q k.1 x‖ ^ 2 := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun k _ => ?_
              rw [smul_apply, norm_smul, mul_pow, Complex.norm_real,
                Real.norm_eq_abs, sq_abs]
          _ ≤ r ^ 2 * (c * ‖x‖ ^ 2) := mul_le_mul_of_nonneg_left h (sq_nonneg _)
          _ = 1 ^ 2 * ‖x‖ ^ 2 := by
              simp only [r, inv_pow, Real.sq_sqrt hc]; field_simp
      input_locality := fun k => by
        rw [ContinuousLinearMap.smul_comp, hloc k.1 k.2] }
  have h := columnSpatialCompression D (fun _ => A) 1 z B le_rfl
  have hsq := pow_le_pow_left₀ (finiteRowNorm_nonneg _) h 2
  rw [finiteRowNorm_sq] at hsq
  have hrow : ∀ k : {k // k ∈ s},
      ‖B.row k (cellColumnProduct D (fun _ => A) (B.decision_mem k) 1 z)‖ ^ 2 =
      r ^ 2 * ‖Q k.1 (cellColumnProjection D A (hu k.1) z)‖ ^ 2 := by
    intro k
    simp only [B, cellColumnProduct, ContinuousLinearMap.comp_id, smul_apply,
      norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  simp only [hrow] at hsq
  rw [← Finset.mul_sum,
    Finset.sum_coe_sort s (fun k => ‖Q k (cellColumnProjection D A (hu k) z)‖ ^ 2)] at hsq
  have hr2 : r ^ 2 = c⁻¹ := by simp only [r, inv_pow, Real.sq_sqrt hc]
  rw [hr2] at hsq
  have := mul_le_mul_of_nonneg_left hsq hc
  rw [← mul_assoc, mul_inv_cancel₀ hcpos.ne', one_mul] at this
  rw [mul_pow, ← mul_assoc] at this
  exact this

/-- The row-space triangle inequality for averages (blueprint line 2069, "restore its average"):
a row bound for each averaged operator persists for the average. -/
theorem rows_opAvg_le {H F κ : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup F] [NormedSpace ℂ F] {P : ℕ} (hP : 0 < P) (s : Finset κ)
    (T : κ → Fin P → H →L[ℂ] H) (Q : κ → H →L[ℂ] F) (z : H) {B : ℝ}
    (hB : ∀ p, ∑ k ∈ s, ‖Q k (T k p z)‖ ^ 2 ≤ B) :
    ∑ k ∈ s, ‖Q k (opAvg (T k) z)‖ ^ 2 ≤ B := by
  have hP' : (0 : ℝ) < P := by exact_mod_cast hP
  have hpt : ∀ k, ‖Q k (opAvg (T k) z)‖ ^ 2 ≤ (P : ℝ)⁻¹ * ∑ p, ‖Q k (T k p z)‖ ^ 2 := by
    intro k
    have e : Q k (opAvg (T k) z) = (P : ℂ)⁻¹ • ∑ p, Q k (T k p z) := by
      simp [opAvg, map_sum]
    rw [e, norm_smul, mul_pow, norm_inv, Complex.norm_natCast]
    have hsum : ‖∑ p, Q k (T k p z)‖ ^ 2 ≤ P * ∑ p, ‖Q k (T k p z)‖ ^ 2 := by
      refine (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2).trans ?_
      have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin P)))
        (f := fun p => ‖Q k (T k p z)‖)
      simpa using this
    calc (P : ℝ)⁻¹ ^ 2 * ‖∑ p, Q k (T k p z)‖ ^ 2 ≤
        (P : ℝ)⁻¹ ^ 2 * (P * ∑ p, ‖Q k (T k p z)‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = (P : ℝ)⁻¹ * ∑ p, ‖Q k (T k p z)‖ ^ 2 := by field_simp
  calc ∑ k ∈ s, ‖Q k (opAvg (T k) z)‖ ^ 2 ≤
      ∑ k ∈ s, (P : ℝ)⁻¹ * ∑ p, ‖Q k (T k p z)‖ ^ 2 := Finset.sum_le_sum fun k _ => hpt k
    _ = (P : ℝ)⁻¹ * ∑ p, ∑ k ∈ s, ‖Q k (T k p z)‖ ^ 2 := by
        rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ (P : ℝ)⁻¹ * ∑ _p : Fin P, B :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun p _ => hB p) (by positivity)
    _ = B := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; field_simp

section LayerExpansion
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-! ### Averaged cumulative layers as averages of complement products (lines 2072-2074) -/

/-- The factors of the expanded layer product for a pad tuple `ω`. -/
noncomputable def layerFactor {P : ℕ} (Pf : ℕ → Fin P → H →L[ℂ] H) (ls : List (ℕ × Bool))
    (ω : Fin ls.length → Fin P) (l : ℕ) : H →L[ℂ] H :=
  if h : l < ls.length then Pf (ls[l]).1 (ω ⟨l, h⟩) else 0

/-- The complement pattern of a layer list. -/
def layerPattern (ls : List (ℕ × Bool)) (l : ℕ) : Bool :=
  if h : l < ls.length then (ls[l]).2 else false

/-- Blueprint lines 2072-2074 ("expand complements ... retain averages as averages"): a layer
product of pad averages is the uniform average over pad tuples of complement products. -/
theorem layerOp_opAvg_expand {P : ℕ} (hP : 0 < P) (Pf : ℕ → Fin P → H →L[ℂ] H)
    (ls : List (ℕ × Bool)) (x : H) :
    layerOp (fun m => opAvg (Pf m)) ls x = ((P : ℂ) ^ ls.length)⁻¹ •
      ∑ ω : Fin ls.length → Fin P,
        operatorComplementProduct (layerFactor Pf ls ω) (layerPattern ls) ls.length x := by
  induction ls using List.reverseRecOn generalizing x with
  | nil => simp [layerOp_nil, operatorComplementProduct]
  | append_singleton l a ih =>
    have hP' : (P : ℂ) ≠ 0 := by exact_mod_cast hP.ne'
    rw [layerOp_append, ContinuousLinearMap.comp_apply, ih]
    set! n := l.length
    have hlen : (l ++ [a]).length = n + 1 := by simp [n]
    -- the last factor as an average
    have hlast : (if a.2 then ContinuousLinearMap.id ℂ H - opAvg (Pf a.1) else opAvg (Pf a.1)) =
        opAvg (fun p => if a.2 then ContinuousLinearMap.id ℂ H - Pf a.1 p else Pf a.1 p) := by
      split_ifs
      · exact id_sub_opAvg hP _
      · rfl
    rw [hlast]
    -- the pad tuples of the longer list
    let e : (Fin n → Fin P) × Fin P ≃ (Fin (l ++ [a]).length → Fin P) :=
      (Fin.snocEquiv (fun _ => Fin P)).symm.symm.trans
        (Equiv.piCongrLeft' (fun _ => Fin P) (finCongr hlen.symm)) |>.trans (Equiv.refl _)
      |> fun e0 => (Equiv.prodComm _ _).trans e0
    rw [← e.sum_comp, Fintype.sum_prod_type]
    have hsc : ((P : ℂ) ^ (l ++ [a]).length)⁻¹ = ((P : ℂ) ^ (n + 1))⁻¹ := by rw [hlen]
    rw [hsc]
    have hterm : ∀ (ω : Fin n → Fin P) (p : Fin P),
        operatorComplementProduct (layerFactor Pf (l ++ [a]) (e (ω, p))) (layerPattern (l ++ [a]))
          (l ++ [a]).length x =
        (if a.2 then ContinuousLinearMap.id ℂ H - Pf a.1 p else Pf a.1 p)
          (operatorComplementProduct (layerFactor Pf l ω) (layerPattern l) n x) := by
      intro ω p
      rw [congrArg (fun m => operatorComplementProduct (layerFactor Pf (l ++ [a]) (e (ω, p)))
        (layerPattern (l ++ [a])) m x) hlen]
      simp only [operatorComplementProduct, ContinuousLinearMap.comp_apply]
      have hn : n < (l ++ [a]).length := by rw [hlen]; omega
      have hget : (l ++ [a])[n] = a := by simp [n]
      have heval : ∀ (j : ℕ) (hj : j < (l ++ [a]).length), e (ω, p) ⟨j, hj⟩ =
          if h : j < n then ω ⟨j, h⟩ else p := by
        intro j hj
        simp [e, Equiv.piCongrLeft', Fin.snoc, Fin.castLT]
      have hpat : layerPattern (l ++ [a]) n = a.2 := by
        simp only [layerPattern, hn, ↓reduceDIte, hget]
      have hfac : layerFactor Pf (l ++ [a]) (e (ω, p)) n = Pf a.1 p := by
        simp only [layerFactor, hn, ↓reduceDIte, hget, heval, lt_irrefl]
      rw [hpat, hfac]
      congr 1
      refine congrFun (congrArg _ (operatorComplementProduct_congr₂ n fun j hj => ⟨?_, ?_⟩)) x
      · have hj' : j < (l ++ [a]).length := by omega
        have hjl : j < l.length := hj
        simp only [layerFactor, hj', hjl, heval, hj, ↓reduceDIte]
        congr 2
        exact List.getElem_append_left hjl
      · have hj' : j < (l ++ [a]).length := by omega
        have hjl : j < l.length := hj
        simp only [layerPattern, hj', hjl, ↓reduceDIte]
        congr 1
        exact List.getElem_append_left hjl
    simp_rw [hterm]
    simp only [opAvg, smul_apply, FunLike.coe_sum, Finset.sum_apply,
      map_smul, map_sum, Finset.smul_sum, smul_smul]
    refine Finset.sum_congr rfl fun ω _ => Finset.sum_congr rfl fun p _ => ?_
    congr 1
    rw [pow_succ, mul_inv]

end LayerExpansion

/-! ### Compression of averaged cumulative histories (blueprint lines 2072-2075) -/

/-- The complement-compression constant of `columnSpatialCompression_complements` for `n`
factors. -/
noncomputable def compressionC {V : Type*} [Fintype V] (D : ColumnTreeData V) (n : ℕ) : ℝ :=
  (1024 * ((n : ℝ) + 1) ^ 1024 * Real.log (2 * D.budget)) ^ (1024 * (n + 1))

theorem compressionC_nonneg {V : Type*} [Fintype V] (D : ColumnTreeData V) (n : ℕ) :
    0 ≤ compressionC D n := by
  unfold compressionC; have := columnBudget_log_one_le D; positivity

/-- Rows bounded for each member of a uniform average over a finite set remain bounded for the
average. -/
theorem rows_uniformAvg_le {H F ι Ω : Type*} [NormedAddCommGroup H] [NormedAddCommGroup F]
    [NormedSpace ℂ H] [NormedSpace ℂ F] [Fintype ι] [Fintype Ω] [Nonempty Ω]
    (R : ι → H →L[ℂ] F) (X : ι → Ω → H) {B : ℝ}
    (hB : ∀ ω, ∑ i, ‖R i (X i ω)‖ ^ 2 ≤ B) :
    ∑ i, ‖R i (((Fintype.card Ω : ℂ))⁻¹ • ∑ ω, X i ω)‖ ^ 2 ≤ B := by
  have hc : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
  have hpt : ∀ i, ‖R i (((Fintype.card Ω : ℂ))⁻¹ • ∑ ω, X i ω)‖ ^ 2 ≤
      ((Fintype.card Ω : ℝ))⁻¹ * ∑ ω, ‖R i (X i ω)‖ ^ 2 := by
    intro i
    rw [map_smul, map_sum, norm_smul, mul_pow, norm_inv, Complex.norm_natCast]
    have hsum : ‖∑ ω, R i (X i ω)‖ ^ 2 ≤ Fintype.card Ω * ∑ ω, ‖R i (X i ω)‖ ^ 2 := by
      refine (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2).trans ?_
      have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset Ω))
        (f := fun ω => ‖R i (X i ω)‖)
      simpa using this
    calc ((Fintype.card Ω : ℝ))⁻¹ ^ 2 * ‖∑ ω, R i (X i ω)‖ ^ 2 ≤
        ((Fintype.card Ω : ℝ))⁻¹ ^ 2 * (Fintype.card Ω * ∑ ω, ‖R i (X i ω)‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = ((Fintype.card Ω : ℝ))⁻¹ * ∑ ω, ‖R i (X i ω)‖ ^ 2 := by field_simp
  calc ∑ i, ‖R i (((Fintype.card Ω : ℂ))⁻¹ • ∑ ω, X i ω)‖ ^ 2 ≤
      ∑ i, ((Fintype.card Ω : ℝ))⁻¹ * ∑ ω, ‖R i (X i ω)‖ ^ 2 :=
        Finset.sum_le_sum fun i _ => hpt i
    _ = ((Fintype.card Ω : ℝ))⁻¹ * ∑ ω, ∑ i, ‖R i (X i ω)‖ ^ 2 := by
        rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ ((Fintype.card Ω : ℝ))⁻¹ * ∑ _ω : Ω, B :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun ω _ => hB ω) (by positivity)
    _ = B := by rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; field_simp

/-- Blueprint lines 2072-2075 (`lem:compression` with complements and averages): rows local to
their decision cells and Bessel with constant `B` remain Bessel after inserting the averaged
cumulative layers at their decision cells, at the complement-compression cost. -/
theorem rows_layer_compression {V F ι : Type*} [Fintype V] [NormedAddCommGroup F]
    [NormedSpace ℂ F] [Fintype ι] (D : ColumnTreeData V) (ls : List (ℕ × Bool)) {P : ℕ}
    (hP : 0 < P) (A : ℕ → Fin P → InheritedColumnMask D) (u : ι → ℤ × ℤ)
    (hu : ∀ i, u i ∈ D.cells) (Pf : ι → ℕ → Fin P → ColumnL2 V →L[ℂ] ColumnL2 V)
    (hPf : ∀ i m p, Pf i m p = cellColumnProjection D (A m p) (hu i))
    (R : ι → ColumnL2 V →L[ℂ] F) {B : ℝ} (hB : 0 ≤ B) (hR : ∀ x, ∑ i, ‖R i x‖ ^ 2 ≤ B * ‖x‖ ^ 2)
    (hloc : ∀ i, (R i).comp (columnL2Restriction (dyadicGridCell D.grid (u i).1 (u i).2)
      (dyadicGridCell_measurable D.grid (u i).1 (u i).2)) = R i) (z : ColumnL2 V) :
    ∑ i, ‖R i (layerOp (fun m => opAvg (Pf i m)) ls z)‖ ^ 2 ≤
      B * compressionC D ls.length ^ 2 * ‖z‖ ^ 2 := by
  rcases hB.eq_or_lt with hB0 | hBpos
  · -- vanishing rows
    have h0 : ∀ i x, R i x = 0 := by
      intro i x
      have h := hR x
      rw [← hB0, zero_mul] at h
      have hk' := Finset.single_le_sum (f := fun i => ‖R i x‖ ^ 2)
        (fun _ _ => sq_nonneg _) (Finset.mem_univ i)
      have : ‖R i x‖ ^ 2 ≤ 0 := hk'.trans h
      exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp (le_antisymm this (sq_nonneg _)))
    simp [h0, ← hB0]
  set n := ls.length
  have : Nonempty (Fin n → Fin P) := ⟨fun _ => ⟨0, hP⟩⟩
  have hcard : (Fintype.card (Fin n → Fin P) : ℂ) = (P : ℂ) ^ n := by
    simp
  have hexp : ∀ i, layerOp (fun m => opAvg (Pf i m)) ls z =
      ((Fintype.card (Fin n → Fin P) : ℂ))⁻¹ • ∑ ω : Fin n → Fin P,
        operatorComplementProduct (layerFactor (Pf i) ls ω) (layerPattern ls) n z := by
    intro i
    rw [hcard]; exact layerOp_opAvg_expand hP (Pf i) ls z
  simp_rw [hexp]
  refine rows_uniformAvg_le R _ fun ω => ?_
  -- one pad tuple: compression with complements
  set! Aω : ℕ → InheritedColumnMask D := fun l =>
    if h : l < n then A (ls[l]).1 (ω ⟨l, h⟩) else A 0 ⟨0, hP⟩
  have hfac : ∀ i, operatorComplementProduct (layerFactor (Pf i) ls ω) (layerPattern ls) n =
      operatorComplementProduct (fun l => cellColumnProjection D (Aω l) (hu i))
        (layerPattern ls) n := by
    intro i
    refine operatorComplementProduct_congr _ n fun l hl => ?_
    have hl' : l < ls.length := hl
    simp only [layerFactor, Aω, hl', hl, ↓reduceDIte, hPf]
  simp_rw [hfac]
  set! r : ℝ := (Real.sqrt B)⁻¹
  have hr0 : 0 < Real.sqrt B := Real.sqrt_pos.mpr hBpos
  let Bf : ColumnRowFamily D ι F :=
    { decision := u
      decision_mem := hu
      row := fun i => (r : ℂ) • R i
      bound := 1
      bound_nonneg := zero_le_one
      square_sum := fun x => by
        calc ∑ i, ‖((r : ℂ) • R i) x‖ ^ 2 = r ^ 2 * ∑ i, ‖R i x‖ ^ 2 := by
              rw [Finset.mul_sum]
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [smul_apply, norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
          _ ≤ r ^ 2 * (B * ‖x‖ ^ 2) := mul_le_mul_of_nonneg_left (hR x) (sq_nonneg _)
          _ = 1 ^ 2 * ‖x‖ ^ 2 := by
              simp only [r, inv_pow, Real.sq_sqrt hB]; field_simp
      input_locality := fun i => by
        rw [ContinuousLinearMap.smul_comp, hloc i] }
  have h := columnSpatialCompression_complements D Aω (layerPattern ls) n z Bf le_rfl
  have hsq := pow_le_pow_left₀ (finiteRowNorm_nonneg _) h 2
  rw [finiteRowNorm_sq] at hsq
  have hrow : ∀ i, ‖Bf.row i (operatorComplementProduct
      (fun l => cellColumnProjection D (Aω l) (Bf.decision_mem i)) (layerPattern ls) n z)‖ ^ 2 =
      r ^ 2 * ‖R i (operatorComplementProduct (fun l => cellColumnProjection D (Aω l) (hu i))
        (layerPattern ls) n z)‖ ^ 2 := by
    intro i
    simp only [Bf, smul_apply, norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  simp only [hrow] at hsq
  rw [← Finset.mul_sum] at hsq
  have hr2 : r ^ 2 = B⁻¹ := by simp only [r, inv_pow, Real.sq_sqrt hB]
  rw [hr2] at hsq
  have := mul_le_mul_of_nonneg_left hsq hB
  rw [← mul_assoc, mul_inv_cancel₀ hBpos.ne', one_mul, mul_pow, ← mul_assoc] at this
  exact this

section DepthBlocks
variable {V : Type*} [Fintype V]

theorem columnL2Restriction_idem (s : Set ℝ) (hs : MeasurableSet s) :
    (columnL2Restriction (V := V) s hs).comp (columnL2Restriction s hs) =
      columnL2Restriction s hs :=
  columnL2Restriction_comp_of_subset hs hs subset_rfl

theorem ColumnDepthFamily.proj_adjoint (Ψ : ColumnDepthFamily V) (h : ℤ) :
    ContinuousLinearMap.adjoint (Ψ.proj h) = Ψ.proj h :=
  (Ψ.isStarProjection_proj h).isSelfAdjoint.adjoint_eq

/-- On a cell of the depth-`h` partition, the depth projection is the cell projection, on both
sides. -/
theorem ColumnDepthFamily.restrict_proj (Ψ : ColumnDepthFamily V) (h : ℤ) {Q : ℤ × ℤ}
    (hQ : Q ∈ (Ψ.partition h).cells) :
    (columnL2Restriction (dyadicGridCell Ψ.D.grid Q.1 Q.2)
      (dyadicGridCell_measurable Ψ.D.grid Q.1 Q.2)).comp (Ψ.proj h) =
        cellColumnProjection Ψ.D Ψ.A ((Ψ.partition h).subset hQ) ∧
    (Ψ.proj h).comp (columnL2Restriction (dyadicGridCell Ψ.D.grid Q.1 Q.2)
      (dyadicGridCell_measurable Ψ.D.grid Q.1 Q.2)) =
        cellColumnProjection Ψ.D Ψ.A ((Ψ.partition h).subset hQ) := by
  have hm := dyadicGridCell_measurable Ψ.D.grid Q.1 Q.2
  have h1 : (columnL2Restriction (dyadicGridCell Ψ.D.grid Q.1 Q.2) hm).comp (Ψ.proj h) =
      cellColumnProjection Ψ.D Ψ.A ((Ψ.partition h).subset hQ) := by
    refine ContinuousLinearMap.ext fun z => Lp.ext ?_
    simp only [ContinuousLinearMap.comp_apply]
    change (columnL2Indicator _ hm (Ψ.proj h z) : ℝ → ColumnHilbert V) =ᵐ[volume] _
    have hae := (ae_restrict_iff' hm).mp (Ψ.proj_ae_cell h z hQ)
    filter_upwards [columnL2Indicator_coeFn _ hm (Ψ.proj h z), hae,
      cellColumnRange_ae_zero_off Ψ.D Ψ.A ((Ψ.partition h).subset hQ)
        (cellColumnProjection_mem Ψ.D Ψ.A ((Ψ.partition h).subset hQ) z)] with y h1 h2 h3
    rw [h1]
    by_cases hy : y ∈ dyadicGridCell Ψ.D.grid Q.1 Q.2
    · rw [Set.indicator_of_mem hy]; exact h2 hy
    · rw [Set.indicator_of_notMem hy]; exact (h3 hy).symm
  refine ⟨h1, ?_⟩
  have h2 := congrArg ContinuousLinearMap.adjoint h1
  rwa [ContinuousLinearMap.adjoint_comp, cellColumnProjection_adjoint,
    columnL2Restriction_adjoint, Ψ.proj_adjoint] at h2

end DepthBlocks

section Intertwine
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem layerOp_intertwine (C C' : ℕ → E →L[ℂ] E) (r : E →L[ℂ] E)
    (h : ∀ m, r.comp (C m) = (C' m).comp r) (ls : List (ℕ × Bool)) :
    r.comp (layerOp C ls) = (layerOp C' ls).comp r := by
  induction ls using List.reverseRecOn with
  | nil => simp [layerOp_nil]
  | append_singleton l a ih =>
    rw [layerOp_append, layerOp_append, ← ContinuousLinearMap.comp_assoc,
      ContinuousLinearMap.comp_assoc _ (layerOp C' l), ← ih, ← ContinuousLinearMap.comp_assoc]
    congr 1
    split_ifs
    · rw [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub, h,
        ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id]
    · exact h _

theorem opAvg_intertwine {P : ℕ} (Q Q' : Fin P → E →L[ℂ] E) (r : E →L[ℂ] E)
    (h : ∀ p, r.comp (Q p) = (Q' p).comp r) : r.comp (opAvg Q) = (opAvg Q').comp r := by
  have hp : ∀ p x, r (Q p x) = Q' p (r x) := fun p x => DFunLike.congr_fun (h p) x
  refine ContinuousLinearMap.ext fun x => ?_
  simp only [ContinuousLinearMap.comp_apply, opAvg, smul_apply, FunLike.coe_sum,
    Finset.sum_apply, hp, map_smul, map_sum]

end Intertwine

section GlobalHistories
variable {V F : Type*} [Fintype V] [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Blueprint lines 1879-1890 (compression for global histories): rows that split orthogonally
over the cells of their depth partition and are Bessel with constant `B` remain Bessel after
inserting the global averaged histories of their depths, at the complement-compression cost. -/
theorem globHist_compression {ι : Type*} [Fintype ι] (Ψ : ColumnDepthFamily V) {P : ℕ}
    (hP : 0 < P) (Am : ℕ → Fin P → InheritedColumnMask Ψ.D) (ls : List (ℕ × Bool))
    (d : ι → ℤ) (R : ι → ColumnL2 V →L[ℂ] F) {B : ℝ} (hB : 0 ≤ B)
    (hR : ∀ x, ∑ i, ‖R i x‖ ^ 2 ≤ B * ‖x‖ ^ 2)
    (hblk : ∀ i x, ‖R i x‖ ^ 2 = ∑ Q : {Q // Q ∈ (Ψ.partition (d i)).cells},
      ‖R i (columnL2Restriction (dyadicGridCell Ψ.D.grid Q.1.1 Q.1.2)
        (dyadicGridCell_measurable Ψ.D.grid Q.1.1 Q.1.2) x)‖ ^ 2) (z : ColumnL2 V) :
    ∑ i, ‖R i (globHist Ψ Am ls (d i) z)‖ ^ 2 ≤ B * compressionC Ψ.D ls.length ^ 2 * ‖z‖ ^ 2 := by
  set! ι' := Σ i, {Q // Q ∈ (Ψ.partition (d i)).cells}
  set! rs : ι' → ColumnL2 V →L[ℂ] ColumnL2 V := fun k =>
    columnL2Restriction (dyadicGridCell Ψ.D.grid k.2.1.1 k.2.1.2)
      (dyadicGridCell_measurable Ψ.D.grid k.2.1.1 k.2.1.2)
  set! R' : ι' → ColumnL2 V →L[ℂ] F := fun k => (R k.1).comp (rs k)
  have hu : ∀ k : ι', k.2.1 ∈ Ψ.D.cells := fun k => (Ψ.partition (d k.1)).subset k.2.2
  have hsum : ∀ (f : ι' → ℝ), ∑ k, f k = ∑ i, ∑ Q : {Q // Q ∈ (Ψ.partition (d i)).cells},
      f ⟨i, Q⟩ := fun f => Fintype.sum_sigma f
  have hR' : ∀ x, ∑ k, ‖R' k x‖ ^ 2 ≤ B * ‖x‖ ^ 2 := by
    intro x
    rw [hsum]
    simp only [R', rs, ContinuousLinearMap.comp_apply]
    simp_rw [← hblk]
    exact hR x
  have hloc : ∀ k, (R' k).comp (columnL2Restriction (dyadicGridCell Ψ.D.grid k.2.1.1 k.2.1.2)
      (dyadicGridCell_measurable Ψ.D.grid k.2.1.1 k.2.1.2)) = R' k := by
    intro k
    change ((R k.1).comp (rs k)).comp (rs k) = (R k.1).comp (rs k)
    rw [ContinuousLinearMap.comp_assoc]
    exact congrArg (fun T => (R k.1).comp T) (columnL2Restriction_idem _ _)
  have hc := rows_layer_compression Ψ.D ls hP Am (fun k : ι' => k.2.1) hu
    (fun k m p => cellColumnProjection Ψ.D (Am m p) (hu k)) (fun _ _ _ => rfl) R' hB hR' hloc z
  refine le_of_eq_of_le ?_ hc
  rw [hsum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hblk]
  refine Finset.sum_congr rfl fun Q _ => ?_
  -- the global history restricted to a partition cell is the local history
  have hcell : ∀ m (p : Fin P), (rs ⟨i, Q⟩).comp ((Ψ.withMask (Am m p)).proj (d i)) =
      (cellColumnProjection Ψ.D (Am m p) (hu ⟨i, Q⟩)).comp (rs ⟨i, Q⟩) := by
    intro m p
    have h := (Ψ.withMask (Am m p)).restrict_proj (d i) (Q := Q.1) Q.2
    have h' := cellColumnProjection_restrict Ψ.D (Am m p) (hu ⟨i, Q⟩)
    exact h.1.trans h'.2.symm
  have hcom : ∀ m (p : Fin P), (cellColumnProjection Ψ.D (Am m p) (hu ⟨i, Q⟩)).comp (rs ⟨i, Q⟩) =
      (rs ⟨i, Q⟩).comp (cellColumnProjection Ψ.D (Am m p) (hu ⟨i, Q⟩)) := by
    intro m p
    have h' := cellColumnProjection_restrict Ψ.D (Am m p) (hu ⟨i, Q⟩)
    exact h'.2.trans h'.1.symm
  have hint := layerOp_intertwine _ (fun m => opAvg fun p =>
    cellColumnProjection Ψ.D (Am m p) (hu ⟨i, Q⟩)) (rs ⟨i, Q⟩)
    (fun m => opAvg_intertwine _ _ _ fun p => hcell m p) ls
  have hcomm := layerOp_commute (fun m => opAvg fun p =>
    cellColumnProjection Ψ.D (Am m p) (hu ⟨i, Q⟩)) (rs ⟨i, Q⟩)
    (fun m => opAvg_commute _ _ fun p => hcom m p) ls
  simp only [R', ContinuousLinearMap.comp_apply]
  refine congrArg (fun v => ‖R i v‖ ^ 2) ?_
  change (rs ⟨i, Q⟩) (globHist Ψ Am ls (d i) z) = _
  rw [← ContinuousLinearMap.comp_apply (rs ⟨i, Q⟩)]
  unfold globHist
  rw [hint, ContinuousLinearMap.comp_apply, ← ContinuousLinearMap.comp_apply
    (layerOp _ ls) (rs ⟨i, Q⟩), hcomm]
  rfl

end GlobalHistories

/-! ### Relabeling of column spaces (blueprint line 1859: histories acting on `F_l`) -/

section Relabel
variable {V W : Type*} [Fintype V] [Fintype W]

open scoped Classical in
/-- The pointwise relabeling of augmented vectors along an injection of labels: the physical
coordinate is kept and the private coordinate of `v` is moved to `f v`. -/
noncomputable def relabelCLM (f : V → W) : ColumnHilbert V →L[ℂ] ColumnHilbert W :=
  ∑ o : Option V, (EuclideanSpace.proj o : ColumnHilbert V →L[ℂ] ℂ).smulRight
    (EuclideanSpace.single (Option.map f o) (1 : ℂ))

open scoped Classical in
theorem relabelCLM_apply (f : V → W) (z : ColumnHilbert V) :
    relabelCLM f z = ∑ o : Option V, z o • EuclideanSpace.single (Option.map f o) (1 : ℂ) := by
  simp [relabelCLM]

open scoped Classical in
theorem norm_relabelCLM {f : V → W} (hf : Function.Injective f) (z : ColumnHilbert V) :
    ‖relabelCLM f z‖ = ‖z‖ := by
  have hinj : Function.Injective (Option.map f) := Option.map_injective hf
  have hon : Orthonormal ℂ fun o : Option V =>
      EuclideanSpace.single (Option.map f o) (1 : ℂ) :=
    EuclideanSpace.orthonormal_single.comp _ hinj
  rw [relabelCLM_apply]
  have h1 : ‖∑ o : Option V, z o • EuclideanSpace.single (Option.map f o) (1 : ℂ)‖ ^ 2 =
      ∑ o : Option V, ‖z o‖ ^ 2 := by
    rw [← @inner_self_eq_norm_sq ℂ, hon.inner_sum, map_sum]
    refine Finset.sum_congr rfl fun o _ => ?_
    rw [RCLike.conj_mul]
    norm_cast
  have h2 : ‖z‖ ^ 2 = ∑ o : Option V, ‖z o‖ ^ 2 := EuclideanSpace.norm_sq_eq z
  rw [← h2] at h1
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h1

/-- The relabeling of column inputs along an injection of labels. -/
noncomputable def colRelabel (f : V → W) : ColumnL2 V →L[ℂ] ColumnL2 W :=
  (relabelCLM f).compLpL 2 volume

theorem colRelabel_coeFn (f : V → W) (z : ColumnL2 V) :
    (colRelabel f z : ℝ → ColumnHilbert W) =ᵐ[volume] fun y => relabelCLM f (z y) :=
  ContinuousLinearMap.coeFn_compLp _ z

theorem norm_colRelabel {f : V → W} (hf : Function.Injective f) (z : ColumnL2 V) :
    ‖colRelabel f z‖ = ‖z‖ := by
  have h : ‖colRelabel f z‖ ^ 2 = ‖z‖ ^ 2 := by
    rw [columnInput_norm_sq_integral, columnInput_norm_sq_integral]
    refine integral_congr_ae ?_
    filter_upwards [colRelabel_coeFn f z] with y hy
    rw [hy, norm_relabelCLM hf]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp h

/-- The relabeling as a linear isometry. -/
noncomputable def colRelabelLI {f : V → W} (hf : Function.Injective f) :
    ColumnL2 V →ₗᵢ[ℂ] ColumnL2 W where
  toLinearMap := (colRelabel f).toLinearMap
  norm_map' := norm_colRelabel hf

end Relabel

/-- An isometric embedding transports orthogonal projections onto finite-dimensional subspaces:
the projection onto the image of `K` of the image of `x` is the image of the projection of `x`. -/
theorem starProjection_map_isometry {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] (ι : E →ₗᵢ[ℂ] F) (K : Submodule ℂ E)
    [FiniteDimensional ℂ K] [FiniteDimensional ℂ (K.map ι.toLinearMap)] (x : E) :
    (K.map ι.toLinearMap).starProjection (ι x) = ι (K.starProjection x) := by
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    (Submodule.mem_map_of_mem (Submodule.starProjection_apply_mem K x)) ?_
  rintro w ⟨w', hw', rfl⟩
  rw [← map_sub]
  change inner ℂ (ι (x - K.starProjection x)) (ι w') = 0
  rw [LinearIsometry.inner_map_map]
  exact Submodule.inner_left_of_mem_orthogonal hw' (Submodule.sub_starProjection_mem_orthogonal x)

section RelabelColumns
variable {V W : Type*} [Fintype V] [Fintype W]

/-- Relabeling a private column value moves its private coordinate. -/
theorem relabelCLM_privateColumnValue {f : V → W} {φ : V → ℝ → ℂ} {ε : V → ℝ}
    {φ' : W → ℝ → ℂ} {ε' : W → ℝ} {v : V} (hφ : φ' (f v) = φ v) (hε : ε' (f v) = ε v) (y : ℝ) :
    relabelCLM f (privateColumnValue φ ε v y) = privateColumnValue φ' ε' (f v) y := by
  classical
  rw [relabelCLM_apply]
  unfold privateColumnValue
  rw [Fintype.sum_option]
  simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.single_apply, Option.map_none, Option.map_some,
    smul_eq_mul, mul_one, mul_zero, add_zero, reduceCtorEq, ↓reduceIte, Option.some.injEq]
  rw [Finset.sum_eq_single v]
  · simp only [hφ, hε, ↓reduceIte]
    simp
  · intro b _ hb
    simp [hb]
  · simp

/-- Relabeling a weighted column gives the weighted column of the image label. -/
theorem colRelabel_wColumn {f : V → W} {s : Set ℝ} {φ : V → ℝ → ℂ} {ε : V → ℝ}
    {φ' : W → ℝ → ℂ} {ε' : W → ℝ} {v : V} (hφ : φ' (f v) = φ v) (hε : ε' (f v) = ε v)
    (hmem : MemLp (s.indicator (privateColumnValue φ ε v)) 2 volume)
    (hmem' : MemLp (s.indicator (privateColumnValue φ' ε' (f v))) 2 volume) :
    colRelabel f (wColumn s φ ε v) = wColumn s φ' ε' (f v) := by
  refine Lp.ext ?_
  filter_upwards [colRelabel_coeFn f (wColumn s φ ε v), wColumn_coeFn hmem, wColumn_coeFn hmem']
    with y h1 h2 h3
  rw [h1, h2, h3]
  by_cases hy : y ∈ s
  · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, relabelCLM_privateColumnValue hφ hε]
  · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, map_zero]

end RelabelColumns

/-- A cell column of a column tree is a weighted column. -/
theorem cellColumnLp_eq_wColumn {V : Type*} [Fintype V] (D : ColumnTreeData V)
    (A : InheritedColumnMask D) {c : ℤ × ℤ} (hc : c ∈ D.cells) (v : {v // v ∈ A.labels c}) :
    cellColumnLp D A hc v =
      wColumn (dyadicGridCell D.grid c.1 c.2) D.scalar D.privateWeight v.1 := by
  refine Lp.ext ?_
  filter_upwards [cellColumnLp_coeFn D A hc v, wColumn_coeFn (cellColumn_memLp D A hc v.2)]
    with y h1 h2
  rw [h1, h2]

/-- The image of a cell range of a column tree under a relabeling is the span of the relabeled
weighted columns. -/
theorem cellColumnRange_map_relabel {V W : Type*} [Fintype V] [Fintype W]
    (D : ColumnTreeData V) (A : InheritedColumnMask D) {c : ℤ × ℤ} (hc : c ∈ D.cells)
    {f : V → W} {φ' : W → ℝ → ℂ} {ε' : W → ℝ} (hφ : ∀ v, φ' (f v) = D.scalar v)
    (hε : ∀ v, ε' (f v) = D.privateWeight v)
    (hmem' : ∀ v ∈ A.labels c, MemLp ((dyadicGridCell D.grid c.1 c.2).indicator
      (privateColumnValue φ' ε' (f v))) 2 volume) :
    (cellColumnRange D A hc).map (colRelabel f).toLinearMap =
      Submodule.span ℂ ((fun v : {v // v ∈ A.labels c} =>
        wColumn (dyadicGridCell D.grid c.1 c.2) φ' ε' (f v.1)) '' Set.univ) := by
  unfold cellColumnRange
  rw [Submodule.map_span, ← Set.range_comp, Set.image_univ]
  congr 1
  ext x
  simp only [Set.mem_range, Function.comp_apply]
  constructor
  · rintro ⟨v, rfl⟩
    refine ⟨v, ?_⟩
    rw [cellColumnLp_eq_wColumn]
    exact (colRelabel_wColumn (hφ v.1) (hε v.1) (cellColumn_memLp D A hc v.2) (hmem' v.1 v.2)).symm
  · rintro ⟨v, rfl⟩
    refine ⟨v, ?_⟩
    rw [cellColumnLp_eq_wColumn]
    exact colRelabel_wColumn (hφ v.1) (hε v.1) (cellColumn_memLp D A hc v.2) (hmem' v.1 v.2)

/-! ### The main column tree of an attempt (blueprint lines 1805, 1859) -/

namespace ActiveSetup.BasicFamilies
variable {κ : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ c₀} (bf : A.BasicFamilies)

/-- The relevant main labels of a catalog: the original basic columns available on some active
cell and the templates of the catalog. -/
def Relevant {Mc : ℕ} (s : List (CatCol bf.Vtx)) : bf.Lab ⊕ Fin Mc → Prop
  | Sum.inl x => ∃ c ∈ A.cells, bf.occAvail c x
  | Sum.inr n => (n : ℕ) < s.length

/-- The relevant main labels. -/
def RLab (Mc : ℕ) (s : List (CatCol bf.Vtx)) : Type :=
  {v : bf.Lab ⊕ Fin Mc // bf.Relevant s v}

noncomputable instance (Mc : ℕ) (s : List (CatCol bf.Vtx)) : Fintype (bf.RLab Mc s) :=
  @Fintype.ofFinite _ (inferInstanceAs (Finite {v : bf.Lab ⊕ Fin Mc // bf.Relevant s v}))

/-- The underlying main label of a relevant label. -/
def rv (Mc : ℕ) (s : List (CatCol bf.Vtx)) (v : bf.RLab Mc s) : bf.Lab ⊕ Fin Mc := v.1

theorem rv_injective (Mc : ℕ) (s : List (CatCol bf.Vtx)) : Function.Injective (bf.rv Mc s) :=
  Subtype.val_injective

/-- The family birth cell of an original label. -/
def famBirth (x : bf.Lab) : ℤ × ℤ := (bf.P x.1 x.2.1).Ψ.D.birth x.2.2

open scoped Classical in
/-- The birth cells of the relevant main labels: the family birth cell of an original column,
clamped to the attempt root, and the birth cell of a template. -/
noncomputable def mBirth {Mc : ℕ} (s : List (CatCol bf.Vtx)) (v : bf.RLab Mc s) : ℤ × ℤ :=
  match v with
  | ⟨Sum.inl x, _⟩ =>
      if dyadicGridCell A.G A.R.1 A.R.2 ⊆
        dyadicGridCell A.G (bf.famBirth x).1 (bf.famBirth x).2 then A.R else bf.famBirth x
  | ⟨Sum.inr n, h⟩ => (s[(n : ℕ)]'h).birth

/-- An original label available at a cell of the setup is available at its family birth cell. -/
theorem cell_sub_famBirth {c : ℤ × ℤ} {x : bf.Lab} (h : bf.occAvail c x) :
    dyadicGridCell A.G c.1 c.2 ⊆ dyadicGridCell A.G (bf.famBirth x).1 (bf.famBirth x).2 := by
  obtain ⟨hcD, -, -⟩ := bf.charts x.1 x.2.1 c h.1
  have := (bf.P x.1 x.2.1).Ψ.A.available c hcD x.2.2 h.2
  rw [(bf.P x.1 x.2.1).grid] at this
  exact this

theorem mBirth_inl_sub {Mc : ℕ} (s : List (CatCol bf.Vtx)) (x : bf.Lab)
    (hx : bf.Relevant (Mc := Mc) s (Sum.inl x)) :
    dyadicGridCell A.G (bf.mBirth s ⟨Sum.inl x, hx⟩).1 (bf.mBirth s ⟨Sum.inl x, hx⟩).2 ⊆
      dyadicGridCell A.G (bf.famBirth x).1 (bf.famBirth x).2 := by
  classical
  simp only [mBirth]
  split_ifs with h
  · exact h
  · exact subset_rfl

/-- An available original label's cell lies in its main birth cell. -/
theorem cell_sub_mBirth_inl {Mc : ℕ} (s : List (CatCol bf.Vtx)) {c : ℤ × ℤ} {x : bf.Lab}
    (h : bf.occAvail c x) (hx : bf.Relevant (Mc := Mc) s (Sum.inl x)) :
    dyadicGridCell A.G c.1 c.2 ⊆
      dyadicGridCell A.G (bf.mBirth s ⟨Sum.inl x, hx⟩).1 (bf.mBirth s ⟨Sum.inl x, hx⟩).2 := by
  classical
  simp only [mBirth]
  split_ifs with hR
  · exact A.sub c h.1
  · exact bf.cell_sub_famBirth h

theorem mBirth_mem_tree {Mc : ℕ} (s : List (CatCol bf.Vtx)) (hb : ∀ e ∈ s, e.birth ∈ A.cells)
    (v : bf.RLab Mc s) : bf.mBirth s v ∈ dyadicFiniteTree A.G A.R A.treeDepth := by
  classical
  obtain ⟨v | n, hv⟩ := v
  · obtain ⟨c, hc, hav⟩ := hv
    simp only [mBirth]
    split_ifs with hR
    · exact dyadicFiniteTree_root_mem A.G A.R _
    · have hcR := A.sub c hc
      have hcb := bf.cell_sub_famBirth hav
      have hbR : dyadicGridCell A.G (bf.famBirth v).1 (bf.famBirth v).2 ⊆
          dyadicGridCell A.G A.R.1 A.R.2 := by
        rcases dyadicGridCell_laminar A.G (bf.famBirth v) A.R with hd | hs | hs
        · exfalso
          have hy := dyadicGridCell_left_mem A.G c.1 c.2
          exact Set.disjoint_left.mp hd (hcb hy) (hcR hy)
        · exact hs
        · exact absurd hs hR
      refine (dyadicFiniteTree_mem_iff A.G A.R _ _).mpr ⟨hbR, ?_⟩
      have h1 := ((dyadicFiniteTree_mem_iff A.G A.R c _).mp (A.cells_mem_tree hc)).2
      have h2 := dyadicGridCell_depth_le_of_subset A.G c (bf.famBirth v) hcb
      omega
  · exact A.cells_mem_tree (hb _ (List.getElem_mem hv))

end ActiveSetup.BasicFamilies

namespace ActiveSetup.BasicFamilies
variable {κ : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ c₀} (bf : A.BasicFamilies)

open scoped Classical in
/-- The number of templates of a catalog whose birth cell contains the point `y`. -/
noncomputable def tmplPath (s : List (CatCol bf.Vtx)) (y : ℝ) : ℕ :=
  ((Finset.range s.length).filter fun n => ∃ h : n < s.length,
    y ∈ dyadicGridCell A.G (s[n]'h).birth.1 (s[n]'h).birth.2).card

/-- A main budget of a catalog of an attempt: the templates are born at active cells, and the
budget `B` dominates eight column budgets plus the template path counts (blueprint line 1835:
the common main catalog budget). -/
structure MainBudget (s : List (CatCol bf.Vtx)) where
  hb : ∀ e ∈ s, e.birth ∈ A.cells
  /-- Upper bound for the original column budget plus the template count along a path. -/
  B : ℝ
  hTp : ∀ y, 8 * A.colBudget + bf.tmplPath s y ≤ B

namespace MainBudget
variable {bf} {s : List (CatCol bf.Vtx)} (mb : bf.MainBudget s)

theorem colBudget_le : A.colBudget ≤ mb.B := by
  have h1 := mb.hTp 0
  have h2 := A.two_le_colBudget
  have h3 : (0 : ℝ) ≤ bf.tmplPath s 0 := Nat.cast_nonneg _
  linarith

theorem two_le : 2 ≤ mb.B := le_trans A.two_le_colBudget mb.colBudget_le

end MainBudget

open scoped Classical in
/-- At most eight column budgets of original columns have a main birth cell containing a point. -/
theorem card_orig_births_le {Mc : ℕ} (s : List (CatCol bf.Vtx)) (y : ℝ) :
    (((Finset.univ : Finset (bf.RLab Mc s)).filter fun v =>
      v.1.isLeft ∧ y ∈ dyadicGridCell A.G (bf.mBirth s v).1 (bf.mBirth s v).2).card : ℝ) ≤
      8 * A.colBudget := by
  set T : Finset (Σ lj : Fin 4 × Fin 2, (bf.P lj.1 lj.2).V) := Finset.univ.sigma fun lj =>
    Finset.univ.filter fun w : (bf.P lj.1 lj.2).V =>
      y ∈ dyadicGridCell A.G ((bf.P lj.1 lj.2).Ψ.D.birth w).1 ((bf.P lj.1 lj.2).Ψ.D.birth w).2
  have hinj : ((Finset.univ : Finset (bf.RLab Mc s)).filter fun v =>
      v.1.isLeft ∧ y ∈ dyadicGridCell A.G (bf.mBirth s v).1 (bf.mBirth s v).2).card ≤
      (T.map ⟨some, Option.some_injective _⟩).card := by
    refine Finset.card_le_card_of_injOn (fun v => match v.1 with
      | Sum.inl x => some (⟨(x.1, x.2.1), x.2.2⟩ : Σ lj : Fin 4 × Fin 2, (bf.P lj.1 lj.2).V)
      | Sum.inr _ => none) ?_ ?_
    · rintro ⟨x | n, hv⟩ hm
      · have hm' := (Finset.mem_filter.mp (Finset.mem_coe.mp hm)).2
        refine Finset.mem_coe.mpr (Finset.mem_map.mpr ⟨⟨(x.1, x.2.1), x.2.2⟩,
          Finset.mem_sigma.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩)
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        exact bf.mBirth_inl_sub s x hv hm'.2
      · exact absurd (Finset.mem_filter.mp (Finset.mem_coe.mp hm)).2.1 Bool.false_ne_true
    · rintro ⟨x | n, hv⟩ hm ⟨x' | n', hv'⟩ hm' he
      · simp only [Option.some.injEq] at he
        have h1 : x.1 = x'.1 := congrArg (fun p => p.1.1) he
        obtain ⟨l, j, w⟩ := x
        obtain ⟨l', j', w'⟩ := x'
        simp only at h1
        subst h1
        have h2 : j = j' := congrArg (fun p => p.1.2) he
        subst h2
        have h3 := (Sigma.mk.inj_iff.mp he).2
        rw [heq_eq_eq] at h3
        subst h3
        rfl
      · exact absurd (Finset.mem_filter.mp (Finset.mem_coe.mp hm')).2.1 Bool.false_ne_true
      · exact absurd (Finset.mem_filter.mp (Finset.mem_coe.mp hm)).2.1 Bool.false_ne_true
      · exact absurd (Finset.mem_filter.mp (Finset.mem_coe.mp hm)).2.1 Bool.false_ne_true
  rw [Finset.card_map] at hinj
  refine (Nat.cast_le.mpr hinj).trans ?_
  rw [Finset.card_sigma]
  push_cast
  calc ∑ lj : Fin 4 × Fin 2, (((Finset.univ.filter fun w : (bf.P lj.1 lj.2).V =>
        y ∈ dyadicGridCell A.G ((bf.P lj.1 lj.2).Ψ.D.birth w).1
          ((bf.P lj.1 lj.2).Ψ.D.birth w).2).card : ℕ) : ℝ)
      ≤ ∑ _lj : Fin 4 × Fin 2, A.colBudget := by
        refine Finset.sum_le_sum fun lj _ => ?_
        have h := (bf.P lj.1 lj.2).Ψ.D.path_count y
        rw [(bf.P lj.1 lj.2).grid] at h
        exact h.trans (bf.budget lj.1 lj.2)
    _ = 8 * A.colBudget := by simp

open scoped Classical in
theorem card_tmpl_births_le {Mc : ℕ} (s : List (CatCol bf.Vtx)) (y : ℝ) :
    ((Finset.univ : Finset (bf.RLab Mc s)).filter fun v =>
      ¬ v.1.isLeft ∧ y ∈ dyadicGridCell A.G (bf.mBirth s v).1 (bf.mBirth s v).2).card ≤
      bf.tmplPath s y := by
  unfold tmplPath
  refine Finset.card_le_card_of_injOn (fun v => match v.1 with
    | Sum.inl _ => 0
    | Sum.inr n => (n : ℕ)) ?_ ?_
  · rintro ⟨x | n, hv⟩ hm
    · exact absurd rfl (Finset.mem_filter.mp (Finset.mem_coe.mp hm)).2.1
    · have hm' := (Finset.mem_filter.mp (Finset.mem_coe.mp hm)).2
      have hv' : (n : ℕ) < s.length := hv
      refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hv', hv', ?_⟩)
      exact hm'.2
  · rintro ⟨x | n, hv⟩ hm ⟨x' | n', hv'⟩ hm' he
    · exact absurd rfl (Finset.mem_filter.mp (Finset.mem_coe.mp hm)).2.1
    · exact absurd rfl (Finset.mem_filter.mp (Finset.mem_coe.mp hm)).2.1
    · exact absurd rfl (Finset.mem_filter.mp (Finset.mem_coe.mp hm')).2.1
    · simp only at he
      have : n = n' := Fin.ext he
      subst this
      rfl

open scoped Classical in
/-- The main column tree of a catalog of an attempt (blueprint lines 1805, 1859): the relevant main
labels with their main scalars and private weights, born at their (clamped) family birth cells
and template birth cells, on the complete tree of the attempt, with a budget `B` that dominates
eight column budgets plus the template path counts. -/
noncomputable def mainTree (Mc : ℕ) (s : List (CatCol bf.Vtx))
    (mb : bf.MainBudget s) : ColumnTreeData (bf.RLab Mc s) where
  grid := A.G
  cells := dyadicFiniteTree A.G A.R A.treeDepth
  root := A.R
  below_root := fun c hc => ((dyadicFiniteTree_mem_iff A.G A.R c _).mp hc).1
  birth := bf.mBirth s
  birth_mem := bf.mBirth_mem_tree s mb.hb
  scalar := fun v => mainScalar Mc (bf.origCols 0) s v.1
  scalar_measurable := fun v => by
    rcases v with ⟨x | n, hv⟩
    · exact (bf.P x.1 x.2.1).Ψ.D.scalar_measurable x.2.2
    · exact catAtom_measurable s n
  privateWeight := fun v => mainWeight Mc (bf.origCols 0) v.1
  privateWeight_pos := fun v => by
    rcases v with ⟨x | n, hv⟩
    · exact (bf.P x.1 x.2.1).Ψ.D.privateWeight_pos x.2.2
    · exact one_pos
  budget := mb.B
  two_le_budget := mb.two_le
  private_lower := fun v => by
    rcases v with ⟨x | n, hv⟩
    · have h1 := (bf.P x.1 x.2.1).Ψ.D.private_lower x.2.2
      have h2 := (bf.P x.1 x.2.1).Ψ.D.two_le_budget
      have h3 : (bf.P x.1 x.2.1).Ψ.D.budget ≤ mb.B := (bf.budget x.1 x.2.1).trans mb.colBudget_le
      exact (inv_anti₀ (by linarith) h3).trans h1
    · change mb.B⁻¹ ≤ Real.sqrt 1
      rw [Real.sqrt_one]
      exact inv_le_one_of_one_le₀ (by linarith [mb.two_le])
  column_bound := fun v => by
    rcases v with ⟨x | n, hv⟩
    · have hfam := (bf.P x.1 x.2.1).Ψ.D.column_bound x.2.2
      rw [(bf.P x.1 x.2.1).grid] at hfam
      have hsub := bf.mBirth_inl_sub (Mc := Mc) s x hv
      have h3 : (bf.P x.1 x.2.1).Ψ.D.budget ≤ mb.B := (bf.budget x.1 x.2.1).trans mb.colBudget_le
      filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hfam] with y hy
      have e1 := norm_privateColumnValue_sq (fun v : bf.RLab Mc s =>
        mainScalar Mc (bf.origCols 0) s v.1) (fun v => mainWeight Mc (bf.origCols 0) v.1)
        ⟨Sum.inl x, hv⟩ y ((bf.P x.1 x.2.1).Ψ.D.privateWeight_pos x.2.2).le
      have e2 := norm_privateColumnValue_sq (bf.P x.1 x.2.1).Ψ.D.scalar
        (bf.P x.1 x.2.1).Ψ.D.privateWeight x.2.2 y
        ((bf.P x.1 x.2.1).Ψ.D.privateWeight_pos x.2.2).le
      have e : ‖privateColumnValue (fun v : bf.RLab Mc s => mainScalar Mc (bf.origCols 0) s v.1)
          (fun v => mainWeight Mc (bf.origCols 0) v.1) ⟨Sum.inl x, hv⟩ y‖ =
          ‖privateColumnValue (bf.P x.1 x.2.1).Ψ.D.scalar (bf.P x.1 x.2.1).Ψ.D.privateWeight
            x.2.2 y‖ := by
        refine (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp ?_
        rw [e1, e2]
        rfl
      rw [e]
      exact hy.trans h3
    · refine Filter.Eventually.of_forall fun y => ?_
      have e1 := norm_privateColumnValue_sq (fun v : bf.RLab Mc s =>
        mainScalar Mc (bf.origCols 0) s v.1) (fun v => mainWeight Mc (bf.origCols 0) v.1)
        ⟨Sum.inr n, hv⟩ y zero_le_one
      have hb1 : ‖catAtom s n y‖ ≤ 1 := catAtom_bound s n y
      have h2 : ‖privateColumnValue (fun v : bf.RLab Mc s => mainScalar Mc (bf.origCols 0) s v.1)
          (fun v => mainWeight Mc (bf.origCols 0) v.1) ⟨Sum.inr n, hv⟩ y‖ ^ 2 ≤ 2 ^ 2 := by
        rw [e1]
        change ‖catAtom s n y‖ ^ 2 + 1 ≤ _
        nlinarith [norm_nonneg (catAtom s n y)]
      exact ((pow_le_pow_iff_left₀ (norm_nonneg _) (by norm_num) two_ne_zero).mp h2).trans mb.two_le
  path_count := fun y => by
    have hsplit : (Finset.univ.filter fun v : bf.RLab Mc s =>
        y ∈ dyadicGridCell A.G (bf.mBirth s v).1 (bf.mBirth s v).2) ⊆
        (Finset.univ.filter fun v : bf.RLab Mc s =>
          v.1.isLeft ∧ y ∈ dyadicGridCell A.G (bf.mBirth s v).1 (bf.mBirth s v).2) ∪
        (Finset.univ.filter fun v : bf.RLab Mc s =>
          ¬ v.1.isLeft ∧ y ∈ dyadicGridCell A.G (bf.mBirth s v).1 (bf.mBirth s v).2) := by
      intro v hv
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union] at hv ⊢
      by_cases h : v.1.isLeft
      · exact Or.inl ⟨h, hv⟩
      · exact Or.inr ⟨h, hv⟩
    have h1 := bf.card_orig_births_le (Mc := Mc) s y
    have h2 := bf.card_tmpl_births_le (Mc := Mc) s y
    refine (Nat.cast_le.mpr ((Finset.card_le_card hsplit).trans
      (Finset.card_union_le _ _))).trans ?_
    push_cast
    have h2' : (((Finset.univ : Finset (bf.RLab Mc s)).filter fun v =>
        ¬ v.1.isLeft ∧ y ∈ dyadicGridCell A.G (bf.mBirth s v).1 (bf.mBirth s v).2).card : ℝ) ≤
        bf.tmplPath s y := by exact_mod_cast h2
    have := mb.hTp y
    linarith

end ActiveSetup.BasicFamilies

namespace ActiveSetup.BasicFamilies
variable {κ : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ c₀} (bf : A.BasicFamilies)

open scoped Classical in
/-- The active ancestors of a cell: the active cells containing it. -/
noncomputable def activeAnc (c : ℤ × ℤ) : Finset (ℤ × ℤ) :=
  A.cells.filter fun a => dyadicGridCell A.G c.1 c.2 ⊆ dyadicGridCell A.G a.1 a.2

open scoped Classical in
/-- The deepest active ancestor of a cell, if any (blueprint line 1859: between actual uses the
inherited projections are retained). -/
noncomputable def deepAnc (c : ℤ × ℤ) : Option (ℤ × ℤ) :=
  if h : (activeAnc (A := A) c).Nonempty then
    some (Classical.choose ((activeAnc (A := A) c).exists_max_image (fun a => a.1) h))
  else none

theorem deepAnc_spec {c a : ℤ × ℤ} (h : deepAnc (A := A) c = some a) :
    a ∈ A.cells ∧ dyadicGridCell A.G c.1 c.2 ⊆ dyadicGridCell A.G a.1 a.2 ∧
      ∀ b ∈ A.cells, dyadicGridCell A.G c.1 c.2 ⊆ dyadicGridCell A.G b.1 b.2 →
        dyadicGridCell A.G a.1 a.2 ⊆ dyadicGridCell A.G b.1 b.2 := by
  classical
  unfold deepAnc at h
  split_ifs at h with hne
  · rw [Option.some_inj] at h
    have hspec := Classical.choose_spec ((activeAnc (A := A) c).exists_max_image (fun a => a.1) hne)
    rw [h] at hspec
    obtain ⟨ha, hmax⟩ := hspec
    obtain ⟨haC, hca⟩ := Finset.mem_filter.mp ha
    refine ⟨haC, hca, fun b hb hcb => ?_⟩
    have hbm := hmax b (Finset.mem_filter.mpr ⟨hb, hcb⟩)
    have hy := dyadicGridCell_left_mem A.G c.1 c.2
    exact dyadicGridCell_subset_of_common_point A.G (hca hy) (hcb hy) hbm

theorem deepAnc_self {c : ℤ × ℤ} (hc : c ∈ A.cells) : deepAnc (A := A) c = some c := by
  classical
  have hne : (activeAnc (A := A) c).Nonempty := ⟨c, Finset.mem_filter.mpr ⟨hc, subset_rfl⟩⟩
  obtain ⟨a, ha⟩ : ∃ a, deepAnc (A := A) c = some a := by
    unfold deepAnc; rw [dite_eq_left_of_eq_true (eq_true hne)]; exact ⟨_, rfl⟩
  obtain ⟨haC, hca, hmin⟩ := deepAnc_spec ha
  have hac := hmin c hc subset_rfl
  have e : a = c := dyadicGridCell_injective A.G (Set.Subset.antisymm hac hca)
  rw [ha, e]

theorem deepAnc_mono {c d a : ℤ × ℤ}
    (hcd : dyadicGridCell A.G c.1 c.2 ⊆ dyadicGridCell A.G d.1 d.2)
    (hd : deepAnc (A := A) d = some a) :
    ∃ a', deepAnc (A := A) c = some a' ∧ dyadicGridCell A.G a'.1 a'.2 ⊆
      dyadicGridCell A.G a.1 a.2 := by
  classical
  obtain ⟨haC, hda, -⟩ := deepAnc_spec hd
  have hne : (activeAnc (A := A) c).Nonempty := ⟨a, Finset.mem_filter.mpr ⟨haC, hcd.trans hda⟩⟩
  obtain ⟨a', ha'⟩ : ∃ a', deepAnc (A := A) c = some a' := by
    unfold deepAnc; rw [dite_eq_left_of_eq_true (eq_true hne)]; exact ⟨_, rfl⟩
  obtain ⟨-, -, hmin⟩ := deepAnc_spec ha'
  exact ⟨a', ha', hmin a haC (hcd.trans hda)⟩

/-- The main labels of the slot `l` at an active cell `a`, of rank at most `r`, in the vertex
mask `M`: the available original columns whose vertex lies in `M` and the templates born above
`a` of rank at most `r` with tag in `M` (blueprint lines 1805-1806). -/
def mainPred (l : Fin 4) {Mc : ℕ} (s : List (CatCol bf.Vtx)) (a : ℤ × ℤ) (r : ℕ)
    (M : bf.Vtx → Prop) : bf.Lab ⊕ Fin Mc → Prop :=
  Sum.elim (fun x => (bf.origCols l).avail a x ∧ M (bf.vtxAt a x))
    (fun n => ∃ hn : (n : ℕ) < s.length, dyadicGridCell A.G a.1 a.2 ⊆
      dyadicGridCell A.G (s[(n : ℕ)]).birth.1 (s[(n : ℕ)]).birth.2 ∧
        (s[(n : ℕ)]).rank ≤ r ∧ M (s[(n : ℕ)]).tag)

theorem mainPred_relevant (l : Fin 4) {Mc : ℕ} (s : List (CatCol bf.Vtx)) {a : ℤ × ℤ} {r : ℕ}
    {M : bf.Vtx → Prop} {v : bf.Lab ⊕ Fin Mc} (hv : bf.mainPred l s a r M v) :
    bf.Relevant s v := by
  rcases v with x | n
  · exact ⟨a, hv.1.2.1, hv.1.2⟩
  · exact hv.1

open scoped Classical in
/-- The inherited masks of the main column tree for the slot `l`, rank `r` and depth-monotone
vertex masks `M`: at a cell, the main labels of its deepest active ancestor, none above the attempt
(blueprint line 1859: retained inherited projections, zero before the attempt). -/
noncomputable def mainMaskT (l : Fin 4) (Mc : ℕ) (s : List (CatCol bf.Vtx))
    (mb : bf.MainBudget s) (r : ℕ) (M : ℤ × ℤ → bf.Vtx → Prop)
    (hM : ∀ c ∈ A.cells, ∀ d ∈ A.cells, dyadicGridCell A.G c.1 c.2 ⊆ dyadicGridCell A.G d.1 d.2 →
      ∀ x, M d x → M c x) :
    InheritedColumnMask (bf.mainTree Mc s mb) where
  labels := fun c => match deepAnc (A := A) c with
    | none => ∅
    | some a => Finset.univ.filter fun v : bf.RLab Mc s => bf.mainPred l s a r (M a) v.1
  available := fun c _ v hv => by
    rcases ha : deepAnc (A := A) c with _ | a
    · rw [ha] at hv; exact absurd hv (Finset.notMem_empty _)
    · rw [ha] at hv
      have hv' := (Finset.mem_filter.mp hv).2
      obtain ⟨-, hca, -⟩ := deepAnc_spec ha
      change dyadicGridCell A.G c.1 c.2 ⊆
        dyadicGridCell A.G (bf.mBirth s v).1 (bf.mBirth s v).2
      obtain ⟨x | n, hrel⟩ := v
      · exact hca.trans (bf.cell_sub_mBirth_inl s hv'.1.2 hrel)
      · obtain ⟨hn, hab, -, -⟩ := hv'
        exact hca.trans hab
  inherited := fun c hc d hd hcd v hv => by
    rcases ha : deepAnc (A := A) d with _ | a
    · rw [ha] at hv; exact absurd hv (Finset.notMem_empty _)
    · rw [ha] at hv
      have hv' := (Finset.mem_filter.mp hv).2
      obtain ⟨a', ha', ha'a⟩ := deepAnc_mono hcd ha
      obtain ⟨haC, -, -⟩ := deepAnc_spec ha
      obtain ⟨ha'C, -, -⟩ := deepAnc_spec ha'
      change v ∈ (match deepAnc (A := A) c with
        | none => ∅
        | some a => Finset.univ.filter fun v : bf.RLab Mc s => bf.mainPred l s a r (M a) v.1)
      rw [ha']
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      obtain ⟨x | n, hrel⟩ := v
      · obtain ⟨⟨hl, hav⟩, hMx⟩ := hv'
        refine ⟨⟨hl, bf.occAvail_desc ha'C ha'a hav⟩, ?_⟩
        rw [bf.vtxAt_desc ha'C haC ha'a hav]
        exact hM a' ha'C a haC ha'a _ hMx
      · obtain ⟨hn, hab, hr, hMn⟩ := hv'
        exact ⟨hn, ha'a.trans hab, hr, hM a' ha'C a haC ha'a _ hMn⟩

theorem mainMaskT_labels_self (l : Fin 4) (Mc : ℕ) (s : List (CatCol bf.Vtx))
    (mb : bf.MainBudget s) (r : ℕ) (M : ℤ × ℤ → bf.Vtx → Prop)
    (hM : ∀ c ∈ A.cells, ∀ d ∈ A.cells, dyadicGridCell A.G c.1 c.2 ⊆ dyadicGridCell A.G d.1 d.2 →
      ∀ x, M d x → M c x) {c : ℤ × ℤ} (hc : c ∈ A.cells) (v : bf.RLab Mc s) :
    v ∈ (bf.mainMaskT l Mc s mb r M hM).labels c ↔ bf.mainPred l s c r (M c) v.1 := by
  classical
  change v ∈ (match deepAnc (A := A) c with
    | none => ∅
    | some a => Finset.univ.filter fun v : bf.RLab Mc s => bf.mainPred l s a r (M a) v.1) ↔ _
  rw [deepAnc_self hc]
  simp

end ActiveSetup.BasicFamilies

namespace ActiveSetup.BasicFamilies
variable {κ : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ c₀} (bf : A.BasicFamilies)

/-- The main depth family of the slot `l` for the rank `r` and the depth-monotone vertex masks
`M` (blueprint line 1859): the nested depth projections of the main column tree with the
inherited masks, on the complete tree of the attempt. -/
noncomputable def mainFam (l : Fin 4) (Mc : ℕ) (s : List (CatCol bf.Vtx))
    (mb : bf.MainBudget s) (r : ℕ) (M : ℤ × ℤ → bf.Vtx → Prop)
    (hM : ∀ c ∈ A.cells, ∀ d ∈ A.cells, dyadicGridCell A.G c.1 c.2 ⊆ dyadicGridCell A.G d.1 d.2 →
      ∀ x, M d x → M c x) : ColumnDepthFamily (bf.RLab Mc s) where
  D := bf.mainTree Mc s mb
  A := bf.mainMaskT l Mc s mb r M hM
  N := A.R.1 + A.treeDepth
  root_le := by change A.R.1 ≤ A.R.1 + A.treeDepth; omega
  complete := fun c hc hN => (dyadicFiniteTree_mem_iff A.G A.R c _).mpr ⟨hc, hN⟩

/-- At an active cell the relabeled cell projection of the main depth family is the main
projection (blueprint lines 1805, 1859): the global main projections restrict to the cell-local
ones. -/
theorem relabel_cellProj (l : Fin 4) (Mc : ℕ) (s : List (CatCol bf.Vtx))
    (mb : bf.MainBudget s) (r : ℕ) (M : ℤ × ℤ → bf.Vtx → Prop)
    (hM : ∀ c ∈ A.cells, ∀ d ∈ A.cells, dyadicGridCell A.G c.1 c.2 ⊆ dyadicGridCell A.G d.1 d.2 →
      ∀ x, M d x → M c x) {c : ℤ × ℤ} (hc : c ∈ A.cells)
    (z : ColumnL2 (bf.RLab Mc s)) :
    colRelabel (bf.rv Mc s) (cellColumnProjection (bf.mainTree Mc s mb)
      (bf.mainMaskT l Mc s mb r M hM) (A.cells_mem_tree hc) z) =
      mainProj A.G Mc (bf.origCols l) s c r (M c) (colRelabel (bf.rv Mc s) z) := by
  set! D := bf.mainTree Mc s mb
  set Am := bf.mainMaskT l Mc s mb r M hM
  have hcT := A.cells_mem_tree hc
  have hlab := bf.mainMaskT_labels_self l Mc s mb r M hM hc
  have hmemL : ∀ v ∈ Am.labels c, v.1 ∈ mainLabels A.G Mc (bf.origCols l) s c r := by
    intro v hv
    have hp := (hlab v).mp hv
    obtain ⟨x | n, hrel⟩ := v
    · exact mem_mainLabels.mpr hp.1
    · obtain ⟨hn, h1, h2, -⟩ := hp
      exact mem_mainLabels.mpr ⟨hn, h1, h2⟩
  have hmap : (cellColumnRange D Am hcT).map (colRelabel (bf.rv Mc s)).toLinearMap =
      mainRange A.G Mc (bf.origCols l) s c r (M c) := by
    rw [cellColumnRange_map_relabel D Am hcT (f := bf.rv Mc s)
      (φ' := mainScalar Mc (bf.origCols l) s) (ε' := mainWeight Mc (bf.origCols l))
      (fun v => rfl) (fun v => rfl) (fun v hv => bf.mainLabel_memLp l s c r (hmemL v hv))]
    unfold mainRange
    congr 1
    ext x
    constructor
    · rintro ⟨⟨v, hv⟩, -, rfl⟩
      have hp := (hlab v).mp hv
      obtain ⟨y | n, hrel⟩ := v
      · exact Or.inl ⟨y, hp.1, hp.2, rfl⟩
      · obtain ⟨hn, h1, h2, h3⟩ := hp
        exact Or.inr ⟨n, hn, h1, h2, h3, rfl⟩
    · rintro (⟨y, hav, hMy, rfl⟩ | ⟨n, hn, h1, h2, h3, rfl⟩)
      · have hp : bf.mainPred l s c r (M c) (Sum.inl y : bf.Lab ⊕ Fin Mc) := ⟨hav, hMy⟩
        exact ⟨⟨⟨Sum.inl y, bf.mainPred_relevant l s hp⟩, (hlab _).mpr hp⟩, Set.mem_univ _, rfl⟩
      · have hp : bf.mainPred l s c r (M c) (Sum.inr n : bf.Lab ⊕ Fin Mc) := ⟨hn, h1, h2, h3⟩
        exact ⟨⟨⟨Sum.inr n, bf.mainPred_relevant l s hp⟩, (hlab _).mpr hp⟩, Set.mem_univ _, rfl⟩
  have hfd : FiniteDimensional ℂ (cellColumnRange D Am hcT) :=
    cellColumnRange_finiteDimensional D Am hcT
  have h := starProjection_map_isometry (colRelabelLI (f := bf.rv Mc s) (bf.rv_injective Mc s))
    (cellColumnRange D Am hcT) z
  change (colRelabelLI (f := bf.rv Mc s) (bf.rv_injective Mc s))
    ((cellColumnRange D Am hcT).starProjection z) = _
  rw [← h]
  unfold mainProj
  exact starProjection_congr hmap _

end ActiveSetup.BasicFamilies

/-! ### Relabelings, restrictions and adjoints -/

section RelabelRestrict
variable {V W : Type*} [Fintype V] [Fintype W]

/-- A relabeling commutes with the restriction to a set. -/
theorem colRelabel_restrict (f : V → W) (s : Set ℝ) (hs : MeasurableSet s) (z : ColumnL2 V) :
    colRelabel f (columnL2Restriction s hs z) = columnL2Restriction s hs (colRelabel f z) := by
  refine Lp.ext ?_
  change (colRelabel f (columnL2Indicator s hs z) : ℝ → ColumnHilbert W) =ᵐ[volume]
    (columnL2Indicator s hs (colRelabel f z) : ℝ → ColumnHilbert W)
  filter_upwards [colRelabel_coeFn f (columnL2Indicator s hs z), columnL2Indicator_coeFn s hs z,
    columnL2Indicator_coeFn s hs (colRelabel f z), colRelabel_coeFn f z] with y h1 h2 h3 h4
  rw [h1, h3, h2]
  by_cases hy : y ∈ s
  · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, h4]
  · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, map_zero]

theorem colRelabel_comp_restrict (f : V → W) (s : Set ℝ) (hs : MeasurableSet s) :
    (colRelabel f).comp (columnL2Restriction s hs) =
      (columnL2Restriction s hs).comp (colRelabel f) :=
  ContinuousLinearMap.ext fun z => colRelabel_restrict f s hs z

/-- The adjoint of a relabeling also commutes with the restriction to a set. -/
theorem colRelabel_adjoint_restrict (f : V → W) (s : Set ℝ) (hs : MeasurableSet s)
    (w : ColumnL2 W) :
    ContinuousLinearMap.adjoint (colRelabel f) (columnL2Restriction s hs w) =
      columnL2Restriction s hs (ContinuousLinearMap.adjoint (colRelabel f) w) := by
  have h := congrArg ContinuousLinearMap.adjoint (colRelabel_comp_restrict f s hs)
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_comp,
    columnL2Restriction_adjoint, columnL2Restriction_adjoint] at h
  exact (DFunLike.congr_fun h w).symm

/-- Along an injection the adjoint of the relabeling is a left inverse. -/
theorem colRelabel_adjoint_apply_relabel {f : V → W} (hf : Function.Injective f)
    (z : ColumnL2 V) : ContinuousLinearMap.adjoint (colRelabel f) (colRelabel f z) = z := by
  refine ext_inner_right ℂ fun x => ?_
  rw [ContinuousLinearMap.adjoint_inner_left]
  exact LinearIsometry.inner_map_map (colRelabelLI hf) z x

theorem norm_colRelabel_adjoint_le {f : V → W} (hf : Function.Injective f) (w : ColumnL2 W) :
    ‖ContinuousLinearMap.adjoint (colRelabel f) w‖ ≤ ‖w‖ := by
  have hop : ‖colRelabel f‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun z => by
      rw [one_mul, norm_colRelabel hf]
  refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
  rw [ContinuousLinearMap.adjoint.norm_map]
  exact mul_le_of_le_one_left (norm_nonneg _) hop

/-- On the range of an injective relabeling, relabeling after the adjoint is the identity. -/
theorem colRelabel_adjoint_of_mem_range {f : V → W} (hf : Function.Injective f) {w : ColumnL2 W}
    (hw : w ∈ LinearMap.range (colRelabel f).toLinearMap) :
    colRelabel f (ContinuousLinearMap.adjoint (colRelabel f) w) = w := by
  obtain ⟨z, rfl⟩ := hw
  change colRelabel f (ContinuousLinearMap.adjoint (colRelabel f) (colRelabel f z)) = colRelabel f z
  rw [colRelabel_adjoint_apply_relabel hf]

end RelabelRestrict

section IntertwineHetero
variable {E E' : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedAddCommGroup E']
  [InnerProductSpace ℂ E']

/-- Layer products intertwine along a map intertwining their factors. -/
theorem layerOp_intertwine₂ (C : ℕ → E →L[ℂ] E) (C' : ℕ → E' →L[ℂ] E') (r : E →L[ℂ] E')
    (h : ∀ m, r.comp (C m) = (C' m).comp r) (ls : List (ℕ × Bool)) :
    r.comp (layerOp C ls) = (layerOp C' ls).comp r := by
  induction ls using List.reverseRecOn with
  | nil => simp [layerOp_nil]
  | append_singleton l a ih =>
    rw [layerOp_append, layerOp_append, ← ContinuousLinearMap.comp_assoc,
      ContinuousLinearMap.comp_assoc _ (layerOp C' l), ← ih, ← ContinuousLinearMap.comp_assoc]
    congr 1
    split_ifs
    · rw [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub, h,
        ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id]
    · exact h _

theorem opAvg_intertwine₂ {P : ℕ} (Q : Fin P → E →L[ℂ] E) (Q' : Fin P → E' →L[ℂ] E')
    (r : E →L[ℂ] E') (h : ∀ p, r.comp (Q p) = (Q' p).comp r) :
    r.comp (opAvg Q) = (opAvg Q').comp r := by
  have hp : ∀ p x, r (Q p x) = Q' p (r x) := fun p x => DFunLike.congr_fun (h p) x
  refine ContinuousLinearMap.ext fun x => ?_
  simp only [ContinuousLinearMap.comp_apply, opAvg, smul_apply, FunLike.coe_sum,
    Finset.sum_apply, hp, map_smul, map_sum]

end IntertwineHetero

section GlobalHistoryCells
variable {V : Type*} [Fintype V]

/-- On a cell of the depth partition, the global averaged history is the layer product of the
averaged cell projections of the cell (blueprint lines 1859, 1879: histories evaluated at their
decision cells). -/
theorem globHist_restrict (Ψ : ColumnDepthFamily V) {P : ℕ}
    (Am : ℕ → Fin P → InheritedColumnMask Ψ.D) (ls : List (ℕ × Bool)) (h : ℤ) {Q : ℤ × ℤ}
    (hQ : Q ∈ (Ψ.partition h).cells) (z : ColumnL2 V) :
    columnL2Restriction (dyadicGridCell Ψ.D.grid Q.1 Q.2)
        (dyadicGridCell_measurable Ψ.D.grid Q.1 Q.2) (globHist Ψ Am ls h z) =
      layerOp (fun m => opAvg fun p =>
        cellColumnProjection Ψ.D (Am m p) ((Ψ.partition h).subset hQ)) ls
        (columnL2Restriction (dyadicGridCell Ψ.D.grid Q.1 Q.2)
          (dyadicGridCell_measurable Ψ.D.grid Q.1 Q.2) z) := by
  set rs := columnL2Restriction (V := V) (dyadicGridCell Ψ.D.grid Q.1 Q.2)
    (dyadicGridCell_measurable Ψ.D.grid Q.1 Q.2)
  have hcell : ∀ m (p : Fin P), rs.comp ((Ψ.withMask (Am m p)).proj h) =
      (cellColumnProjection Ψ.D (Am m p) ((Ψ.partition h).subset hQ)).comp rs := by
    intro m p
    have h1 := (Ψ.withMask (Am m p)).restrict_proj h (Q := Q) hQ
    have h2 := cellColumnProjection_restrict Ψ.D (Am m p) ((Ψ.partition h).subset hQ)
    exact h1.1.trans h2.2.symm
  have hint := layerOp_intertwine _ (fun m => opAvg fun p =>
    cellColumnProjection Ψ.D (Am m p) ((Ψ.partition h).subset hQ)) rs
    (fun m => opAvg_intertwine _ _ _ fun p => hcell m p) ls
  unfold globHist
  rw [← ContinuousLinearMap.comp_apply rs, hint]
  rfl

end GlobalHistoryCells

namespace ActiveSetup.BasicFamilies
variable {κ : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ c₀} (bf : A.BasicFamilies)

/-- The main column tree as a depth family on the complete tree of the attempt (its masks are
replaced by `withMask`). -/
noncomputable def mainBase (Mc : ℕ) (s : List (CatCol bf.Vtx)) (mb : bf.MainBudget s) :
    ColumnDepthFamily (bf.RLab Mc s) :=
  bf.mainFam 0 Mc s mb 0 (fun _ _ => False) (fun _ _ _ _ _ _ h => h)

theorem mem_partition_mainBase (Mc : ℕ) (s : List (CatCol bf.Vtx)) (mb : bf.MainBudget s)
    {I : ℤ × ℤ} (hI : I ∈ A.cells) : I ∈ ((bf.mainBase Mc s mb).partition I.1).cells := by
  have hIR := (dyadicFiniteTree_mem_iff A.G A.R I _).mp (A.cells_mem_tree hI)
  exact (bf.mainBase Mc s mb).depth_of_mem
    (dyadicGridCell_depth_le_of_subset A.G I A.R hIR.1) hIR.2 rfl hIR.1

/-- At an active cell, the cell restriction of the relabeled global depth projection of the main
tree with the inherited masks is the main projection of the cell applied to the restricted
relabeled input (blueprint lines 1805, 1859). -/
theorem proj_bridge (l : Fin 4) (Mc : ℕ) (s : List (CatCol bf.Vtx)) (mb : bf.MainBudget s)
    (r : ℕ) (M : ℤ × ℤ → bf.Vtx → Prop)
    (hM : ∀ c ∈ A.cells, ∀ d ∈ A.cells, dyadicGridCell A.G c.1 c.2 ⊆ dyadicGridCell A.G d.1 d.2 →
      ∀ x, M d x → M c x) {I : ℤ × ℤ} (hI : I ∈ A.cells) (z : ColumnL2 (bf.RLab Mc s)) :
    columnL2Restriction (dyadicGridCell A.G I.1 I.2) (dyadicGridCell_measurable A.G I.1 I.2)
        (colRelabel (bf.rv Mc s) (((bf.mainBase Mc s mb).withMask
          (bf.mainMaskT l Mc s mb r M hM)).proj I.1 z)) =
      mainProj A.G Mc (bf.origCols l) s I r (M I)
        (columnL2Restriction (dyadicGridCell A.G I.1 I.2) (dyadicGridCell_measurable A.G I.1 I.2)
          (colRelabel (bf.rv Mc s) z)) := by
  set Ψ := (bf.mainBase Mc s mb).withMask (bf.mainMaskT l Mc s mb r M hM)
  have hQ : I ∈ (Ψ.partition I.1).cells := bf.mem_partition_mainBase Mc s mb hI
  have h1 : (columnL2Restriction (dyadicGridCell A.G I.1 I.2)
      (dyadicGridCell_measurable A.G I.1 I.2)).comp (Ψ.proj I.1) =
      cellColumnProjection (bf.mainTree Mc s mb) (bf.mainMaskT l Mc s mb r M hM)
        (A.cells_mem_tree hI) := (Ψ.restrict_proj I.1 hQ).1
  have h2 : (Ψ.proj I.1).comp (columnL2Restriction (dyadicGridCell A.G I.1 I.2)
      (dyadicGridCell_measurable A.G I.1 I.2)) =
      cellColumnProjection (bf.mainTree Mc s mb) (bf.mainMaskT l Mc s mb r M hM)
        (A.cells_mem_tree hI) := (Ψ.restrict_proj I.1 hQ).2
  rw [← colRelabel_restrict, ← ContinuousLinearMap.comp_apply (columnL2Restriction _ _), h1,
    ← colRelabel_restrict, ← bf.relabel_cellProj l Mc s mb r M hM hI, ← h2]
  have hid := DFunLike.congr_fun (columnL2Restriction_idem (V := bf.RLab Mc s)
    (dyadicGridCell A.G I.1 I.2) (dyadicGridCell_measurable A.G I.1 I.2)) z
  rw [ContinuousLinearMap.comp_apply] at hid
  simp only [ContinuousLinearMap.comp_apply, hid]

end ActiveSetup.BasicFamilies

namespace ActiveSetup.BasicFamilies.FamParams
variable {κ : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ c₀} {bf : A.BasicFamilies}
  (fp : bf.FamParams)

/-- The inherited cumulative masks of the main tree of the slot `l` (blueprint lines 1807, 1859):
the split `m`, the pad index `p`. -/
noncomputable def cumMaskT (l : Fin 4) (s : List (CatCol bf.Vtx)) (mb : bf.MainBudget s) (m : ℕ)
    (p : Fin fp.P) : InheritedColumnMask (bf.mainTree fp.Mc s mb) :=
  bf.mainMaskT l fp.Mc s mb (fp.crank m) (fun c => fp.cmask c m (p + 1))
    (fun _ hc _ hd hcd x hx => fp.cmask_mono hc hd hcd m (p + 1) x hx)

/-- The inherited ball masks of the main tree of the slot `l` for the group `G` at the ball level
`j` and the pad index `p` (blueprint lines 1807, 1859). -/
noncomputable def ballMaskT (l : Fin 4) (s : List (CatCol bf.Vtx)) (mb : bf.MainBudget s)
    (G : bf.Grp) (j : ℕ) (p : Fin fp.P) : InheritedColumnMask (bf.mainTree fp.Mc s mb) :=
  bf.mainMaskT l fp.Mc s mb (fp.brank j) (fun c => fp.bmask c G j (p + 1))
    (fun _ hc _ hd hcd x hx => fp.bmask_mono hc hd hcd G j (p + 1) x hx)

/-- The global shared cumulative history `B'_{l,s}` with layers `ls` at the depth `h`, on the
relevant main labels: a layer product of averaged global main depth projections or their
complements (blueprint lines 1859, 1871). -/
noncomputable def gHist (l : Fin 4) (s : List (CatCol bf.Vtx)) (mb : bf.MainBudget s)
    (ls : List (ℕ × Bool)) (h : ℤ) :
    ColumnL2 (bf.RLab fp.Mc s) →L[ℂ] ColumnL2 (bf.RLab fp.Mc s) :=
  globHist (bf.mainBase fp.Mc s mb) (fp.cumMaskT l s mb) ls h

/-- The global positive smeared ball filter `L_{l,G}` at the ball level `j` and the depth `h`
(blueprint lines 1807, 1859). -/
noncomputable def gBall (l : Fin 4) (s : List (CatCol bf.Vtx)) (mb : bf.MainBudget s) (G : bf.Grp)
    (j : ℕ) (h : ℤ) : ColumnL2 (bf.RLab fp.Mc s) →L[ℂ] ColumnL2 (bf.RLab fp.Mc s) :=
  opAvg fun p : Fin fp.P => ((bf.mainBase fp.Mc s mb).withMask (fp.ballMaskT l s mb G j p)).proj h

/-- At an active cell the global cumulative history restricts to the cell-local history of the
search leaves (blueprint line 1859). -/
theorem hist_bridge (l : Fin 4) (s : List (CatCol bf.Vtx)) (mb : bf.MainBudget s)
    (ls : List (ℕ × Bool)) {I : ℤ × ℤ} (hI : I ∈ A.cells) (z : ColumnL2 (bf.RLab fp.Mc s)) :
    columnL2Restriction (dyadicGridCell A.G I.1 I.2) (dyadicGridCell_measurable A.G I.1 I.2)
        (colRelabel (bf.rv fp.Mc s) (fp.gHist l s mb ls I.1 z)) =
      layerOp (fun m => fp.cumFilt l s I m) ls
        (columnL2Restriction (dyadicGridCell A.G I.1 I.2) (dyadicGridCell_measurable A.G I.1 I.2)
          (colRelabel (bf.rv fp.Mc s) z)) := by
  set! r := (columnL2Restriction (V := bf.Lab ⊕ Fin fp.Mc) (dyadicGridCell A.G I.1 I.2)
    (dyadicGridCell_measurable A.G I.1 I.2)).comp (colRelabel (bf.rv fp.Mc s))
  have hfac : ∀ m (p : Fin fp.P), r.comp (((bf.mainBase fp.Mc s mb).withMask
      (fp.cumMaskT l s mb m p)).proj I.1) =
      (mainProj A.G fp.Mc (bf.origCols l) s I (fp.crank m) (fp.cmask I m (p + 1))).comp r := by
    intro m p
    refine ContinuousLinearMap.ext fun z => ?_
    exact bf.proj_bridge l fp.Mc s mb (fp.crank m) (fun c => fp.cmask c m (p + 1)) _ hI z
  have h := layerOp_intertwine₂ (fun m => opAvg fun p : Fin fp.P =>
    ((bf.mainBase fp.Mc s mb).withMask (fp.cumMaskT l s mb m p)).proj I.1)
    (fun m => fp.cumFilt l s I m) r (fun m => opAvg_intertwine₂ _ _ r fun p => hfac m p) ls
  exact DFunLike.congr_fun h z

/-- At an active cell the global ball filter restricts to the cell-local ball filter (blueprint
line 1859). -/
theorem ball_bridge (l : Fin 4) (s : List (CatCol bf.Vtx)) (mb : bf.MainBudget s) (G : bf.Grp)
    (j : ℕ) {I : ℤ × ℤ} (hI : I ∈ A.cells) (z : ColumnL2 (bf.RLab fp.Mc s)) :
    columnL2Restriction (dyadicGridCell A.G I.1 I.2) (dyadicGridCell_measurable A.G I.1 I.2)
        (colRelabel (bf.rv fp.Mc s) (fp.gBall l s mb G j I.1 z)) =
      fp.ballFilt l s I G j
        (columnL2Restriction (dyadicGridCell A.G I.1 I.2) (dyadicGridCell_measurable A.G I.1 I.2)
          (colRelabel (bf.rv fp.Mc s) z)) := by
  set! r := (columnL2Restriction (V := bf.Lab ⊕ Fin fp.Mc) (dyadicGridCell A.G I.1 I.2)
    (dyadicGridCell_measurable A.G I.1 I.2)).comp (colRelabel (bf.rv fp.Mc s))
  have hfac : ∀ p : Fin fp.P, r.comp (((bf.mainBase fp.Mc s mb).withMask
      (fp.ballMaskT l s mb G j p)).proj I.1) =
      (mainProj A.G fp.Mc (bf.origCols l) s I (fp.brank j) (fp.bmask I G j (p + 1))).comp r := by
    intro p
    refine ContinuousLinearMap.ext fun z => ?_
    exact bf.proj_bridge l fp.Mc s mb (fp.brank j) (fun c => fp.bmask c G j (p + 1)) _ hI z
  have h := opAvg_intertwine₂ _ _ r hfac
  exact DFunLike.congr_fun h z

end ActiveSetup.BasicFamilies.FamParams

section FreshRelabel
variable {V : Type} [Fintype V] {Mc : ℕ}

open scoped Classical in
/-- Relabeling into original labels creates no template coordinates. -/
theorem colRelabel_inl_fresh {V' : Type*} [Fintype V'] (g : V' → V) (z : ColumnL2 V') :
    MainFresh Mc 0 (colRelabel (fun v => (Sum.inl (g v) : V ⊕ Fin Mc)) z) := fun m _ => by
  filter_upwards [colRelabel_coeFn (fun v => (Sum.inl (g v) : V ⊕ Fin Mc)) z] with y hy
  rw [hy, relabelCLM_apply, Fintype.sum_option]
  simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.single_apply, Option.map_none, Option.map_some,
    smul_eq_mul, reduceCtorEq, ↓reduceIte, mul_zero, zero_add]
  rw [WithLp.ofLp_sum]
  simp

/-- The restriction to a set keeps the absence of template coordinates. -/
theorem MainFresh.restrict {n : ℕ} {x : ColumnL2 (V ⊕ Fin Mc)} (h : MainFresh Mc n x)
    (s : Set ℝ) (hs : MeasurableSet s) : MainFresh Mc n (columnL2Restriction s hs x) :=
  fun m hm => by
    change ∀ᵐ y ∂volume, (columnL2Indicator s hs x : ℝ → ColumnHilbert (V ⊕ Fin Mc)) y
      (some (Sum.inr m)) = 0
    filter_upwards [columnL2Indicator_coeFn s hs x, h m hm] with y h1 h2
    rw [h1]
    by_cases hy : y ∈ s
    · rw [Set.indicator_of_mem hy, h2]
    · rw [Set.indicator_of_notMem hy]; rfl

end FreshRelabel

/-- A relabeling keeps the physical coordinate. -/
theorem augPhys_colRelabel {V W : Type*} [Fintype V] [Fintype W] (f : V → W) (z : ColumnL2 V) :
    augPhys (colRelabel f z) =ᵐ[volume] augPhys z := by
  classical
  filter_upwards [colRelabel_coeFn f z] with y hy
  simp only [augPhys]
  rw [hy, relabelCLM_apply, Fintype.sum_option]
  simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.single_apply, Option.map_none, Option.map_some,
    smul_eq_mul, ↓reduceIte, mul_one]
  rw [WithLp.ofLp_sum]
  simp

/-- The restriction to a set restricts the physical coordinate. -/
theorem augPhys_restrict {V : Type*} [Fintype V] (s : Set ℝ) (hs : MeasurableSet s)
    (z : ColumnL2 V) :
    augPhys (columnL2Restriction s hs z) =ᵐ[volume] s.indicator (augPhys z) := by
  change (fun y => (columnL2Indicator s hs z : ℝ → ColumnHilbert V) y none) =ᵐ[volume] _
  filter_upwards [columnL2Indicator_coeFn s hs z] with y hy
  rw [hy]
  by_cases h : y ∈ s
  · rw [Set.indicator_of_mem h, Set.indicator_of_mem h]; rfl
  · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h]; rfl

theorem augPhys_sub {V : Type*} [Fintype V] (x x' : ColumnL2 V) :
    augPhys (x - x') =ᵐ[volume] augPhys x - augPhys x' := by
  filter_upwards [Lp.coeFn_sub x x'] with y hy
  simp only [augPhys, hy, Pi.sub_apply, PiLp.sub_apply]

namespace ActiveSetup.BasicFamilies
variable {κ : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ c₀} (bf : A.BasicFamilies)

/-- The embedding of the column space of the basic family `(l, j)` into the main column space:
its columns are the original basic columns of the slot `l` (blueprint lines 1676, 1805). -/
noncomputable def famEmb (Mc : ℕ) (l : Fin 4) (j : Fin 2) :
    ColumnL2 (bf.P l j).V →L[ℂ] ColumnL2 (bf.Lab ⊕ Fin Mc) :=
  colRelabel (fun v => (Sum.inl ⟨l, j, v⟩ : bf.Lab ⊕ Fin Mc))

theorem famEmb_injective (Mc : ℕ) (l : Fin 4) (j : Fin 2) :
    Function.Injective (fun v : (bf.P l j).V => (Sum.inl ⟨l, j, v⟩ : bf.Lab ⊕ Fin Mc)) := by
  intro v w h
  have h1 := Sum.inl_injective h
  simp only [Sigma.mk.injEq, heq_eq_eq, true_and] at h1
  exact h1

/-- The global basic input of the slot `l` at the depth `h`: the fixed signed sum
`P_{l,0,h} F_{l,0} - P_{l,1,h} F_{l,1}` of the depth projections of the two basic families acting on
their inputs, in the main column space (blueprint prop:base line 1611, line 1859). -/
noncomputable def gBasic (Mc : ℕ) (l : Fin 4) (h : ℤ) : ColumnL2 (bf.Lab ⊕ Fin Mc) :=
  bf.famEmb Mc l 0 ((bf.P l 0).Ψ.proj h (bf.P l 0).Z) -
    bf.famEmb Mc l 1 ((bf.P l 1).Ψ.proj h (bf.P l 1).Z)

/-- The basic input of the slot `l` on the cell `I`: the global basic input at the depth of `I`
restricted to `I`. -/
noncomputable def basicIn (Mc : ℕ) (l : Fin 4) (I : ℤ × ℤ) : ColumnL2 (bf.Lab ⊕ Fin Mc) :=
  columnL2Restriction (dyadicGridCell A.G I.1 I.2) (dyadicGridCell_measurable A.G I.1 I.2)
    (bf.gBasic Mc l I.1)

theorem famCell_mem (l : Fin 4) (j : Fin 2) {I : ℤ × ℤ} (hI : I ∈ A.cells) :
    I ∈ ((bf.P l j).Ψ.partition I.1).cells := by
  obtain ⟨-, hIN, -⟩ := bf.charts l j I hI
  have hsub : dyadicGridCell (bf.P l j).Ψ.D.grid I.1 I.2 ⊆
      dyadicGridCell (bf.P l j).Ψ.D.grid (bf.P l j).Ψ.D.root.1 (bf.P l j).Ψ.D.root.2 := by
    rw [(bf.P l j).grid]; exact (A.sub I hI).trans (bf.P l j).root_sub
  exact (bf.P l j).Ψ.depth_of_mem
    (dyadicGridCell_depth_le_of_subset _ I _ hsub) hIN rfl hsub

/-- At an active cell the basic depth projection restricts to the basic cell projection. -/
theorem fam_restrict (l : Fin 4) (j : Fin 2) {I : ℤ × ℤ} (hI : I ∈ A.cells)
    (Z : ColumnL2 (bf.P l j).V) :
    columnL2Restriction (dyadicGridCell A.G I.1 I.2) (dyadicGridCell_measurable A.G I.1 I.2)
        ((bf.P l j).Ψ.proj I.1 Z) =
      cellColumnProjection (bf.P l j).Ψ.D (bf.P l j).Ψ.A
        (((bf.P l j).Ψ.partition I.1).subset (bf.famCell_mem l j hI)) Z := by
  have h := ((bf.P l j).Ψ.restrict_proj I.1 (bf.famCell_mem l j hI)).1
  rw [(bf.P l j).grid] at h
  exact DFunLike.congr_fun h Z

/-- The basic input on an active cell is the fixed signed sum of the basic cell projections of
the family inputs. -/
theorem basicIn_eq (Mc : ℕ) (l : Fin 4) {I : ℤ × ℤ} (hI : I ∈ A.cells) :
    bf.basicIn Mc l I =
      bf.famEmb Mc l 0 (cellColumnProjection (bf.P l 0).Ψ.D (bf.P l 0).Ψ.A
        (((bf.P l 0).Ψ.partition I.1).subset (bf.famCell_mem l 0 hI)) (bf.P l 0).Z) -
      bf.famEmb Mc l 1 (cellColumnProjection (bf.P l 1).Ψ.D (bf.P l 1).Ψ.A
        (((bf.P l 1).Ψ.partition I.1).subset (bf.famCell_mem l 1 hI)) (bf.P l 1).Z) := by
  unfold basicIn gBasic famEmb
  rw [map_sub, ← colRelabel_restrict, ← colRelabel_restrict, bf.fam_restrict l 0 hI,
    bf.fam_restrict l 1 hI]

/-- A basic cell column embeds as the main column of its original label. -/
theorem famEmb_cellColumn (Mc : ℕ) (s : List (CatCol bf.Vtx)) (l : Fin 4) (j : Fin 2)
    {I : ℤ × ℤ} (hI : I ∈ A.cells) (hID : I ∈ (bf.P l j).Ψ.D.cells)
    (v : {v // v ∈ (bf.P l j).Ψ.A.labels I}) :
    bf.famEmb Mc l j (cellColumnLp (bf.P l j).Ψ.D (bf.P l j).Ψ.A hID v) =
      mainCol A.G Mc (bf.origCols l) s I (Sum.inl ⟨l, j, v.1⟩) := by
  have hmem := cellColumn_memLp (bf.P l j).Ψ.D (bf.P l j).Ψ.A hID v.2
  have hmem' := bf.origCol_memLp (Mc := Mc) l s (I := I) (v := ⟨l, j, v.1⟩) ⟨hI, v.2⟩
  rw [cellColumnLp_eq_wColumn]
  unfold famEmb mainCol
  rw [(bf.P l j).grid] at hmem ⊢
  exact colRelabel_wColumn (f := fun v => (Sum.inl ⟨l, j, v⟩ : bf.Lab ⊕ Fin Mc))
    (φ' := mainScalar Mc (bf.origCols l) s) (ε' := mainWeight Mc (bf.origCols l)) rfl rfl hmem hmem'

/-- An original column of the slot `l` available at an active cell is the relabeling of a column
of the main tree. -/
theorem origCol_mem_range (l : Fin 4) (Mc : ℕ) (s : List (CatCol bf.Vtx)) (mb : bf.MainBudget s)
    {I : ℤ × ℤ} (hI : I ∈ A.cells) {x : bf.Lab} (hxl : x.1 = l) (hx : bf.occAvail I x) :
    mainCol A.G Mc (bf.origCols l) s I (Sum.inl x) ∈
      LinearMap.range (colRelabel (bf.rv Mc s)).toLinearMap := by
  set! Am := bf.mainMaskT l Mc s mb 0 (fun _ _ => True) (fun _ _ _ _ _ _ h => h)
  have hrel : bf.Relevant (Mc := Mc) s (Sum.inl x) := ⟨I, hI, hx⟩
  have hv : (⟨Sum.inl x, hrel⟩ : bf.RLab Mc s) ∈ Am.labels I :=
    (bf.mainMaskT_labels_self l Mc s mb 0 _ _ hI _).mpr ⟨⟨hxl, hx⟩, trivial⟩
  have hIT : I ∈ (bf.mainTree Mc s mb).cells := A.cells_mem_tree hI
  refine ⟨cellColumnLp (bf.mainTree Mc s mb) Am hIT ⟨_, hv⟩, ?_⟩
  change colRelabel (bf.rv Mc s) (cellColumnLp (bf.mainTree Mc s mb) Am hIT ⟨_, hv⟩) = _
  rw [cellColumnLp_eq_wColumn]
  exact colRelabel_wColumn (f := bf.rv Mc s) (φ' := mainScalar Mc (bf.origCols l) s)
    (ε' := mainWeight Mc (bf.origCols l)) rfl rfl
    (cellColumn_memLp (bf.mainTree Mc s mb) Am hIT hv)
    (bf.origCol_memLp l s hx)

/-- The basic input on an active cell has only relevant main coordinates. -/
theorem basicIn_mem_range (Mc : ℕ) (s : List (CatCol bf.Vtx)) (mb : bf.MainBudget s) (l : Fin 4)
    {I : ℤ × ℤ} (hI : I ∈ A.cells) :
    bf.basicIn Mc l I ∈ LinearMap.range (colRelabel (bf.rv Mc s)).toLinearMap := by
  have hfam : ∀ j : Fin 2, ∀ hID : I ∈ (bf.P l j).Ψ.D.cells, ∀ Z,
      bf.famEmb Mc l j (cellColumnProjection (bf.P l j).Ψ.D (bf.P l j).Ψ.A hID Z) ∈
        LinearMap.range (colRelabel (bf.rv Mc s)).toLinearMap := by
    intro j hID Z
    have hle : Submodule.map (bf.famEmb Mc l j).toLinearMap
        (cellColumnRange (bf.P l j).Ψ.D (bf.P l j).Ψ.A hID) ≤
          LinearMap.range (colRelabel (bf.rv Mc s)).toLinearMap := by
      unfold cellColumnRange
      rw [Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨v, rfl⟩, rfl⟩
      change bf.famEmb Mc l j (cellColumnLp (bf.P l j).Ψ.D (bf.P l j).Ψ.A hID v) ∈ _
      rw [bf.famEmb_cellColumn Mc s l j hI hID v]
      exact bf.origCol_mem_range l Mc s mb hI rfl ⟨hI, v.2⟩
    exact hle (Submodule.mem_map_of_mem (cellColumnProjection_mem _ _ hID Z))
  rw [bf.basicIn_eq Mc l hI]
  exact Submodule.sub_mem _ (hfam 0 _ _) (hfam 1 _ _)

end ActiveSetup.BasicFamilies

namespace ActiveSetup.BasicFamilies.FamParams
variable {κ : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ c₀} {bf : A.BasicFamilies}
  (fp : bf.FamParams)

/-- Blueprint line 1859: on an active cell the shared history of a basic `B` slot is the cell
restriction of the global shared history at the depth of the cell acting on the global basic input
(the fixed signed sum of the basic depth projections of the family inputs `F_l`), relabeled from
the relevant main labels. -/
theorem basic_history (l : Fin 4) (s : List (CatCol bf.Vtx)) (mb : bf.MainBudget s)
    (ls : List (ℕ × Bool)) {I : ℤ × ℤ} (hI : I ∈ A.cells) :
    layerOp (fun m => fp.cumFilt l s I m) ls (bf.basicIn fp.Mc l I) =
      columnL2Restriction (dyadicGridCell A.G I.1 I.2) (dyadicGridCell_measurable A.G I.1 I.2)
        (colRelabel (bf.rv fp.Mc s) (fp.gHist l s mb ls I.1
          (ContinuousLinearMap.adjoint (colRelabel (bf.rv fp.Mc s)) (bf.gBasic fp.Mc l I.1)))) := by
  rw [fp.hist_bridge l s mb ls hI, ← colRelabel_restrict, ← colRelabel_adjoint_restrict]
  change _ = layerOp (fun m => fp.cumFilt l s I m) ls (colRelabel (bf.rv fp.Mc s)
    (ContinuousLinearMap.adjoint (colRelabel (bf.rv fp.Mc s)) (bf.basicIn fp.Mc l I)))
  rw [colRelabel_adjoint_of_mem_range (bf.rv_injective fp.Mc s)
    (bf.basicIn_mem_range fp.Mc s mb l hI)]

/-- Blueprint line 1859, the leaf outputs of a basic `B` slot: on an active cell the ball output
`Z_{l,G,s} = L_{l,G,s} B_{l,s} B_l` is the cell restriction of the global ball filter applied to the
global shared history of the global basic input. -/
theorem basic_leaf_out (l : Fin 4) (s : List (CatCol bf.Vtx)) (mb : bf.MainBudget s)
    (ls : List (ℕ × Bool)) (G : bf.Grp) (j : ℕ) {I : ℤ × ℤ} (hI : I ∈ A.cells) :
    fp.ballFilt l s I G j (layerOp (fun m => fp.cumFilt l s I m) ls (bf.basicIn fp.Mc l I)) =
      columnL2Restriction (dyadicGridCell A.G I.1 I.2) (dyadicGridCell_measurable A.G I.1 I.2)
        (colRelabel (bf.rv fp.Mc s) (fp.gBall l s mb G j I.1 (fp.gHist l s mb ls I.1
          (ContinuousLinearMap.adjoint (colRelabel (bf.rv fp.Mc s))
            (bf.gBasic fp.Mc l I.1))))) := by
  rw [fp.basic_history l s mb ls hI, fp.ball_bridge l s mb G j hI]

/-- Blueprint line 1859 (the compression loss): rows on the main column space that are Bessel with
constant `B` and local to active decision cells `u_i` remain Bessel after inserting, at the depth
of each decision cell, the global shared history of the slot `l` and the basic depth projection of
the family `(l, j)` acting on an input `Z` of the family (e.g. `F_{l,j}` or `1_R F_{l,j}`), at the
cost of the complement compression of the main tree for `|ls|` factors and the one-factor
compression of the basic tree. -/
theorem basic_compression {F ι : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [Fintype ι]
    (l : Fin 4) (s : List (CatCol bf.Vtx)) (mb : bf.MainBudget s) (ls : List (ℕ × Bool))
    (j : Fin 2) (u : ι → ℤ × ℤ) (hu : ∀ i, u i ∈ A.cells)
    (R : ι → ColumnL2 (bf.Lab ⊕ Fin fp.Mc) →L[ℂ] F) {B : ℝ} (hB : 0 ≤ B)
    (hR : ∀ x, ∑ i, ‖R i x‖ ^ 2 ≤ B * ‖x‖ ^ 2)
    (hloc : ∀ i, (R i).comp (columnL2Restriction (dyadicGridCell A.G (u i).1 (u i).2)
      (dyadicGridCell_measurable A.G (u i).1 (u i).2)) = R i) (Z : ColumnL2 (bf.P l j).V) :
    ∑ i, ‖R i (colRelabel (bf.rv fp.Mc s) (fp.gHist l s mb ls (u i).1
        (ContinuousLinearMap.adjoint (colRelabel (bf.rv fp.Mc s))
          (bf.famEmb fp.Mc l j ((bf.P l j).Ψ.proj (u i).1 Z)))))‖ ^ 2 ≤
      B * compressionC (bf.mainTree fp.Mc s mb) ls.length ^ 2 *
        compression1 (bf.P l j).Ψ.D ^ 2 * ‖Z‖ ^ 2 := by
  set ι' := colRelabel (bf.rv fp.Mc s)
  set ιA := ContinuousLinearMap.adjoint ι'
  set E := bf.famEmb fp.Mc l j
  set Ψ := (bf.P l j).Ψ
  have huT : ∀ i, u i ∈ (bf.mainTree fp.Mc s mb).cells := fun i => A.cells_mem_tree (hu i)
  have huD : ∀ i, u i ∈ Ψ.D.cells := fun i =>
    (Ψ.partition (u i).1).subset (bf.famCell_mem l j (hu i))
  set! Lc : ι → ℕ → ColumnL2 (bf.RLab fp.Mc s) →L[ℂ] ColumnL2 (bf.RLab fp.Mc s) := fun i m =>
    opAvg fun p => cellColumnProjection (bf.mainTree fp.Mc s mb) (fp.cumMaskT l s mb m p) (huT i)
  set! ρ : ι → ColumnL2 (bf.RLab fp.Mc s) →L[ℂ] ColumnL2 (bf.RLab fp.Mc s) := fun i =>
    columnL2Restriction (dyadicGridCell A.G (u i).1 (u i).2)
      (dyadicGridCell_measurable A.G (u i).1 (u i).2)
  -- the global history at a decision cell is the local layer product
  have hcell : ∀ i z, ρ i (fp.gHist l s mb ls (u i).1 z) = layerOp (Lc i) ls (ρ i z) := fun i z =>
    globHist_restrict (bf.mainBase fp.Mc s mb) (fp.cumMaskT l s mb) ls (u i).1
      (bf.mem_partition_mainBase fp.Mc s mb (hu i)) z
  have hLcom : ∀ i, (layerOp (Lc i) ls).comp (ρ i) = (ρ i).comp (layerOp (Lc i) ls) := by
    intro i
    refine layerOp_commute _ _ (fun m => opAvg_commute _ _ fun p => ?_) ls
    have h' := cellColumnProjection_restrict (bf.mainTree fp.Mc s mb) (fp.cumMaskT l s mb m p)
      (huT i)
    exact h'.2.trans h'.1.symm
  -- the rows after the history
  set! Q : ι → ColumnL2 (bf.P l j).V →L[ℂ] F := fun i =>
    (R i).comp (ι'.comp ((layerOp (Lc i) ls).comp (ιA.comp E)))
  have hA : ∀ (t : Set ℝ) (ht : MeasurableSet t) (w : ColumnL2 (bf.Lab ⊕ Fin fp.Mc)),
      ιA (columnL2Restriction t ht w) = columnL2Restriction t ht (ιA w) :=
    fun t ht w => colRelabel_adjoint_restrict _ t ht w
  have hι : ∀ (t : Set ℝ) (ht : MeasurableSet t) (y : ColumnL2 (bf.RLab fp.Mc s)),
      ι' (columnL2Restriction t ht y) = columnL2Restriction t ht (ι' y) :=
    fun t ht y => colRelabel_restrict _ t ht y
  have hE : ∀ (t : Set ℝ) (ht : MeasurableSet t) (y : ColumnL2 (bf.P l j).V),
      E (columnL2Restriction t ht y) = columnL2Restriction t ht (E y) :=
    fun t ht y => colRelabel_restrict _ t ht y
  have hterm : ∀ i, R i (ι' (fp.gHist l s mb ls (u i).1 (ιA (E (Ψ.proj (u i).1 Z))))) =
      Q i (cellColumnProjection Ψ.D Ψ.A (huD i) Z) := by
    intro i
    have h1 : R i (ι' (fp.gHist l s mb ls (u i).1 (ιA (E (Ψ.proj (u i).1 Z))))) =
        R i (columnL2Restriction (dyadicGridCell A.G (u i).1 (u i).2)
          (dyadicGridCell_measurable A.G (u i).1 (u i).2)
          (ι' (fp.gHist l s mb ls (u i).1 (ιA (E (Ψ.proj (u i).1 Z)))))) := by
      conv_lhs => rw [← hloc i]
      rfl
    rw [h1, ← hι]
    change R i (ι' (ρ i (fp.gHist l s mb ls (u i).1 (ιA (E (Ψ.proj (u i).1 Z)))))) = _
    rw [hcell i]
    have h2 : ρ i (ιA (E (Ψ.proj (u i).1 Z))) =
        ιA (E (cellColumnProjection Ψ.D Ψ.A (huD i) Z)) := by
      change columnL2Restriction _ _ (ιA _) = _
      rw [← hA, ← hE]
      congr 2
      exact bf.fam_restrict l j (hu i) _
    rw [h2]
    rfl
  simp_rw [hterm]
  -- the Bessel bound of the rows after the history
  have hRι : ∀ y, ∑ i, ‖(R i).comp ι' y‖ ^ 2 ≤ B * ‖y‖ ^ 2 := by
    intro y
    have := hR (ι' y)
    simp only [ContinuousLinearMap.comp_apply]
    rwa [show ‖ι' y‖ = ‖y‖ from norm_colRelabel (bf.rv_injective fp.Mc s) y] at this
  have hlocι : ∀ i, ((R i).comp ι').comp (ρ i) = (R i).comp ι' := by
    intro i
    rw [ContinuousLinearMap.comp_assoc, colRelabel_comp_restrict, ← ContinuousLinearMap.comp_assoc,
      hloc i]
  have hC0 := compressionC_nonneg (bf.mainTree fp.Mc s mb) ls.length
  have hQ : ∀ x, ∑ i ∈ Finset.univ, ‖Q i x‖ ^ 2 ≤
      (B * compressionC (bf.mainTree fp.Mc s mb) ls.length ^ 2) * ‖x‖ ^ 2 := by
    intro x
    have h := rows_layer_compression (bf.mainTree fp.Mc s mb) ls fp.hP (fp.cumMaskT l s mb) u huT
      (fun i m p => cellColumnProjection (bf.mainTree fp.Mc s mb) (fp.cumMaskT l s mb m p) (huT i))
      (fun _ _ _ => rfl) (fun i => (R i).comp ι') hB hRι hlocι (ιA (E x))
    have hn : ‖ιA (E x)‖ ≤ ‖x‖ := by
      refine (norm_colRelabel_adjoint_le (bf.rv_injective fp.Mc s) _).trans ?_
      exact (norm_colRelabel (bf.famEmb_injective fp.Mc l j) x).le
    refine le_of_eq_of_le ?_ (h.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) hn 2) (by positivity)))
    rfl
  have hg : Ψ.D.grid = A.G := (bf.P l j).grid
  have hQloc : ∀ i ∈ Finset.univ, (Q i).comp (columnL2Restriction
      (dyadicGridCell Ψ.D.grid (u i).1 (u i).2)
      (dyadicGridCell_measurable Ψ.D.grid (u i).1 (u i).2)) = Q i := by
    intro i _
    rw [hg]
    refine ContinuousLinearMap.ext fun x => ?_
    simp only [Q, ContinuousLinearMap.comp_apply]
    rw [hE, hA]
    have h3 := DFunLike.congr_fun (hLcom i) (ιA (E x))
    simp only [ContinuousLinearMap.comp_apply] at h3
    change R i (ι' (layerOp (Lc i) ls (ρ i (ιA (E x))))) = _
    rw [h3]
    change R i (ι' (columnL2Restriction _ _ _)) = _
    rw [hι]
    exact DFunLike.congr_fun (hloc i) _
  have h := rows_projection_compression Ψ.D Ψ.A Finset.univ u huD Q (by positivity) hQ hQloc
    Z
  simpa only [Finset.sum_const] using h

end ActiveSetup.BasicFamilies.FamParams

namespace ActiveSetup.BasicFamilies
variable {κ : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ c₀} (bf : A.BasicFamilies)

/-- The basic input of a cell has no template coordinates (blueprint line 1805: original labels
have rank zero). -/
theorem basicIn_fresh (Mc : ℕ) (l : Fin 4) (I : ℤ × ℤ) : MainFresh Mc 0 (bf.basicIn Mc l I) := by
  unfold basicIn gBasic famEmb
  exact ((colRelabel_inl_fresh (fun v : (bf.P l 0).V => (⟨l, 0, v⟩ : bf.Lab)) _).sub
    (colRelabel_inl_fresh (fun v : (bf.P l 1).V => (⟨l, 1, v⟩ : bf.Lab)) _)).restrict _ _

/-- The basic input of a cell vanishes off the cell. -/
theorem basicIn_support (Mc : ℕ) (l : Fin 4) (I : ℤ × ℤ) :
    ∀ᵐ y ∂volume, y ∉ dyadicGridCell A.G I.1 I.2 →
      (bf.basicIn Mc l I : ℝ → ColumnHilbert (bf.Lab ⊕ Fin Mc)) y = 0 := by
  change ∀ᵐ y ∂volume, y ∉ dyadicGridCell A.G I.1 I.2 →
    (columnL2Indicator _ (dyadicGridCell_measurable A.G I.1 I.2) (bf.gBasic Mc l I.1) :
      ℝ → ColumnHilbert (bf.Lab ⊕ Fin Mc)) y = 0
  filter_upwards [columnL2Indicator_coeFn _ (dyadicGridCell_measurable A.G I.1 I.2)
    (bf.gBasic Mc l I.1)] with y hy hyI
  rw [hy, Set.indicator_of_notMem hyI]

open scoped Classical in
/-- On an active cell the basic input is a combination of the original columns of the slot
available there (blueprint lines 1611, 1859: the basic guard slot input of prop:localize). -/
theorem basicIn_comb (Mc : ℕ) (s : List (CatCol bf.Vtx)) (l : Fin 4) {I : ℤ × ℤ}
    (hI : I ∈ A.cells) :
    ∃ cb : bf.Lab → ℂ, bf.basicIn Mc l I = ∑ v ∈ Finset.univ.filter
      (fun v => (bf.origCols l).avail I v),
        cb v • mainCol A.G Mc (bf.origCols l) s I (Sum.inl v) := by
  have hID : ∀ j : Fin 2, I ∈ (bf.P l j).Ψ.D.cells := fun j =>
    ((bf.P l j).Ψ.partition I.1).subset (bf.famCell_mem l j hI)
  have hex : ∀ j : Fin 2, ∃ a : {v // v ∈ (bf.P l j).Ψ.A.labels I} → ℂ,
      ∑ v, a v • cellColumnLp (bf.P l j).Ψ.D (bf.P l j).Ψ.A (hID j) v =
        cellColumnProjection (bf.P l j).Ψ.D (bf.P l j).Ψ.A (hID j) (bf.P l j).Z := fun j =>
    (cellColumnRange_mem_iff _ _ _ _).mp (cellColumnProjection_mem _ _ _ _)
  choose a ha using hex
  have hemb : ∀ j : Fin 2, bf.famEmb Mc l j
      (cellColumnProjection (bf.P l j).Ψ.D (bf.P l j).Ψ.A (hID j) (bf.P l j).Z) =
        ∑ v, a j v • mainCol A.G Mc (bf.origCols l) s I (Sum.inl ⟨l, j, v.1⟩) := by
    intro j
    rw [← ha j, map_sum]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [map_smul, bf.famEmb_cellColumn Mc s l j hI (hID j) v]
  refine ⟨fun x => ∑ j : Fin 2, ∑ v : {v // v ∈ (bf.P l j).Ψ.A.labels I},
    if (⟨l, j, v.1⟩ : bf.Lab) = x then (-1 : ℂ) ^ (j : ℕ) * a j v else 0, ?_⟩
  rw [bf.basicIn_eq Mc l hI, hemb 0, hemb 1]
  simp only [Finset.sum_smul, ite_smul, zero_smul]
  rw [Finset.sum_comm]
  have hin : ∀ (j : Fin 2) (v : {v // v ∈ (bf.P l j).Ψ.A.labels I}),
      (⟨l, j, v.1⟩ : bf.Lab) ∈ Finset.univ.filter (fun v => (bf.origCols l).avail I v) :=
    fun j v => Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl, hI, v.2⟩
  have hj : ∀ j : Fin 2, ∑ x ∈ Finset.univ.filter (fun v => (bf.origCols l).avail I v),
      ∑ v : {v // v ∈ (bf.P l j).Ψ.A.labels I}, (if (⟨l, j, v.1⟩ : bf.Lab) = x then
        ((-1 : ℂ) ^ (j : ℕ) * a j v) • mainCol A.G Mc (bf.origCols l) s I (Sum.inl x) else 0) =
      ∑ v : {v // v ∈ (bf.P l j).Ψ.A.labels I}, ((-1 : ℂ) ^ (j : ℕ) * a j v) •
        mainCol A.G Mc (bf.origCols l) s I (Sum.inl ⟨l, j, v.1⟩) := by
    intro j
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [Finset.sum_ite_eq, ite_eq_left_of_eq_true _ _ (eq_true (hin j v))]
  rw [Fin.sum_univ_two, hj 0, hj 1]
  simp only [Fin.val_zero, pow_zero, one_mul, Fin.val_one, pow_one, neg_one_mul, neg_smul,
    Finset.sum_neg_distrib, ← sub_eq_add_neg]

/-- The physical coordinate of the basic input of an active cell is the basic argument `B_l` on the
cell (blueprint prop:base line 1611). -/
theorem basicIn_phys (Mc : ℕ) (l : Fin 4) {I : ℤ × ℤ} (hI : I ∈ A.cells) :
    augPhys (bf.basicIn Mc l I) =ᵐ[volume] (dyadicGridCell A.G I.1 I.2).indicator (A.B l I) := by
  have hval : ∀ j : Fin 2, ∀ᵐ y ∂volume, y ∈ dyadicGridCell A.G I.1 I.2 →
      augPhys ((bf.P l j).Ψ.proj I.1 (bf.P l j).Z) y = (bf.P l j).val I y := by
    intro j
    set Ψ := (bf.P l j).Ψ
    have hg : Ψ.D.grid = A.G := (bf.P l j).grid
    have hsub : dyadicGridCell Ψ.D.grid I.1 I.2 ⊆
        dyadicGridCell Ψ.D.grid Ψ.D.root.1 Ψ.D.root.2 := by
      rw [hg]; exact (A.sub I hI).trans (bf.P l j).root_sub
    have hroot : Ψ.D.root.1 ≤ I.1 := dyadicGridCell_depth_le_of_subset _ I _ hsub
    have hQ := Ψ.anc_mem_partition hsub hroot
    have hQc : Ψ.anc I ∈ Ψ.D.cells := (Ψ.partition I.1).subset hQ
    have hae := (ae_restrict_iff' (dyadicGridCell_measurable _ _ _)).mp
      (Ψ.proj_ae_cell I.1 (bf.P l j).Z hQ)
    filter_upwards [hae] with y hy hyI
    have hyI' : y ∈ dyadicGridCell Ψ.D.grid I.1 I.2 := by rw [hg]; exact hyI
    have h1 := hy (Ψ.cell_sub_anc I hyI')
    unfold augPhys BasicProjection.val ColumnDepthFamily.currentZ
    rw [dite_eq_left_of_eq_true (eq_true hQc), h1]
  have h1 := augPhys_restrict (dyadicGridCell A.G I.1 I.2) (dyadicGridCell_measurable A.G I.1 I.2)
    (bf.gBasic Mc l I.1)
  have h2 := augPhys_sub (bf.famEmb Mc l 0 ((bf.P l 0).Ψ.proj I.1 (bf.P l 0).Z))
    (bf.famEmb Mc l 1 ((bf.P l 1).Ψ.proj I.1 (bf.P l 1).Z))
  have h30 := augPhys_colRelabel (fun v => (Sum.inl ⟨l, 0, v⟩ : bf.Lab ⊕ Fin Mc))
    ((bf.P l 0).Ψ.proj I.1 (bf.P l 0).Z)
  have h31 := augPhys_colRelabel (fun v => (Sum.inl ⟨l, 1, v⟩ : bf.Lab ⊕ Fin Mc))
    ((bf.P l 1).Ψ.proj I.1 (bf.P l 1).Z)
  filter_upwards [h1, h2, h30, h31, hval 0, hval 1, bf.rep l I hI] with y e1 e2 e30 e31 v0 v1 hrep
  change augPhys (columnL2Restriction _ _ (bf.gBasic Mc l I.1)) y = _
  rw [e1]
  by_cases hy : y ∈ dyadicGridCell A.G I.1 I.2
  · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, hrep hy]
    unfold gBasic
    rw [e2, Pi.sub_apply]
    unfold famEmb
    rw [e30, e31, v0 hy, v1 hy]
  · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy]

/-! ### The zero convention and the retained inherited projections (blueprint line 1859) -/

/-- Above the attempt (no active cell contains the cell) the inherited masks of the main tree are
empty (blueprint line 1859: before an attempt the outputs are zero). -/
theorem mainMaskT_labels_none (l : Fin 4) (Mc : ℕ) (s : List (CatCol bf.Vtx))
    (mb : bf.MainBudget s) (r : ℕ) (M : ℤ × ℤ → bf.Vtx → Prop)
    (hM : ∀ c ∈ A.cells, ∀ d ∈ A.cells, dyadicGridCell A.G c.1 c.2 ⊆ dyadicGridCell A.G d.1 d.2 →
      ∀ x, M d x → M c x) {c : ℤ × ℤ} (hc : deepAnc (A := A) c = none) :
    (bf.mainMaskT l Mc s mb r M hM).labels c = ∅ := by
  classical
  change (match deepAnc (A := A) c with
    | none => ∅
    | some a => Finset.univ.filter fun v : bf.RLab Mc s => bf.mainPred l s a r (M a) v.1) = ∅
  rw [hc]

/-- Between actual uses the inherited projections are retained (blueprint line 1859): at a cell of
the tree whose deepest active ancestor is `a`, the masks of the main tree are those of `a`. -/
theorem mainMaskT_labels_retain (l : Fin 4) (Mc : ℕ) (s : List (CatCol bf.Vtx))
    (mb : bf.MainBudget s) (r : ℕ) (M : ℤ × ℤ → bf.Vtx → Prop)
    (hM : ∀ c ∈ A.cells, ∀ d ∈ A.cells, dyadicGridCell A.G c.1 c.2 ⊆ dyadicGridCell A.G d.1 d.2 →
      ∀ x, M d x → M c x) {c a : ℤ × ℤ} (hc : deepAnc (A := A) c = some a) :
    (bf.mainMaskT l Mc s mb r M hM).labels c = (bf.mainMaskT l Mc s mb r M hM).labels a := by
  classical
  have ha : deepAnc (A := A) a = some a := deepAnc_self (deepAnc_spec hc).1
  change (match deepAnc (A := A) c with
    | none => ∅
    | some a => Finset.univ.filter fun v : bf.RLab Mc s => bf.mainPred l s a r (M a) v.1) =
    (match deepAnc (A := A) a with
    | none => ∅
    | some a => Finset.univ.filter fun v : bf.RLab Mc s => bf.mainPred l s a r (M a) v.1)
  rw [hc, ha]

/-- Above the attempt the main cell projections vanish. -/
theorem mainCellProj_none (l : Fin 4) (Mc : ℕ) (s : List (CatCol bf.Vtx))
    (mb : bf.MainBudget s) (r : ℕ) (M : ℤ × ℤ → bf.Vtx → Prop)
    (hM : ∀ c ∈ A.cells, ∀ d ∈ A.cells, dyadicGridCell A.G c.1 c.2 ⊆ dyadicGridCell A.G d.1 d.2 →
      ∀ x, M d x → M c x) {c : ℤ × ℤ} (hcT : c ∈ (bf.mainTree Mc s mb).cells)
    (hc : deepAnc (A := A) c = none) :
    cellColumnProjection (bf.mainTree Mc s mb) (bf.mainMaskT l Mc s mb r M hM) hcT = 0 := by
  have hR : cellColumnRange (bf.mainTree Mc s mb) (bf.mainMaskT l Mc s mb r M hM) hcT = ⊥ := by
    unfold cellColumnRange
    rw [Submodule.span_eq_bot]
    rintro _ ⟨⟨v, hv⟩, rfl⟩
    rw [bf.mainMaskT_labels_none l Mc s mb r M hM hc] at hv
    exact absurd hv (Finset.notMem_empty _)
  refine ContinuousLinearMap.ext fun z => ?_
  change (cellColumnRange (bf.mainTree Mc s mb) (bf.mainMaskT l Mc s mb r M hM) hcT).starProjection
    z = 0
  rw [starProjection_congr hR z, Submodule.starProjection_bot]
  rfl

end ActiveSetup.BasicFamilies

namespace ActiveSetup.BasicFamilies.FamParams
variable {κ : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ c₀} {bf : A.BasicFamilies}
  (fp : bf.FamParams)

/-- Blueprint line 1859 (zero convention): on a cell of the depth partition lying above the attempt
(contained in no active cell) the global ball outputs vanish. -/
theorem gBall_zero_before (l : Fin 4) (s : List (CatCol bf.Vtx)) (mb : bf.MainBudget s)
    (G : bf.Grp) (j : ℕ) (h : ℤ) {c : ℤ × ℤ} (hc : c ∈ ((bf.mainBase fp.Mc s mb).partition h).cells)
    (hnone : deepAnc (A := A) c = none) (z : ColumnL2 (bf.RLab fp.Mc s)) :
    columnL2Restriction (dyadicGridCell A.G c.1 c.2) (dyadicGridCell_measurable A.G c.1 c.2)
      (fp.gBall l s mb G j h z) = 0 := by
  have hp : ∀ p : Fin fp.P, columnL2Restriction (dyadicGridCell A.G c.1 c.2)
      (dyadicGridCell_measurable A.G c.1 c.2)
      (((bf.mainBase fp.Mc s mb).withMask (fp.ballMaskT l s mb G j p)).proj h z) = 0 := by
    intro p
    have hcT : c ∈ (bf.mainTree fp.Mc s mb).cells :=
      ((bf.mainBase fp.Mc s mb).partition h).subset hc
    have h1 : (columnL2Restriction (dyadicGridCell A.G c.1 c.2)
        (dyadicGridCell_measurable A.G c.1 c.2)).comp
        (((bf.mainBase fp.Mc s mb).withMask (fp.ballMaskT l s mb G j p)).proj h) =
        cellColumnProjection (bf.mainTree fp.Mc s mb) (fp.ballMaskT l s mb G j p) hcT :=
      (((bf.mainBase fp.Mc s mb).withMask (fp.ballMaskT l s mb G j p)).restrict_proj h hc).1
    have h2 : cellColumnProjection (bf.mainTree fp.Mc s mb) (fp.ballMaskT l s mb G j p) hcT = 0 :=
      bf.mainCellProj_none l fp.Mc s mb _ _ _ hcT hnone
    rw [← ContinuousLinearMap.comp_apply (columnL2Restriction _ _), h1, h2]
    rfl
  unfold gBall opAvg
  simp only [smul_apply, FunLike.coe_sum, Finset.sum_apply,
    map_smul, map_sum, hp, Finset.sum_const_zero, smul_zero]

end ActiveSetup.BasicFamilies.FamParams

/-! ### The compression loss `G₀` (blueprint lines 1670, 1859) -/

section CompressionLoss
variable {V : Type*} [Fintype V]

/-- The complement compression for `n = O(log k)` factors in a column tree with
`log (2 budget) ≤ k^c` is a small overhead `G₀ = exp(C_q (1 + log 2k)^2)` (eq:small-overhead). -/
theorem compressionC_le_overhead (D : ColumnTreeData V) (n c : ℕ) {k : ℝ} (hk : 1 ≤ k)
    (hD : Real.log (2 * D.budget) ≤ k ^ c) (hn : (n : ℝ) ≤ c * (Real.log k + 1)) :
    compressionC D n ≤
      Real.exp (1024 * (c + 1) * (1024 * (c + 1) + c + 7) * (1 + Real.log (2 * k)) ^ 2) := by
  have hL1 : 1 ≤ Real.log (2 * D.budget) := columnBudget_log_one_le D
  have hn0 : (1 : ℝ) ≤ (n : ℝ) + 1 := by have := Nat.cast_nonneg (α := ℝ) n; linarith
  obtain ⟨t, ht1, hlt, hC⟩ : ∃ t : ℝ, 1 ≤ t ∧ Real.log t = 1024 * Real.log ((n : ℝ) + 1) ∧
      compressionC D n = (1024 * t * Real.log (2 * D.budget)) ^ (1024 * (n + 1)) :=
    ⟨((n : ℝ) + 1) ^ 1024, one_le_pow₀ hn0, by rw [Real.log_pow]; push_cast; ring, rfl⟩
  obtain ⟨L, hLe, hL1'⟩ : ∃ L : ℝ, L = Real.log (2 * D.budget) ∧ 1 ≤ L := ⟨_, rfl, hL1⟩
  rw [← hLe] at hC hD
  obtain ⟨X, hXe⟩ : ∃ X : ℝ, X = 1 + Real.log (2 * k) := ⟨_, rfl⟩
  rw [← hXe]
  have hlogk : 0 ≤ Real.log k := Real.log_nonneg hk
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog2k : Real.log (2 * k) = Real.log 2 + Real.log k :=
    Real.log_mul (by norm_num) (by linarith)
  have hkX : Real.log k + 1 ≤ X := by rw [hXe, hlog2k]; linarith
  have hX1 : 1 ≤ X := by linarith
  have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg c
  have hn1 : (n : ℝ) + 1 ≤ (c + 1) * X := by nlinarith only [hn, hkX, hX1]
  have htL : 1 ≤ t * L := one_le_mul_of_one_le_of_one_le ht1 hL1'
  have hb1 : 1 ≤ 1024 * t * L := by nlinarith only [ht1, hL1']
  have hb0 : 0 < 1024 * t * L := by linarith
  have hlogb : Real.log (1024 * t * L) ≤ (1024 * (c + 1) + c + 7) * X := by
    rw [Real.log_mul (by positivity) (by linarith), Real.log_mul (by norm_num) (by linarith), hlt]
    have h1 : Real.log 1024 ≤ 7 := by
      have : Real.log 1024 = 10 * Real.log 2 := by
        rw [show (1024 : ℝ) = 2 ^ 10 by norm_num, Real.log_pow]; norm_num
      rw [this]; have := Real.log_two_lt_d9; linarith
    have h2 : Real.log ((n : ℝ) + 1) ≤ (c + 1) * X := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (n : ℝ) + 1 by linarith)
      linarith
    have h3 : Real.log L ≤ c * X := by
      have hLk : Real.log L ≤ Real.log (k ^ c) := Real.log_le_log (by linarith) hD
      rw [Real.log_pow] at hLk
      have : (c : ℝ) * Real.log k ≤ c * X := mul_le_mul_of_nonneg_left (by linarith) hc0
      linarith
    nlinarith only [hXe, hlogk, hlog2, hlog2k, h1, h2, h3]
  rw [hC, ← Real.exp_log (pow_pos hb0 _), Real.exp_le_exp, Real.log_pow]
  have hlb0 : 0 ≤ Real.log (1024 * t * L) := Real.log_nonneg hb1
  push_cast
  calc (1024 * ((n : ℝ) + 1)) * Real.log (1024 * t * L) ≤
      (1024 * ((c + 1) * X)) * ((1024 * (c + 1) + c + 7) * X) := by gcongr
    _ = 1024 * (c + 1) * (1024 * (c + 1) + c + 7) * X ^ 2 := by ring

/-- The one-factor compression constant is at most the complement compression constant for one
factor. -/
theorem compression1_le_compressionC (D : ColumnTreeData V) :
    compression1 D ≤ compressionC D 1 := by
  have hL1 : 1 ≤ Real.log (2 * D.budget) := columnBudget_log_one_le D
  have hu : (1 : ℝ) ≤ ((1 : ℕ) : ℝ) + 1 := by norm_num
  obtain ⟨P5, P10, p1, q1, hC1, hCC⟩ : ∃ P5 P10 : ℝ, P5 ≤ P10 ∧ 1 ≤ P5 ∧
      compression1 D = (512 * P5 * Real.log (2 * D.budget)) ^ (512 * (1 + 1)) ∧
      compressionC D 1 = (1024 * P10 * Real.log (2 * D.budget)) ^ (1024 * (1 + 1)) :=
    ⟨_, _, pow_le_pow_right₀ hu (by norm_num : 512 ≤ 1024), one_le_pow₀ hu, rfl, rfl⟩
  obtain ⟨L, hLe⟩ : ∃ L : ℝ, L = Real.log (2 * D.budget) := ⟨_, rfl⟩
  rw [hC1, hCC, ← hLe]
  rw [← hLe] at hL1
  have hPL : 1 ≤ P5 * L := one_le_mul_of_one_le_of_one_le q1 hL1
  have hb1 : (1 : ℝ) ≤ 512 * P5 * L := by nlinarith
  have hb12 : 512 * P5 * L ≤ 1024 * P10 * L := by nlinarith
  calc (512 * P5 * L) ^ (512 * (1 + 1)) ≤ (1024 * P10 * L) ^ (512 * (1 + 1)) :=
        pow_le_pow_left₀ (by linarith) hb12 _
    _ ≤ (1024 * P10 * L) ^ (1024 * (1 + 1)) :=
        pow_le_pow_right₀ (hb1.trans hb12) (by norm_num)

/-- Blueprint line 1859, "the compression loss is `G₀`": the loss of `basic_compression` for
histories of length `n ≤ c (log k + 1)` in a main tree and a basic tree with `log (2 budget) ≤ k^c`
is at most `G₀ = exp(C_q (1 + log 2k)^2)` with `C_q = 4096 (c+1) (1024 (c+1) + c + 7)`. -/
theorem compression_loss_le {W : Type*} [Fintype W] (D : ColumnTreeData V) (D' : ColumnTreeData W)
    (n c : ℕ) (hc : 1 ≤ c) {k : ℝ} (hk : 1 ≤ k) (hD : Real.log (2 * D.budget) ≤ k ^ c)
    (hD' : Real.log (2 * D'.budget) ≤ k ^ c) (hn : (n : ℝ) ≤ c * (Real.log k + 1)) :
    compressionC D n ^ 2 * compression1 D' ^ 2 ≤
      Real.exp (4096 * (c + 1) * (1024 * (c + 1) + c + 7) * (1 + Real.log (2 * k)) ^ 2) := by
  have h1 := compressionC_le_overhead D n c hk hD hn
  have hn1 : ((1 : ℕ) : ℝ) ≤ c * (Real.log k + 1) := by
    have := Real.log_nonneg hk
    have hc' : (1 : ℝ) ≤ c := by exact_mod_cast hc
    push_cast; nlinarith
  have h2 := (compression1_le_compressionC D').trans (compressionC_le_overhead D' 1 c hk hD' hn1)
  have h0 := compressionC_nonneg D n
  have h0' := compression1_nonneg D'
  obtain ⟨K, hKe⟩ : ∃ K : ℝ, K = 1024 * (c + 1) * (1024 * (c + 1) + c + 7) *
      (1 + Real.log (2 * k)) ^ 2 := ⟨_, rfl⟩
  rw [← hKe] at h1 h2
  have h3 : compressionC D n ^ 2 * compression1 D' ^ 2 ≤
      Real.exp K ^ 2 * Real.exp K ^ 2 :=
    mul_le_mul (pow_le_pow_left₀ h0 h1 2) (pow_le_pow_left₀ h0' h2 2) (sq_nonneg _) (sq_nonneg _)
  refine h3.trans (le_of_eq ?_)
  rw [← pow_add, ← Real.exp_nat_mul, hKe]
  congr 1
  push_cast
  ring

end CompressionLoss

namespace ActiveSetup.BasicFamilies
variable {κ : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ c₀} (bf : A.BasicFamilies)

open scoped Classical in
/-- The template path count of a catalog is at most the number of main labels at the deepest
template birth cell containing the point (blueprint line 1835: the main catalog budget is a path
count). -/
theorem tmplPath_le (Mc : ℕ) (s : List (CatCol bf.Vtx)) (hMc : s.length ≤ Mc) (l : Fin 4)
    (hb : ∀ e ∈ s, e.birth ∈ A.cells) {r : ℕ} (hr : ∀ e ∈ s, e.rank ≤ r) {N : ℝ} (hN0 : 0 ≤ N)
    (hN : ∀ I ∈ A.cells, ((mainLabels A.G Mc (bf.origCols l) s I r).card : ℝ) ≤ N) (y : ℝ) :
    (bf.tmplPath s y : ℝ) ≤ N := by
  set T := (Finset.range s.length).filter fun n => ∃ h : n < s.length,
    y ∈ dyadicGridCell A.G (s[n]'h).birth.1 (s[n]'h).birth.2
  change ((T.card : ℕ) : ℝ) ≤ N
  rcases T.eq_empty_or_nonempty with hT | hT
  · rw [hT, Finset.card_empty, Nat.cast_zero]; exact hN0
  obtain ⟨n₀, hn₀, hmax⟩ := T.exists_max_image (fun n => if h : n < s.length then
    (s[n]'h).birth.1 else 0) hT
  obtain ⟨-, hn₀s, hy₀⟩ := Finset.mem_filter.mp hn₀
  set I := (s[n₀]'hn₀s).birth
  have hI : I ∈ A.cells := hb _ (List.getElem_mem hn₀s)
  have hcard : T.card ≤ (mainLabels A.G Mc (bf.origCols l) s I r).card :=
    Finset.card_le_card_of_injOn (fun n => if h : n < Mc then (Sum.inr ⟨n, h⟩ : bf.Lab ⊕ Fin Mc)
      else Sum.inr ⟨0, by omega⟩)
      (fun n hn => by
        obtain ⟨-, hns, hyn⟩ := Finset.mem_filter.mp hn
        have hnM : n < Mc := by omega
        simp only [hnM, ↓reduceDIte]
        refine mem_mainLabels.mpr ⟨hns, ?_, hr _ (List.getElem_mem hns)⟩
        have hdep := hmax n hn
        simp only [hns, hn₀s, ↓reduceDIte] at hdep
        exact dyadicGridCell_subset_of_common_point A.G hy₀ hyn hdep)
      (fun n₁ hn₁ n₂ hn₂ h => by
        have h1 : n₁ < Mc := by have := (Finset.mem_filter.mp hn₁).2.1; omega
        have h2 : n₂ < Mc := by have := (Finset.mem_filter.mp hn₂).2.1; omega
        simp only [h1, h2, ↓reduceDIte, Sum.inr.injEq, Fin.mk.injEq] at h
        exact h)
  exact (Nat.cast_le.mpr hcard).trans (hN I hI)

/-- A main budget from catalog counts: if the main labels of rank at most `r` number at most `N` at
every active cell, then `8 colBudget + N` is a main budget (blueprint lines 1828, 1835). -/
noncomputable def MainBudget.ofCounts (Mc : ℕ) (s : List (CatCol bf.Vtx)) (hMc : s.length ≤ Mc)
    (l : Fin 4) (hb : ∀ e ∈ s, e.birth ∈ A.cells) {r : ℕ} (hr : ∀ e ∈ s, e.rank ≤ r) {N : ℝ}
    (hN0 : 0 ≤ N)
    (hN : ∀ I ∈ A.cells, ((mainLabels A.G Mc (bf.origCols l) s I r).card : ℝ) ≤ N) :
    bf.MainBudget s where
  hb := hb
  B := 8 * A.colBudget + N
  hTp := fun y => by
    have := bf.tmplPath_le Mc s hMc l hb hr hN0 hN y
    linarith

end ActiveSetup.BasicFamilies

/-! ## Certified variation on the main columns (blueprint lem:variation, lines 1861-1879) -/

/-! ### Generic variation lemmas (moved from Sec13_1, Sec13_3 and Sec13_4) -/

theorem dyadicGridCell_eq_of_meet (Gd : RealDyadicGrid) {I J : ℤ × ℤ} (hIJ : I.1 = J.1)
    (h : (dyadicGridCell Gd I.1 I.2 ∩ dyadicGridCell Gd J.1 J.2).Nonempty) : I = J := by
  obtain ⟨y, hyI, hyJ⟩ := h
  have h1 := dyadicIndex_eq hyI
  rw [hIJ] at h1
  have h2 := dyadicIndex_eq hyJ
  exact Prod.ext hIJ (h1.symm.trans h2)

section DepthBlocks2
variable {V : Type*} [Fintype V]

/-- A depth projection commutes with the restriction to a cell of a coarser depth partition. -/
theorem ColumnDepthFamily.proj_comm_restrict (Ψ : ColumnDepthFamily V) {h' h : ℤ} (hh : h' ≤ h)
    {Q : ℤ × ℤ} (hQ : Q ∈ (Ψ.partition h').cells) :
    (Ψ.proj h).comp (columnL2Restriction (dyadicGridCell Ψ.D.grid Q.1 Q.2)
      (dyadicGridCell_measurable Ψ.D.grid Q.1 Q.2)) =
    (columnL2Restriction (dyadicGridCell Ψ.D.grid Q.1 Q.2)
      (dyadicGridCell_measurable Ψ.D.grid Q.1 Q.2)).comp (Ψ.proj h) := by
  set rQ := columnL2Restriction (V := V) (dyadicGridCell Ψ.D.grid Q.1 Q.2)
    (dyadicGridCell_measurable Ψ.D.grid Q.1 Q.2)
  have hQd : Q.1 = Ψ.depth h' := ((Ψ.mem_partition h' Q).mp hQ).1
  have hcell : ∀ c : {c // c ∈ (Ψ.partition h).cells},
      (cellColumnProjection Ψ.D Ψ.A ((Ψ.partition h).subset c.2)).comp rQ =
        rQ.comp (cellColumnProjection Ψ.D Ψ.A ((Ψ.partition h).subset c.2)) := by
    intro c
    have hcd : c.1.1 = Ψ.depth h := ((Ψ.mem_partition h c.1).mp c.2).1
    have hle : Q.1 ≤ c.1.1 := by rw [hQd, hcd]; exact Ψ.depth_mono hh
    obtain ⟨hl, hr⟩ := cellColumnProjection_restrict Ψ.D Ψ.A ((Ψ.partition h).subset c.2)
    rcases dyadicGridCell_nested_or_disjoint_of_le Ψ.D.grid hle Q.2 c.1.2 with hdis | hsub
    · have e1 : (cellColumnProjection Ψ.D Ψ.A ((Ψ.partition h).subset c.2)).comp rQ = 0 := by
        rw [← hr, ContinuousLinearMap.comp_assoc, columnL2Restriction_comp_disjoint _ _
          hdis.symm, ContinuousLinearMap.comp_zero]
      have e2 : rQ.comp (cellColumnProjection Ψ.D Ψ.A ((Ψ.partition h).subset c.2)) = 0 := by
        rw [← hl, ← ContinuousLinearMap.comp_assoc, columnL2Restriction_comp_disjoint _ _ hdis,
          ContinuousLinearMap.zero_comp]
      rw [e1, e2]
    · have e1 : (cellColumnProjection Ψ.D Ψ.A ((Ψ.partition h).subset c.2)).comp rQ =
          cellColumnProjection Ψ.D Ψ.A ((Ψ.partition h).subset c.2) := by
        rw [← hr, ContinuousLinearMap.comp_assoc, columnL2Restriction_comp_of_subset _ _ hsub]
      have e2 : rQ.comp (cellColumnProjection Ψ.D Ψ.A ((Ψ.partition h).subset c.2)) =
          cellColumnProjection Ψ.D Ψ.A ((Ψ.partition h).subset c.2) := by
        rw [← hl, ← ContinuousLinearMap.comp_assoc, columnL2Restriction_comp_of_subset' _ _ hsub]
      rw [e1, e2]
  refine ContinuousLinearMap.ext fun z => ?_
  simp only [ContinuousLinearMap.comp_apply]
  change partitionColumnProjection Ψ.D Ψ.A (Ψ.partition h) (rQ z) =
    rQ (partitionColumnProjection Ψ.D Ψ.A (Ψ.partition h) z)
  rw [partitionColumnProjection_eq_sum, partitionColumnProjection_eq_sum, map_sum]
  exact Finset.sum_congr rfl fun c _ => DFunLike.congr_fun (hcell c) z

/-- Outputs of a depth projection vanish off the root. -/
theorem ColumnDepthFamily.proj_vanish (Ψ : ColumnDepthFamily V) (h : ℤ) (z : ColumnL2 V) :
    ∀ᵐ y ∂volume, y ∉ dyadicGridCell Ψ.D.grid Ψ.D.root.1 Ψ.D.root.2 →
      (Ψ.proj h z : ℝ → ColumnHilbert V) y = 0 := by
  change ∀ᵐ y ∂volume, y ∉ _ → (partitionColumnProjection Ψ.D Ψ.A (Ψ.partition h) z :
    ℝ → ColumnHilbert V) y = 0
  rw [partitionColumnProjection_eq_sum]
  have hall : ∀ᵐ y ∂volume, ∀ c : {c // c ∈ (Ψ.partition h).cells},
      y ∉ dyadicGridCell Ψ.D.grid Ψ.D.root.1 Ψ.D.root.2 →
        (cellColumnProjection Ψ.D Ψ.A ((Ψ.partition h).subset c.2) z :
          ℝ → ColumnHilbert V) y = 0 := by
    refine Filter.eventually_all.mpr fun c => ?_
    filter_upwards [cellColumnRange_ae_zero_off Ψ.D Ψ.A ((Ψ.partition h).subset c.2)
      (cellColumnProjection_mem Ψ.D Ψ.A ((Ψ.partition h).subset c.2) z)] with y hy hyr
    exact hy fun hyc => hyr (Ψ.D.below_root _ ((Ψ.partition h).subset c.2) hyc)
  filter_upwards [hall, Lp.coeFn_fun_finsetSum (Finset.univ : Finset {c // c ∈
    (Ψ.partition h).cells}) (fun c => cellColumnProjection Ψ.D Ψ.A
      ((Ψ.partition h).subset c.2) z)] with y hy h1 hyr
  rw [h1, Finset.sum_eq_zero fun c _ => hy c hyr]

/-- A column function (of any label type) vanishing off the root of a depth family splits
orthogonally over its depth partition. -/
theorem ColumnDepthFamily.norm_sq_partition' {W : Type*} [Fintype W]
    (Ψ : ColumnDepthFamily V) (h : ℤ) (v : ColumnL2 W)
    (hv : ∀ᵐ y ∂volume, y ∉ dyadicGridCell Ψ.D.grid Ψ.D.root.1 Ψ.D.root.2 →
      (v : ℝ → ColumnHilbert W) y = 0) :
    ‖v‖ ^ 2 = ∑ Q : {Q // Q ∈ (Ψ.partition h).cells},
      ‖columnL2Restriction (dyadicGridCell Ψ.D.grid Q.1.1 Q.1.2)
        (dyadicGridCell_measurable Ψ.D.grid Q.1.1 Q.1.2) v‖ ^ 2 := by
  classical
  set π := Ψ.partition h
  set! w : (ℤ × ℤ) → ColumnL2 W := fun Q => columnL2Restriction (dyadicGridCell Ψ.D.grid Q.1 Q.2)
    (dyadicGridCell_measurable Ψ.D.grid Q.1 Q.2) v
  have hw : ∀ Q, ∀ᵐ y ∂volume, y ∉ dyadicGridCell Ψ.D.grid Q.1 Q.2 →
      (w Q : ℝ → ColumnHilbert W) y = 0 := by
    intro Q
    filter_upwards [columnL2Indicator_coeFn _ (dyadicGridCell_measurable Ψ.D.grid Q.1 Q.2) v]
      with y hy hyQ
    change (columnL2Indicator _ (dyadicGridCell_measurable Ψ.D.grid Q.1 Q.2) v :
      ℝ → ColumnHilbert W) y = 0
    rw [hy, Set.indicator_of_notMem hyQ]
  have hsum : v = ∑ Q ∈ π.cells, w Q := by
    refine Lp.ext ?_
    have hall : ∀ᵐ y ∂volume, ∀ Q ∈ π.cells, (w Q : ℝ → ColumnHilbert W) y =
        (dyadicGridCell Ψ.D.grid Q.1 Q.2).indicator (v : ℝ → ColumnHilbert W) y := by
      rw [Filter.eventually_all_finset]
      intro Q _
      exact columnL2Indicator_coeFn _ (dyadicGridCell_measurable Ψ.D.grid Q.1 Q.2) v
    filter_upwards [hall, hv, Lp.coeFn_fun_finsetSum π.cells w] with y h1 h2 h3
    rw [h3, Finset.sum_congr rfl h1, ← Finset.indicator_biUnion_apply _ _ π.disjoint, π.cover]
    by_cases hy : y ∈ dyadicGridCell Ψ.D.grid Ψ.D.root.1 Ψ.D.root.2
    · rw [Set.indicator_of_mem hy]
    · rw [Set.indicator_of_notMem hy, h2 hy]
  conv_lhs => rw [hsum]
  rw [columnL2_norm_sq_sum_disjoint π.cells w (fun Q => dyadicGridCell Ψ.D.grid Q.1 Q.2)
    π.disjoint hw]
  exact (Finset.sum_coe_sort π.cells (fun Q => ‖w Q‖ ^ 2)).symm

/-- A column function vanishing off the root splits orthogonally over a depth partition. -/
theorem ColumnDepthFamily.norm_sq_partition (Ψ : ColumnDepthFamily V) (h : ℤ) (v : ColumnL2 V)
    (hv : ∀ᵐ y ∂volume, y ∉ dyadicGridCell Ψ.D.grid Ψ.D.root.1 Ψ.D.root.2 →
      (v : ℝ → ColumnHilbert V) y = 0) :
    ‖v‖ ^ 2 = ∑ Q : {Q // Q ∈ (Ψ.partition h).cells},
      ‖columnL2Restriction (dyadicGridCell Ψ.D.grid Q.1.1 Q.1.2)
        (dyadicGridCell_measurable Ψ.D.grid Q.1.1 Q.1.2) v‖ ^ 2 := by
  exact Ψ.norm_sq_partition' h v hv

end DepthBlocks2

section GlobalJumps
variable {V : Type*} [Fintype V]

/-- The interval rows of one nested depth family are Bessel (orthogonal increments) and split
orthogonally over the partition at their left depth. -/
theorem ColumnDepthFamily.interval_rows {ι : Type*} [Fintype ι] (Ψ : ColumnDepthFamily V)
    (r t : ι → ℕ) (hrt : ∀ i, r i ≤ t i)
    (hdis : ∀ i j, i ≠ j → Disjoint (Finset.Ioc (r i) (t i)) (Finset.Ioc (r j) (t j))) :
    (∀ x, ∑ i, ‖(Ψ.proj (Ψ.D.root.1 + t i) - Ψ.proj (Ψ.D.root.1 + r i)) x‖ ^ 2 ≤
      1 * ‖x‖ ^ 2) ∧
    ∀ i x, ‖(Ψ.proj (Ψ.D.root.1 + t i) - Ψ.proj (Ψ.D.root.1 + r i)) x‖ ^ 2 =
      ∑ Q : {Q // Q ∈ (Ψ.partition (Ψ.D.root.1 + r i)).cells},
        ‖(Ψ.proj (Ψ.D.root.1 + t i) - Ψ.proj (Ψ.D.root.1 + r i))
          (columnL2Restriction (dyadicGridCell Ψ.D.grid Q.1.1 Q.1.2)
            (dyadicGridCell_measurable Ψ.D.grid Q.1.1 Q.1.2) x)‖ ^ 2 := by
  refine ⟨fun x => ?_, fun i x => ?_⟩
  · rw [one_mul]
    exact projection_interval_differences_bessel (fun n => Ψ.proj (Ψ.D.root.1 + n))
      (Finset.univ.sup t) (fun n _ => Ψ.isStarProjection_proj _)
      (fun a _ b _ hab => Ψ.proj_nested (by omega)) r t hrt
      (fun i => Finset.le_sup (f := t) (Finset.mem_univ i)) hdis x
  · set ρ := Ψ.D.root.1
    have hv : ∀ᵐ y ∂volume, y ∉ dyadicGridCell Ψ.D.grid Ψ.D.root.1 Ψ.D.root.2 →
        (((Ψ.proj (ρ + t i) - Ψ.proj (ρ + r i)) x : ColumnL2 V) : ℝ → ColumnHilbert V) y = 0 := by
      filter_upwards [Ψ.proj_vanish (ρ + t i) x, Ψ.proj_vanish (ρ + r i) x,
        Lp.coeFn_sub (Ψ.proj (ρ + t i) x) (Ψ.proj (ρ + r i) x)] with y h1 h2 h3 hy
      rw [sub_apply, h3, Pi.sub_apply, h1 hy, h2 hy, sub_zero]
    rw [Ψ.norm_sq_partition (ρ + r i) _ hv]
    refine Finset.sum_congr rfl fun Q _ => ?_
    have hri := hrt i
    have h1 := Ψ.proj_comm_restrict (h' := ρ + r i) (h := ρ + t i) (by omega) Q.2
    have h2 := Ψ.proj_comm_restrict (h' := ρ + r i) (h := ρ + r i) le_rfl Q.2
    rw [sub_apply, sub_apply, map_sub,
      ← ContinuousLinearMap.comp_apply _ (Ψ.proj (ρ + t i)), ← h1,
      ← ContinuousLinearMap.comp_apply _ (Ψ.proj (ρ + r i)), ← h2]
    rfl

/-- One layer of the jump: the change of a single averaged layer between the endpoints, applied
to the left history of the preceding layers, is compressed. -/
theorem globHist_layer_jump {ι : Type*} [Fintype ι] (Ψ : ColumnDepthFamily V) {P : ℕ}
    (hP : 0 < P) (Am : ℕ → Fin P → InheritedColumnMask Ψ.D) (l : List (ℕ × Bool))
    (a : ℕ × Bool) (r t : ι → ℕ) (hrt : ∀ i, r i ≤ t i)
    (hdis : ∀ i j, i ≠ j → Disjoint (Finset.Ioc (r i) (t i)) (Finset.Ioc (r j) (t j)))
    (z : ColumnL2 V) :
    ∑ i, ‖(opAvg (fun p => (Ψ.withMask (Am a.1 p)).proj (Ψ.D.root.1 + t i)) -
        opAvg (fun p => (Ψ.withMask (Am a.1 p)).proj (Ψ.D.root.1 + r i)))
        (globHist Ψ Am l (Ψ.D.root.1 + r i) z)‖ ^ 2 ≤
      compressionC Ψ.D l.length ^ 2 * ‖z‖ ^ 2 := by
  set ρ := Ψ.D.root.1
  have : Nonempty (Fin P) := ⟨⟨0, hP⟩⟩
  have hrows : ∀ p : Fin P, ∑ i, ‖((Ψ.withMask (Am a.1 p)).proj (ρ + t i) -
      (Ψ.withMask (Am a.1 p)).proj (ρ + r i)) (globHist Ψ Am l (ρ + r i) z)‖ ^ 2 ≤
        compressionC Ψ.D l.length ^ 2 * ‖z‖ ^ 2 := by
    intro p
    obtain ⟨hB, hblk⟩ := (Ψ.withMask (Am a.1 p)).interval_rows r t hrt hdis
    have h := globHist_compression Ψ hP Am l (fun i => ρ + r i)
      (fun i => (Ψ.withMask (Am a.1 p)).proj (ρ + t i) - (Ψ.withMask (Am a.1 p)).proj (ρ + r i))
      zero_le_one hB hblk z
    rwa [one_mul] at h
  have hexp : ∀ i, (opAvg (fun p => (Ψ.withMask (Am a.1 p)).proj (ρ + t i)) -
      opAvg (fun p => (Ψ.withMask (Am a.1 p)).proj (ρ + r i)))
        (globHist Ψ Am l (ρ + r i) z) =
      ((Fintype.card (Fin P) : ℂ))⁻¹ • ∑ p, ((Ψ.withMask (Am a.1 p)).proj (ρ + t i) -
        (Ψ.withMask (Am a.1 p)).proj (ρ + r i)) (globHist Ψ Am l (ρ + r i) z) := by
    intro i
    simp only [opAvg, Fintype.card_fin, sub_apply, smul_apply,
      FunLike.coe_sum, Finset.sum_apply, Finset.sum_sub_distrib, smul_sub]
  simp_rw [hexp]
  have := rows_uniformAvg_le (fun _ : ι => ContinuousLinearMap.id ℂ (ColumnL2 V))
    (fun i p => ((Ψ.withMask (Am a.1 p)).proj (ρ + t i) -
      (Ψ.withMask (Am a.1 p)).proj (ρ + r i)) (globHist Ψ Am l (ρ + r i) z)) hrows
  simpa using this

/-- Blueprint lines 1886-1888 ("telescope `B_t' - B_r'`, discard left contractions, and use the
changed middle factors as orthogonal rows on `[r,t]`; compression inserts their right factors"):
the jumps of the global averaged histories over disjoint depth intervals. -/
theorem globHist_jump {ι : Type*} [Fintype ι] (Ψ : ColumnDepthFamily V) {P : ℕ} (hP : 0 < P)
    (Am : ℕ → Fin P → InheritedColumnMask Ψ.D) (ls : List (ℕ × Bool)) (r t : ι → ℕ)
    (hrt : ∀ i, r i ≤ t i)
    (hdis : ∀ i j, i ≠ j → Disjoint (Finset.Ioc (r i) (t i)) (Finset.Ioc (r j) (t j)))
    (z : ColumnL2 V) :
    ∑ i, ‖globHist Ψ Am ls (Ψ.D.root.1 + t i) z - globHist Ψ Am ls (Ψ.D.root.1 + r i) z‖ ^ 2 ≤
      ls.length * (∑ m ∈ Finset.range ls.length, compressionC Ψ.D m ^ 2) * ‖z‖ ^ 2 := by
  set ρ := Ψ.D.root.1
  induction ls using List.reverseRecOn with
  | nil => simp [globHist, layerOp_nil]
  | append_singleton l a ih =>
    set n := l.length
    have hlen : (l ++ [a]).length = n + 1 := by simp [n]
    rw [hlen, Finset.sum_range_succ]
    set! F : ℤ → ColumnL2 V →L[ℂ] ColumnL2 V := fun h =>
      if a.2 then ContinuousLinearMap.id ℂ (ColumnL2 V) -
        opAvg (fun p => (Ψ.withMask (Am a.1 p)).proj h)
      else opAvg (fun p => (Ψ.withMask (Am a.1 p)).proj h)
    have happ : ∀ h, globHist Ψ Am (l ++ [a]) h = (F h).comp (globHist Ψ Am l h) := by
      intro h; unfold globHist; rw [layerOp_append]
    have hcon : ∀ h w, ‖F h w‖ ≤ ‖w‖ := by
      intro h w
      simp only [F]
      split_ifs
      · exact norm_id_sub_opAvg_apply_le hP _ (fun p x => norm_sub_starProjection_le _
          ((Ψ.withMask (Am a.1 p)).isStarProjection_proj h) x) w
      · exact norm_opAvg_apply_le _ (fun p x => starProjection_norm_apply_le _
          ((Ψ.withMask (Am a.1 p)).isStarProjection_proj h) x) w
    have hdiff : ∀ i w, ‖(F (ρ + t i) - F (ρ + r i)) w‖ = ‖(opAvg (fun p =>
        (Ψ.withMask (Am a.1 p)).proj (ρ + t i)) - opAvg (fun p =>
          (Ψ.withMask (Am a.1 p)).proj (ρ + r i))) w‖ := by
      intro i w
      simp only [F]
      split_ifs
      · rw [show (ContinuousLinearMap.id ℂ (ColumnL2 V) - opAvg (fun p =>
            (Ψ.withMask (Am a.1 p)).proj (ρ + t i))) - (ContinuousLinearMap.id ℂ (ColumnL2 V) -
            opAvg (fun p => (Ψ.withMask (Am a.1 p)).proj (ρ + r i))) = -(opAvg (fun p =>
            (Ψ.withMask (Am a.1 p)).proj (ρ + t i)) - opAvg (fun p =>
            (Ψ.withMask (Am a.1 p)).proj (ρ + r i))) by abel, neg_apply,
          norm_neg]
      · rfl
    set! x : ι → ℝ := fun i => ‖globHist Ψ Am l (ρ + t i) z - globHist Ψ Am l (ρ + r i) z‖
    set! y : ι → ℝ := fun i => ‖(opAvg (fun p => (Ψ.withMask (Am a.1 p)).proj (ρ + t i)) -
      opAvg (fun p => (Ψ.withMask (Am a.1 p)).proj (ρ + r i)))
        (globHist Ψ Am l (ρ + r i) z)‖
    have hD : ∀ i, ‖globHist Ψ Am (l ++ [a]) (ρ + t i) z -
        globHist Ψ Am (l ++ [a]) (ρ + r i) z‖ ≤ x i + y i := by
      intro i
      rw [happ, happ, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply]
      have e : F (ρ + t i) (globHist Ψ Am l (ρ + t i) z) - F (ρ + r i)
          (globHist Ψ Am l (ρ + r i) z) = F (ρ + t i) (globHist Ψ Am l (ρ + t i) z -
            globHist Ψ Am l (ρ + r i) z) + (F (ρ + t i) - F (ρ + r i))
              (globHist Ψ Am l (ρ + r i) z) := by
        rw [map_sub, sub_apply]; abel
      rw [e]
      exact (norm_add_le _ _).trans (add_le_add (hcon _ _) (le_of_eq (hdiff i _)))
    have hx := ih
    have hy := globHist_layer_jump Ψ hP Am l a r t hrt hdis z
    change ∑ i, x i ^ 2 ≤ _ at hx
    change ∑ i, y i ^ 2 ≤ _ at hy
    have hx0 : ∀ i, 0 ≤ x i := fun i => norm_nonneg _
    have hy0 : ∀ i, 0 ≤ y i := fun i => norm_nonneg _
    have hsq : ∑ i, ‖globHist Ψ Am (l ++ [a]) (ρ + t i) z -
        globHist Ψ Am (l ++ [a]) (ρ + r i) z‖ ^ 2 ≤ ∑ i, (x i + y i) ^ 2 :=
      Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hD i) 2
    refine hsq.trans ?_
    set S := ∑ m ∈ Finset.range n, compressionC Ψ.D m ^ 2
    have hz := sq_nonneg ‖z‖
    rcases Nat.eq_zero_or_pos n with hn | hn
    · have hxs : ∑ i, x i ^ 2 ≤ 0 := by rw [hn] at hx; simpa using hx
      have hxz : ∀ i, x i = 0 := by
        intro i
        have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => sq_nonneg (x i))).mp
          (le_antisymm hxs (Finset.sum_nonneg fun i _ => sq_nonneg _)) i (Finset.mem_univ i)
        exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
      have hy' : ∑ i, y i ^ 2 ≤ compressionC Ψ.D n ^ 2 * ‖z‖ ^ 2 := hy
      rw [hn] at hy'
      simp only [hxz, zero_add]
      have hS : S = 0 := by simp [S, hn]
      rw [hS, hn]
      push_cast
      linarith
    · have hnr : (0 : ℝ) < n := by exact_mod_cast hn
      have hpt : ∀ i, (n : ℝ) * (x i + y i) ^ 2 ≤ (n + 1) * x i ^ 2 + n * (n + 1) * y i ^ 2 :=
        fun i => by nlinarith only [sq_nonneg (x i - n * y i)]
      have hsum : (n : ℝ) * ∑ i, (x i + y i) ^ 2 ≤
          (n + 1) * ∑ i, x i ^ 2 + n * (n + 1) * ∑ i, y i ^ 2 := by
        rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_le_sum fun i _ => hpt i
      have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => sq_nonneg _
      refine le_of_mul_le_mul_left ?_ hnr
      push_cast
      calc (n : ℝ) * ∑ i, (x i + y i) ^ 2 ≤
          (n + 1) * ∑ i, x i ^ 2 + n * (n + 1) * ∑ i, y i ^ 2 := hsum
        _ ≤ (n + 1) * (n * S * ‖z‖ ^ 2) + n * (n + 1) *
            (compressionC Ψ.D n ^ 2 * ‖z‖ ^ 2) := by gcongr
        _ = n * ((n + 1) * (S + compressionC Ψ.D n ^ 2) * ‖z‖ ^ 2) := by ring

end GlobalJumps

section RestrictionUnions
variable {V : Type*} [Fintype V]

theorem columnL2Restriction_comm {s t : Set ℝ} (hs : MeasurableSet s) (ht : MeasurableSet t) :
    (columnL2Restriction (V := V) s hs).comp (columnL2Restriction t ht) =
      (columnL2Restriction t ht).comp (columnL2Restriction s hs) := by
  refine ContinuousLinearMap.ext fun w => Lp.ext ?_
  simp only [ContinuousLinearMap.comp_apply]
  change (columnL2Indicator s hs (columnL2Indicator t ht w) : ℝ → ColumnHilbert V) =ᵐ[volume]
    (columnL2Indicator t ht (columnL2Indicator s hs w) : ℝ → ColumnHilbert V)
  filter_upwards [columnL2Indicator_coeFn s hs (columnL2Indicator t ht w),
    columnL2Indicator_coeFn t ht w, columnL2Indicator_coeFn t ht (columnL2Indicator s hs w),
    columnL2Indicator_coeFn s hs w] with y h1 h2 h3 h4
  rw [h1, h3]
  by_cases hy : y ∈ s <;> by_cases hy' : y ∈ t <;>
    simp [Set.indicator_of_mem, Set.indicator_of_notMem, hy, hy', h2, h4]

end RestrictionUnions

namespace ActiveSetup
variable {κ' : LocalKernelClass} {c₀ : ℕ} (A : ActiveSetup κ' c₀)

/-- The active cells are closed under ancestors below the root. -/
def AncClosed : Prop :=
  ∀ I ∈ A.cells, ∀ J : ℤ × ℤ, dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G J.1 J.2 →
    dyadicGridCell A.G J.1 J.2 ⊆ dyadicGridCell A.G A.R.1 A.R.2 → J ∈ A.cells

end ActiveSetup

theorem sum_filter_fst_eq {γ ι M : Type*} [Fintype γ] [Fintype ι] [DecidableEq γ]
    [AddCommMonoid M] (f : γ × ι → M) (G : γ) :
    ∑ k ∈ (Finset.univ : Finset (γ × ι)).filter (fun k => k.1 = G), f k = ∑ i, f (G, i) := by
  rw [Finset.sum_filter, Fintype.sum_prod_type, Finset.sum_eq_single G]
  · simp
  · intro b _ hb; simp [hb]
  · intro h; exact absurd (Finset.mem_univ G) h

theorem cells_pairwiseDisjoint_of_depth (Gd : RealDyadicGrid) (S : Finset (ℤ × ℤ)) {h : ℤ}
    (hS : ∀ I ∈ S, I.1 = h) :
    Set.PairwiseDisjoint (S : Set (ℤ × ℤ)) fun I => dyadicGridCell Gd I.1 I.2 := by
  intro I hI J hJ hne
  rw [Function.onFun, Set.disjoint_iff_inter_eq_empty]
  by_contra hov
  exact hne (dyadicGridCell_eq_of_meet Gd ((hS I hI).trans (hS J hJ).symm)
    (Set.nonempty_iff_ne_empty.mpr hov))


section DepthLocality2
variable {V W : Type*} [Fintype V] [Fintype W]

/-- Rows whose outputs vanish off the root of a depth family and which commute with the
restrictions to its depth-`h` cells split orthogonally over that partition (the hypothesis of
`basic_insert`). -/
theorem ColumnDepthFamily.blk_of_commute (Ψ : ColumnDepthFamily V) (h : ℤ)
    (R : ColumnL2 W →L[ℂ] ColumnL2 W)
    (hvan : ∀ x, ∀ᵐ y ∂volume, y ∉ dyadicGridCell Ψ.D.grid Ψ.D.root.1 Ψ.D.root.2 →
      (R x : ℝ → ColumnHilbert W) y = 0)
    (hc : ∀ Q ∈ (Ψ.partition h).cells,
      R.comp (columnL2Restriction (dyadicGridCell Ψ.D.grid Q.1 Q.2)
        (dyadicGridCell_measurable Ψ.D.grid Q.1 Q.2)) =
      (columnL2Restriction (dyadicGridCell Ψ.D.grid Q.1 Q.2)
        (dyadicGridCell_measurable Ψ.D.grid Q.1 Q.2)).comp R) (x : ColumnL2 W) :
    ‖R x‖ ^ 2 = ∑ Q : {Q // Q ∈ (Ψ.partition h).cells},
      ‖R (columnL2Restriction (dyadicGridCell Ψ.D.grid Q.1.1 Q.1.2)
        (dyadicGridCell_measurable Ψ.D.grid Q.1.1 Q.1.2) x)‖ ^ 2 := by
  rw [Ψ.norm_sq_partition' h (R x) (hvan x)]
  refine Finset.sum_congr rfl fun Q _ => ?_
  rw [← ContinuousLinearMap.comp_apply R, hc Q.1 Q.2]
  rfl

end DepthLocality2

/-- Outputs of a restriction vanish off its set. -/
theorem columnL2Restriction_vanish {V : Type*} [Fintype V] (s : Set ℝ) (hs : MeasurableSet s)
    (x : ColumnL2 V) :
    ∀ᵐ y ∂volume, y ∉ s → (columnL2Restriction s hs x : ℝ → ColumnHilbert V) y = 0 := by
  filter_upwards [columnL2Indicator_coeFn s hs x] with y hy hys
  change (columnL2Indicator s hs x : ℝ → ColumnHilbert V) y = 0
  rw [hy, Set.indicator_of_notMem hys]

/-- Depth intervals of naturals shifted by a common offset stay disjoint. -/
theorem Ioc_disjoint_shift {a b c d δ : ℕ}
    (h : Disjoint (Finset.Ioc a b) (Finset.Ioc c d)) :
    Disjoint (Finset.Ioc (a + δ) (b + δ)) (Finset.Ioc (c + δ) (d + δ)) := by
  rw [Finset.disjoint_left] at h ⊢
  intro x hx hx'
  simp only [Finset.mem_Ioc] at hx hx'
  exact h (a := x - δ) (by rw [Finset.mem_Ioc]; omega) (by rw [Finset.mem_Ioc]; omega)

/-- The jumps of a basic depth family over disjoint intervals measured from a deeper root are
Bessel. -/
theorem ColumnDepthFamily.jumps_from_le {V : Type*} [Fintype V] (Ψ : ColumnDepthFamily V)
    {ι : Type*} [Fintype ι] {ρ : ℤ} (hρ : Ψ.D.root.1 ≤ ρ) (r t : ι → ℕ) (hrt : ∀ i, r i ≤ t i)
    (hdis : ∀ i i', i ≠ i' → Disjoint (Finset.Ioc (r i) (t i)) (Finset.Ioc (r i') (t i')))
    (Z : ColumnL2 V) :
    ∑ i, ‖(Ψ.proj (ρ + t i) - Ψ.proj (ρ + r i)) Z‖ ^ 2 ≤ ‖Z‖ ^ 2 := by
  set! δ := (ρ - Ψ.D.root.1).toNat
  have hδ : ∀ n : ℕ, ρ + n = Ψ.D.root.1 + ((n + δ : ℕ) : ℤ) := by
    intro n; push_cast; omega
  have h := (Ψ.interval_rows (fun i => r i + δ) (fun i => t i + δ)
    (fun i => by have := hrt i; omega) (fun i i' hne => Ioc_disjoint_shift (hdis i i' hne))).1 Z
  rw [one_mul] at h
  refine le_trans (le_of_eq ?_) h
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hδ (t i), hδ (r i)]

section CertifiedVariationGen
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Certified variation with general histories (blueprint lines 1879-1905, 2149) -/

/-- `certifiedVariation` with the histories `B'` replaced by arbitrary vectors: the left histories
`Br i` enter only through the compression estimate for the ball rows, and the right histories
`Bt i` only through the jump bound `Σ_i ‖Bt i - Br i‖² ≤ J`. Then
`Σ_{G,i} ‖E (L_{t} Bt - L_{r} Br)‖² ≤ 2 C_w (G₀ ‖F‖² + J)`. This is the form used for the
attempt (blueprint line 2149), whose histories are products of global nested projections. -/
theorem certifiedVariation_gen {γ ι : Type*} [Fintype γ] [DecidableEq γ] [Fintype ι] (T : ℕ)
    (L : γ → ℕ → H →L[ℂ] H) (hL : ∀ G, ∀ n ≤ T, IsStarProjection (L G n))
    (hLnest : ∀ G, ∀ i ≤ T, ∀ j ≤ T, i ≤ j → (L G i).comp (L G j) = L G i)
    (E : γ → ι → H →L[ℂ] H) (hE : ∀ G i y, ‖E G i y‖ ≤ ‖y‖)
    (r t : ι → ℕ) (hrt : ∀ i, r i ≤ t i) (ht : ∀ i, t i ≤ T)
    (hdis : ∀ i j, i ≠ j → Disjoint (Finset.Ioc (r i) (t i)) (Finset.Ioc (r j) (t j)))
    (Bt Br : ι → H) (F : H) {Cw G₀ J : ℝ} (hCw : 0 ≤ Cw)
    (hwr1 : ∀ x : γ × ι → H, ‖∑ k, ContinuousLinearMap.adjoint
        ((E k.1 k.2).comp (L k.1 (t k.2) - L k.1 (r k.2))) (x k)‖ ^ 2 ≤
      Cw * ∑ G, ‖∑ k ∈ (Finset.univ : Finset (γ × ι)).filter (fun k => k.1 = G),
        ContinuousLinearMap.adjoint ((E k.1 k.2).comp (L k.1 (t k.2) - L k.1 (r k.2))) (x k)‖ ^ 2)
    (hcomp1 : ∀ c : ℝ, 0 ≤ c → (∀ h, ∑ k : γ × ι,
        ‖(E k.1 k.2).comp (L k.1 (t k.2) - L k.1 (r k.2)) h‖ ^ 2 ≤ c * ‖h‖ ^ 2) →
      ∑ k : γ × ι, ‖(E k.1 k.2).comp (L k.1 (t k.2) - L k.1 (r k.2)) (Br k.2)‖ ^ 2 ≤
        c * G₀ * ‖F‖ ^ 2)
    (hwr2 : ∀ i, ∀ x : γ → H, ‖∑ G, ContinuousLinearMap.adjoint
        ((E G i).comp (L G (t i))) (x G)‖ ^ 2 ≤
      Cw * ∑ G, ‖∑ G' ∈ (Finset.univ : Finset γ).filter (fun G' => G' = G),
        ContinuousLinearMap.adjoint ((E G' i).comp (L G' (t i))) (x G')‖ ^ 2)
    (hjump : ∑ i, ‖Bt i - Br i‖ ^ 2 ≤ J) :
    ∑ k : γ × ι, ‖E k.1 k.2 (L k.1 (t k.2) (Bt k.2) - L k.1 (r k.2) (Br k.2))‖ ^ 2 ≤
      2 * Cw * (G₀ * ‖F‖ ^ 2 + J) := by
  set! R1 : γ × ι → H →L[ℂ] H := fun k => (E k.1 k.2).comp (L k.1 (t k.2) - L k.1 (r k.2))
  have hgrp1 : ∀ G h, ∑ k ∈ (Finset.univ : Finset (γ × ι)).filter (fun k => k.1 = G),
      ‖R1 k h‖ ^ 2 ≤ ‖h‖ ^ 2 := by
    intro G h
    rw [sum_filter_fst (fun k => ‖R1 k h‖ ^ 2) G]
    calc ∑ i, ‖R1 (G, i) h‖ ^ 2 ≤ ∑ i, ‖(L G (t i) - L G (r i)) h‖ ^ 2 :=
          Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _)
            (by simp only [R1, ContinuousLinearMap.comp_apply]; exact hE G i _) 2
      _ ≤ ‖h‖ ^ 2 := projection_interval_differences_bessel (L G) T (hL G) (hLnest G) r t hrt
          ht hdis h
  have hjoint1 : ∀ h, ∑ k : γ × ι, ‖R1 k h‖ ^ 2 ≤ Cw * ‖h‖ ^ 2 :=
    fun h => joint_bessel_of_wholeRanges Finset.univ Prod.fst R1 hgrp1 hCw hwr1 h
  have hterm1 := hcomp1 Cw hCw hjoint1
  have hjoint2 : ∀ i y, ∑ G, ‖(E G i).comp (L G (t i)) y‖ ^ 2 ≤ Cw * ‖y‖ ^ 2 := by
    intro i y
    apply joint_bessel_of_wholeRanges Finset.univ id (fun G => (E G i).comp (L G (t i))) _ hCw
      (hwr2 i) y
    intro G h
    rw [Finset.sum_filter, Finset.sum_eq_single G (fun b _ hb => by simp [hb])
      (fun h' => absurd (Finset.mem_univ G) h')]
    simp only [id, ite_true, ContinuousLinearMap.comp_apply]
    exact pow_le_pow_left₀ (norm_nonneg _) ((hE G i _).trans
      (starProjection_norm_apply_le _ (hL G (t i) (ht i)) _)) 2
  have hterm2 : ∑ k : γ × ι, ‖E k.1 k.2 (L k.1 (t k.2) (Bt k.2 - Br k.2))‖ ^ 2 ≤ Cw * J := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    calc ∑ i, ∑ G, ‖E G i (L G (t i) (Bt i - Br i))‖ ^ 2 ≤
        ∑ i, Cw * ‖Bt i - Br i‖ ^ 2 := Finset.sum_le_sum fun i _ => hjoint2 i _
      _ = Cw * ∑ i, ‖Bt i - Br i‖ ^ 2 := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left hjump hCw
  have hsplit : ∀ k : γ × ι, E k.1 k.2 (L k.1 (t k.2) (Bt k.2) - L k.1 (r k.2) (Br k.2)) =
      R1 k (Br k.2) + E k.1 k.2 (L k.1 (t k.2) (Bt k.2 - Br k.2)) := by
    intro k
    simp only [R1, ContinuousLinearMap.comp_apply, sub_apply, map_sub]
    abel
  calc ∑ k : γ × ι, ‖E k.1 k.2 (L k.1 (t k.2) (Bt k.2) - L k.1 (r k.2) (Br k.2))‖ ^ 2
      ≤ ∑ k : γ × ι, (2 * ‖R1 k (Br k.2)‖ ^ 2 +
          2 * ‖E k.1 k.2 (L k.1 (t k.2) (Bt k.2 - Br k.2))‖ ^ 2) := by
        apply Finset.sum_le_sum; intro k _
        rw [hsplit]
        have := norm_add_le (R1 k (Br k.2)) (E k.1 k.2 (L k.1 (t k.2) (Bt k.2 - Br k.2)))
        have h0 := norm_nonneg (R1 k (Br k.2) + E k.1 k.2 (L k.1 (t k.2) (Bt k.2 - Br k.2)))
        nlinarith [sq_nonneg (‖R1 k (Br k.2)‖ - ‖E k.1 k.2 (L k.1 (t k.2) (Bt k.2 - Br k.2))‖)]
    _ = 2 * ∑ k : γ × ι, ‖R1 k (Br k.2)‖ ^ 2 +
        2 * ∑ k : γ × ι, ‖E k.1 k.2 (L k.1 (t k.2) (Bt k.2 - Br k.2))‖ ^ 2 := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ 2 * (Cw * G₀ * ‖F‖ ^ 2) + 2 * (Cw * J) :=
        add_le_add (mul_le_mul_of_nonneg_left hterm1 (by norm_num))
          (mul_le_mul_of_nonneg_left hterm2 (by norm_num))
    _ = _ := by ring

end CertifiedVariationGen

section CertifiedVariationAvg
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- `certifiedVariation_gen` for pad averages of ball projections (blueprint line 1883, "couple
individual pad choices across times; Jensen"). -/
theorem certifiedVariation_avg {γ ι : Type*} [Fintype γ] [DecidableEq γ] [Fintype ι] (T : ℕ)
    {P : ℕ} (hP : 0 < P) (L : Fin P → γ → ℕ → H →L[ℂ] H)
    (hL : ∀ p G, ∀ n ≤ T, IsStarProjection (L p G n))
    (hLnest : ∀ p G, ∀ i ≤ T, ∀ j ≤ T, i ≤ j → (L p G i).comp (L p G j) = L p G i)
    (E : γ → ι → H →L[ℂ] H) (hE : ∀ G i y, ‖E G i y‖ ≤ ‖y‖)
    (r t : ι → ℕ) (hrt : ∀ i, r i ≤ t i) (ht : ∀ i, t i ≤ T)
    (hdis : ∀ i j, i ≠ j → Disjoint (Finset.Ioc (r i) (t i)) (Finset.Ioc (r j) (t j)))
    (Bt Br : ι → H) (F : H) {Cw G₀ J : ℝ} (hCw : 0 ≤ Cw)
    (hwr1 : ∀ p, ∀ x : γ × ι → H, ‖∑ k, ContinuousLinearMap.adjoint
        ((E k.1 k.2).comp (L p k.1 (t k.2) - L p k.1 (r k.2))) (x k)‖ ^ 2 ≤
      Cw * ∑ G, ‖∑ k ∈ (Finset.univ : Finset (γ × ι)).filter (fun k => k.1 = G),
        ContinuousLinearMap.adjoint ((E k.1 k.2).comp (L p k.1 (t k.2) - L p k.1 (r k.2)))
          (x k)‖ ^ 2)
    (hcomp1 : ∀ p, ∀ c : ℝ, 0 ≤ c → (∀ h, ∑ k : γ × ι,
        ‖(E k.1 k.2).comp (L p k.1 (t k.2) - L p k.1 (r k.2)) h‖ ^ 2 ≤ c * ‖h‖ ^ 2) →
      ∑ k : γ × ι, ‖(E k.1 k.2).comp (L p k.1 (t k.2) - L p k.1 (r k.2)) (Br k.2)‖ ^ 2 ≤
        c * G₀ * ‖F‖ ^ 2)
    (hwr2 : ∀ p i, ∀ x : γ → H, ‖∑ G, ContinuousLinearMap.adjoint
        ((E G i).comp (L p G (t i))) (x G)‖ ^ 2 ≤
      Cw * ∑ G, ‖∑ G' ∈ (Finset.univ : Finset γ).filter (fun G' => G' = G),
        ContinuousLinearMap.adjoint ((E G' i).comp (L p G' (t i))) (x G')‖ ^ 2)
    (hjump : ∑ i, ‖Bt i - Br i‖ ^ 2 ≤ J) :
    ∑ k : γ × ι, ‖E k.1 k.2 (opAvg (fun p => L p k.1 (t k.2)) (Bt k.2) -
        opAvg (fun p => L p k.1 (r k.2)) (Br k.2))‖ ^ 2 ≤ 2 * Cw * (G₀ * ‖F‖ ^ 2 + J) := by
  have : Nonempty (Fin P) := ⟨⟨0, hP⟩⟩
  have hexp : ∀ k : γ × ι, opAvg (fun p => L p k.1 (t k.2)) (Bt k.2) -
      opAvg (fun p => L p k.1 (r k.2)) (Br k.2) = ((Fintype.card (Fin P) : ℂ))⁻¹ •
        ∑ p, (L p k.1 (t k.2) (Bt k.2) - L p k.1 (r k.2) (Br k.2)) := by
    intro k
    simp only [opAvg, Fintype.card_fin, smul_apply, FunLike.coe_sum, Finset.sum_apply,
      Finset.sum_sub_distrib, smul_sub]
  simp_rw [hexp]
  exact rows_uniformAvg_le (fun k : γ × ι => E k.1 k.2)
    (fun k p => L p k.1 (t k.2) (Bt k.2) - L p k.1 (r k.2) (Br k.2)) fun p =>
      certifiedVariation_gen T (L p) (hL p) (hLnest p) E hE r t hrt ht hdis Bt Br F hCw
        (hwr1 p) (hcomp1 p) (hwr2 p) hjump

end CertifiedVariationAvg

/-! ### Whole endpoint ranges on the main columns (blueprint lines 1777-1789, 1875) -/

section GroupOutputFiber
variable {V W : Type*} [Fintype V] [Fintype W]

open scoped Classical in
/-- Group outputs over finer labels `V` that push forward along `lab : V → W`, with at most one
label of each fiber present at the point, have the norm of the pushed-forward group output when
the scalars agree at the present labels and the weights agree. -/
theorem groupOutput_fiber_norm (lab : V → W) (φ : W → ℝ → ℂ) (ε : W → ℝ) (φ' : V → ℝ → ℂ)
    (ε' : V → ℝ) (hε0 : ∀ w, 0 ≤ ε w) (hε'0 : ∀ v, 0 ≤ ε' v) (a : V → ℝ → ℂ) (y : ℝ)
    (hφ : ∀ v, a v y ≠ 0 → φ (lab v) y = φ' v y) (hε : ∀ v, ε (lab v) = ε' v)
    (hfib : ∀ v₁ v₂, lab v₁ = lab v₂ → a v₁ y ≠ 0 → a v₂ y ≠ 0 → v₁ = v₂) :
    ‖groupOutput φ ε (fun w y => ∑ v ∈ Finset.univ.filter (fun v => lab v = w), a v y) y‖ =
      ‖groupOutput φ' ε' a y‖ := by
  refine (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp ?_
  rw [norm_sq_groupOutput _ _ _ _ hε0, norm_sq_groupOutput _ _ _ _ hε'0]
  have hphys : ∑ w, (∑ v ∈ Finset.univ.filter (fun v => lab v = w), a v y) * φ w y =
      ∑ v, a v y * φ' v y := by
    have e : ∑ w, (∑ v ∈ Finset.univ.filter (fun v => lab v = w), a v y) * φ w y =
        ∑ v, a v y * φ (lab v) y := by
      simp_rw [Finset.sum_mul]
      rw [← Finset.sum_fiberwise (Finset.univ : Finset V) lab (fun v => a v y * φ (lab v) y)]
      refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun v hv => ?_
      rw [(Finset.mem_filter.mp hv).2]
    rw [e]
    refine Finset.sum_congr rfl fun v _ => ?_
    by_cases hv : a v y = 0
    · rw [hv, zero_mul, zero_mul]
    · rw [hφ v hv]
  have hfiber : ∀ w, ‖∑ v ∈ Finset.univ.filter (fun v => lab v = w), a v y‖ ^ 2 =
      ∑ v ∈ Finset.univ.filter (fun v => lab v = w), ‖a v y‖ ^ 2 := by
    intro w
    by_cases h : ∃ v₀ ∈ Finset.univ.filter (fun v => lab v = w), a v₀ y ≠ 0
    · obtain ⟨v₀, hv₀, hne⟩ := h
      have hoth : ∀ v ∈ Finset.univ.filter (fun v => lab v = w), v ≠ v₀ → a v y = 0 := by
        intro v hv hvv
        by_contra hz
        exact hvv (hfib v v₀ ((Finset.mem_filter.mp hv).2.trans (Finset.mem_filter.mp hv₀).2.symm)
          hz hne)
      rw [Finset.sum_eq_single v₀ (fun v hv hvv => hoth v hv hvv) (fun h => absurd hv₀ h),
        Finset.sum_eq_single v₀ (fun v hv hvv => by rw [hoth v hv hvv, norm_zero]; ring)
          (fun h => absurd hv₀ h)]
    · push Not at h
      rw [Finset.sum_eq_zero h, Finset.sum_eq_zero fun v hv => by rw [h v hv, norm_zero]; ring,
        norm_zero]
      ring
  have hpriv : ∑ w, ‖∑ v ∈ Finset.univ.filter (fun v => lab v = w), a v y‖ ^ 2 * ε w =
      ∑ v, ‖a v y‖ ^ 2 * ε' v := by
    simp_rw [hfiber, Finset.sum_mul]
    rw [← Finset.sum_fiberwise (Finset.univ : Finset V) lab (fun v => ‖a v y‖ ^ 2 * ε' v)]
    refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun v hv => ?_
    rw [← hε v, (Finset.mem_filter.mp hv).2]
  rw [hphys, hpriv]

end GroupOutputFiber

namespace ActiveSetup.BasicFamilies
variable {κ : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ c₀} (bf : A.BasicFamilies)

/-- Two occurrences of an original label whose admission cells meet have the same vertex:
admission cells of distinct vertices of one label are disjoint. -/
theorem vtxAt_eq_of_meet {I J : ℤ × ℤ} {x : bf.Lab} (hI : bf.occAvail I x)
    (hJ : bf.occAvail J x)
    (hm : (dyadicGridCell A.G (bf.vtxAt I x).2.1.1 (bf.vtxAt I x).2.1.2 ∩
      dyadicGridCell A.G (bf.vtxAt J x).2.1.1 (bf.vtxAt J x).2.1.2).Nonempty) :
    bf.vtxAt I x = bf.vtxAt J x := by
  classical
  -- the admission cell is the shallowest available ancestor
  have hmin : ∀ {I : ℤ × ℤ}, bf.occAvail I x → ∀ K : ℤ × ℤ, bf.occAvail K x →
      dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G K.1 K.2 → (bf.vtxAt I x).2.1.1 ≤ K.1 := by
    intro I hI K hK hIK
    have hne : (admAnc (G := A.G) (R := A.R) (N := A.treeDepth) bf.occAvail
        ⟨I, A.cells_mem_tree hI.1⟩ x).Nonempty :=
      ⟨⟨I, A.cells_mem_tree hI.1⟩, (mem_admAnc bf.occAvail).mpr ⟨subset_rfl, hI⟩⟩
    have h2 := (admCellOf_spec bf.occAvail hne).2 ⟨K, A.cells_mem_tree hK.1⟩
      ((mem_admAnc bf.occAvail).mpr ⟨hIK, hK⟩)
    simp only [vtxAt, hI.1, ↓reduceDIte]
    exact h2
  obtain ⟨y, hyI, hyJ⟩ := hm
  obtain ⟨hIa, hIs⟩ := bf.vtxAt_spec hI
  obtain ⟨hJa, hJs⟩ := bf.vtxAt_spec hJ
  have hfI := bf.vtxAt_fst I x
  have hfJ := bf.vtxAt_fst J x
  have hcell : (bf.vtxAt I x).2.1 = (bf.vtxAt J x).2.1 := by
    rcases le_total (bf.vtxAt I x).2.1.1 (bf.vtxAt J x).2.1.1 with h | h
    · have hsub := dyadicGridCell_subset_of_common_point A.G hyJ hyI h
      have h' := hmin hJ _ hIa (hJs.trans hsub)
      exact anc_eq_of_depth (hJs.trans hsub) hJs (le_antisymm h h')
    · have hsub := dyadicGridCell_subset_of_common_point A.G hyI hyJ h
      have h' := hmin hI _ hJa (hIs.trans hsub)
      exact anc_eq_of_depth hIs (hIs.trans hsub) (le_antisymm h' h)
  exact Prod.ext (hfI.trans hfJ.symm) (Subtype.ext hcell)

/-- The vertex-labelled main labels: vertices (original column occurrences) and templates. -/
abbrev VLab (Mc : ℕ) : Type := bf.Vtx ⊕ Fin Mc

/-- The main label of a vertex-labelled main label. -/
def vLab (Mc : ℕ) : bf.VLab Mc → bf.Lab ⊕ Fin Mc := Sum.elim (fun b => Sum.inl b.1) Sum.inr

/-- The vertex-labelled main label of a main label at a cell. -/
noncomputable def vKey (Mc : ℕ) (I : ℤ × ℤ) : bf.Lab ⊕ Fin Mc → bf.VLab Mc :=
  Sum.elim (fun x => Sum.inl (bf.vtxAt I x)) Sum.inr

theorem vLab_vKey (Mc : ℕ) (I : ℤ × ℤ) (v : bf.Lab ⊕ Fin Mc) : bf.vLab Mc (bf.vKey Mc I v) = v := by
  rcases v with x | n
  · exact congrArg Sum.inl (bf.vtxAt_fst I x)
  · rfl

open scoped Classical in
/-- The scalars of the vertex-labelled main labels: the chart atom of an available vertex (zero
otherwise) and the template atom. -/
noncomputable def vPhi (Mc : ℕ) (s : List (CatCol bf.Vtx)) : bf.VLab Mc → ℝ → ℂ :=
  Sum.elim (fun b => if bf.occAvail b.2.1 b.1 then quadraticChartAtom (bf.vchart b).2 else 0)
    (fun n => catAtom s n)

/-- The private weights of the vertex-labelled main labels. -/
noncomputable def vEps (Mc : ℕ) : bf.VLab Mc → ℝ :=
  Sum.elim (fun b => (bf.P b.1.1 b.1.2.1).Ψ.D.privateWeight b.1.2.2) (fun _ => 1)

/-- The tag of a vertex-labelled main label (a default beyond the catalog). -/
noncomputable def vTag (Mc : ℕ) (s : List (CatCol bf.Vtx)) (d : bf.Vtx) : bf.VLab Mc → bf.Vtx :=
  Sum.elim id (fun n => if h : (n : ℕ) < s.length then (s[(n : ℕ)]).tag else d)

theorem vEps_pos (Mc : ℕ) (v : bf.VLab Mc) : 0 < bf.vEps Mc v := by
  rcases v with b | n
  · exact (bf.P b.1.1 b.1.2.1).Ψ.D.privateWeight_pos b.1.2.2
  · exact one_pos

theorem vEps_eq (Mc : ℕ) (l : Fin 4) (v : bf.VLab Mc) :
    mainWeight Mc (bf.origCols l) (bf.vLab Mc v) = bf.vEps Mc v := by
  rcases v with b | n <;> rfl

theorem one_le_colBudget_sq_vEps (Mc : ℕ) (v : bf.VLab Mc) :
    1 ≤ A.colBudget ^ 2 * bf.vEps Mc v := by
  rcases v with b | n
  · have h := (bf.P b.1.1 b.1.2.1).inv_privateWeight_le (bf.budget b.1.1 b.1.2.1) b.1.2.2
    have hp := (bf.P b.1.1 b.1.2.1).Ψ.D.privateWeight_pos b.1.2.2
    change 1 ≤ A.colBudget ^ 2 * (bf.P b.1.1 b.1.2.1).Ψ.D.privateWeight b.1.2.2
    rw [inv_le_iff_one_le_mul₀ hp] at h
    linarith
  · change 1 ≤ A.colBudget ^ 2 * 1
    have := A.two_le_colBudget
    nlinarith

theorem vPhi_measurable (Mc : ℕ) (s : List (CatCol bf.Vtx)) (v : bf.VLab Mc) :
    Measurable (bf.vPhi Mc s v) := by
  classical
  rcases v with b | n
  · change Measurable (if bf.occAvail b.2.1 b.1 then quadraticChartAtom (bf.vchart b).2 else 0)
    split_ifs
    · exact quadraticChartAtom_measurable _
    · exact measurable_const
  · exact catAtom_measurable s n

theorem norm_vPhi_le (Mc : ℕ) (s : List (CatCol bf.Vtx)) (v : bf.VLab Mc) (y : ℝ) :
    ‖bf.vPhi Mc s v y‖ ≤ 1 := by
  classical
  rcases v with b | n
  · change ‖(if bf.occAvail b.2.1 b.1 then quadraticChartAtom (bf.vchart b).2 else 0) y‖ ≤ 1
    split_ifs with h
    · exact (bf.vchart_spec b h).2.1 y
    · simp
  · exact catAtom_bound s n y

end ActiveSetup.BasicFamilies

namespace ActiveSetup.BasicFamilies
variable {κ : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ c₀} (bf : A.BasicFamilies)

/-- A vertex-labelled main label occurs at a cell: an available original column of the slot with
that vertex, or a template of the catalog. -/
def VOccurs (l : Fin 4) {Mc : ℕ} (s : List (CatCol bf.Vtx)) (I : ℤ × ℤ) : bf.VLab Mc → Prop :=
  Sum.elim (fun b => ∃ x, (bf.origCols l).avail I x ∧ bf.vtxAt I x = b)
    (fun n => (n : ℕ) < s.length)

/-- The scalar of an occurring vertex-labelled main label is a pure source chart of its tag in
the slot, on the whole line (blueprint line 1798: pure main columns). -/
theorem vPhi_chart (l : Fin 4) {Mc : ℕ} (s : List (CatCol bf.Vtx))
    (hT : ∀ e ∈ s, ∃ R ∈ residueBox (bf.vtag e.tag).dim 9, ∃ γ : ℝ,
      e = templateCol (bf.vtag e.tag) l R γ e.birth e.rank e.tag)
    (htag : ∀ e ∈ s, bf.occAvail e.tag.2.1 e.tag.1) (d : bf.Vtx) {I : ℤ × ℤ}
    {v : bf.VLab Mc} (hv : bf.VOccurs l s I v) :
    ∃ B : QuadraticChartData (bf.vtag (bf.vTag Mc s d v)).dim,
      QuadraticChartComplexity A.csrc A.Hsrc B ∧ IsBoundedQuadraticChart B ∧
      B.horizontal = (bf.vtag (bf.vTag Mc s d v)).θ ∧
      B.matrix = (slotCoeff l : ℚ) • (bf.vtag (bf.vTag Mc s d v)).C ∧
      B.quadratic = slotCoeff l * (bf.vtag (bf.vTag Mc s d v)).lam ∧
      bf.vPhi Mc s v = quadraticChartAtom B := by
  classical
  rcases v with b | n
  · obtain ⟨x, hx, rfl⟩ := hv
    obtain ⟨hc, hb, hθ, hM, hq, -⟩ := bf.origCol_source l hx
    have hav : bf.occAvail (bf.vtxAt I x).2.1 (bf.vtxAt I x).1 := by
      rw [bf.vtxAt_fst]; exact (bf.vtxAt_spec hx.2).1
    refine ⟨(bf.vchart (bf.vtxAt I x)).2, hc, hb, hθ, hM, hq, ?_⟩
    change (if bf.occAvail (bf.vtxAt I x).2.1 (bf.vtxAt I x).1 then
      quadraticChartAtom (bf.vchart (bf.vtxAt I x)).2 else 0) = _
    split_ifs
    rfl
  · have hn : (n : ℕ) < s.length := hv
    set e := s[(n : ℕ)]
    have he : e ∈ s := List.getElem_mem _
    obtain ⟨R, hR, γ, hde⟩ := hT e he
    have htg : bf.vTag Mc s d (Sum.inr n) = e.tag := by
      simp only [vTag, Sum.elim_inr, hn, ↓reduceDIte]; rfl
    rw [htg]
    obtain ⟨A', hA', hθ, hM, hq, hatom⟩ := bf.templateCol_source (htag e he) l hR γ e.birth e.rank
    have hatom' : e.atom = quadraticChartAtom A' := by
      rw [← hatom]; exact congrArg CatCol.atom hde
    refine ⟨A', hA', fun y => by rw [← hatom']; exact e.bound y, hθ, hM, hq, ?_⟩
    funext y
    simp only [vPhi, Sum.elim_inr, catAtom, hn, ↓reduceDIte]
    exact congrFun hatom' y

end ActiveSetup.BasicFamilies

namespace ActiveSetup.BasicFamilies.FamParams
variable {κ : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ c₀} {bf : A.BasicFamilies}
  (fp : bf.FamParams)

open Classical in
/-- A downstream actual-use certificate of the group `G` of color `k` inside the cell `I`: an
active cell `u ⊆ I` with a successful present vertex of color `k` and group `G` (blueprint lines
1863, 1876). -/
def Cert (k : ℕ) (G : bf.Grp) (I : ℤ × ℤ) : Prop :=
  ∃ u ∈ A.cells, dyadicGridCell A.G u.1 u.2 ⊆ dyadicGridCell A.G I.1 I.2 ∧
    ∃ x ∈ bf.admT.X (bf.admAt u), fp.K.Success (fp.K.colorData (bf.admT.st (bf.admAt u)) x) ∧
      fp.K.color bf.admT A.famVtxBound (bf.admAt u) x = k ∧
      fp.K.grp bf.admT A.famVtxBound (bf.admAt u) x = G

open Classical in
theorem Cert.mono {k : ℕ} {G : bf.Grp} {I J : ℤ × ℤ} (h : fp.Cert k G I)
    (hIJ : dyadicGridCell A.G I.1 I.2 ⊆ dyadicGridCell A.G J.1 J.2) : fp.Cert k G J := by
  obtain ⟨u, hu, huI, hx⟩ := h
  exact ⟨u, hu, huI.trans hIJ, hx⟩

open Classical in
/-- Blueprint lem:masks, separation clause, for endpoints: tags in the ball masks of distinct
groups of one color on nested certified endpoint cells `J ⊆ I` are at distance greater than one at
the finer endpoint. -/
theorem endpoint_sep {k : ℕ} {G G' : bf.Grp} (hGG : G ≠ G') {I J : ℤ × ℤ} (hI : I ∈ A.cells)
    (hJ : J ∈ A.cells) (hJI : dyadicGridCell A.G J.1 J.2 ⊆ dyadicGridCell A.G I.1 I.2)
    (hcI : fp.Cert k G I) (hcJ : fp.Cert k G' J) {h h' : ℕ} (hh : h ≤ fp.Hmax)
    (hh' : h' ≤ fp.Hmax) {b b' : bf.Vtx}
    (hb : b ∈ fp.K.mask bf.admT A.famVtxBound G h (bf.admAt I))
    (hb' : b' ∈ fp.K.mask bf.admT A.famVtxBound G' h' (bf.admAt J)) :
    ¬ (bf.tagDist fp.Hed).d J.1 b b' ≤ 1 := by
  obtain ⟨u, hu, huI, w, hw, hs, hc, hg⟩ := hcI
  obtain ⟨u', hu', huJ, w', hw', hs', hc', hg'⟩ := hcJ
  rw [← hg] at hb
  rw [← hg'] at hb'
  have hne : fp.K.grp bf.admT A.famVtxBound (bf.admAt u) w ≠
      fp.K.grp bf.admT A.famVtxBound (bf.admAt u') w' := by rw [hg, hg']; exact hGG
  have h4 := (bf.masks fp.Hed fp.Hmax fp.ωp fp.ωh).2.2.2 (bf.admAt I) (bf.admAt J) (bf.admAt u)
    (bf.admAt u') w w' (bf.admAt_anc hJ hI hJI) (bf.admAt_anc hu hI huI)
    (bf.admAt_anc hu' hJ huJ) hw hw' hs hs' (hc.trans hc'.symm) hne h h' hh hh' b b' hb hb'
  rwa [bf.depth_admAt hJ] at h4

open Classical in
/-- An endpoint occurrence of a vertex-labelled main label for the group `G` of color `k` on the
cell `I`: the cell is active, the label occurs there with its tag in a pad mask of `G` at a pad at
most `H_max`, and `I` carries a downstream use certificate of `G` (blueprint lem:whole-ranges:
"usable endpoint cells whose masks contain their tags"). -/
def VOccOK (l : Fin 4) (s : List (CatCol bf.Vtx)) (d : bf.Vtx) (k : ℕ) (G : bf.Grp)
    (v : bf.VLab fp.Mc) (I : ℤ × ℤ) : Prop :=
  I ∈ A.cells ∧ bf.VOccurs l s I v ∧ (∃ h ≤ fp.Hmax,
    bf.vTag fp.Mc s d v ∈ fp.K.mask bf.admT A.famVtxBound G h (bf.admAt I)) ∧ fp.Cert k G I

open Classical in
/-- Overlapping occurrences of two labels in distinct groups of one color are separated at the
finer of the two depths. -/
theorem vocc_overlap_sep (l : Fin 4) (s : List (CatCol bf.Vtx)) (d : bf.Vtx) {k : ℕ}
    {G G' : bf.Grp} (hGG : G ≠ G') {v w : bf.VLab fp.Mc} {I J : ℤ × ℤ}
    (hI : fp.VOccOK l s d k G v I) (hJ : fp.VOccOK l s d k G' w J)
    (hov : (dyadicGridCell A.G I.1 I.2 ∩ dyadicGridCell A.G J.1 J.2).Nonempty) :
    ∃ t, I.1 ≤ t ∧ J.1 ≤ t ∧ (t = I.1 ∨ t = J.1) ∧
      ¬ (bf.tagDist fp.Hed).d t (bf.vTag fp.Mc s d v) (bf.vTag fp.Mc s d w) ≤ 1 := by
  obtain ⟨hIc, -, ⟨h, hh, hbm⟩, hcI⟩ := hI
  obtain ⟨hJc, -, ⟨h', hh', hbm'⟩, hcJ⟩ := hJ
  rcases le_total I.1 J.1 with hle | hle
  · rcases dyadicGridCell_nested_or_disjoint_of_le A.G hle I.2 J.2 with hd | hsub
    · exact absurd (Set.disjoint_iff_inter_eq_empty.mp hd) hov.ne_empty
    exact ⟨J.1, hle, le_rfl, Or.inr rfl, fp.endpoint_sep hGG hIc hJc hsub hcI hcJ hh hh' hbm hbm'⟩
  · rcases dyadicGridCell_nested_or_disjoint_of_le A.G hle J.2 I.2 with hd | hsub
    · rw [Set.inter_comm] at hov
      exact absurd (Set.disjoint_iff_inter_eq_empty.mp hd) hov.ne_empty
    refine ⟨I.1, le_rfl, hle, Or.inl rfl, ?_⟩
    have := fp.endpoint_sep (Ne.symm hGG) hJc hIc hsub hcJ hcI hh' hh hbm' hbm
    rwa [(bf.tagDist fp.Hed).symm] at this

open Classical in
/-- The last separating depth of two vertex-labelled main labels among the occurrence depths. -/
noncomputable def vLastSep (s : List (CatCol bf.Vtx)) (d : bf.Vtx) {ι : Type*} [Fintype ι]
    (occ : ι → bf.VLab fp.Mc → Finset (ℤ × ℤ)) (v w : bf.VLab fp.Mc) : ℤ :=
  if h : ((AttemptParams.occDepths occ).filter fun t =>
      ¬ (bf.tagDist fp.Hed).d t (bf.vTag fp.Mc s d v) (bf.vTag fp.Mc s d w) ≤ 1).Nonempty
  then ((AttemptParams.occDepths occ).filter fun t =>
      ¬ (bf.tagDist fp.Hed).d t (bf.vTag fp.Mc s d v) (bf.vTag fp.Mc s d w) ≤ 1).max' h
  else 0

end ActiveSetup.BasicFamilies.FamParams

namespace ActiveSetup.BasicFamilies.FamParams
variable {κ : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ c₀} {bf : A.BasicFamilies}
  (fp : bf.FamParams)

open Classical in
/-- Blueprint lem:whole-ranges (lines 1777-1789) for one slot `l` and color `k` of the attempt on
the main columns: group outputs built from occurring vertex-labelled main columns (original column
occurrences and templates) with coefficients constant on whole certified endpoint cells, whose
masks contain the tags, are almost orthogonal, `‖Σ_G Z_G‖² ≤ (1 + τ N W₀²) Σ_G ‖Z_G‖²` with the
inverse private weights at most `W₀² = colBudget²`, when the edge height dominates the graph
threshold at `τ` and at most `N` group-label pairs are present at each point. -/
theorem vWholeRanges (l : Fin 4) (s : List (CatCol bf.Vtx))
    (hT : ∀ e ∈ s, ∃ R ∈ residueBox (bf.vtag e.tag).dim 9, ∃ γ : ℝ,
      e = templateCol (bf.vtag e.tag) l R γ e.birth e.rank e.tag)
    (htag : ∀ e ∈ s, bf.occAvail e.tag.2.1 e.tag.1) (d : bf.Vtx)
    {ι : Type*} [Fintype ι] (grp : ι → bf.Grp) (hgrp : Function.Injective grp) (k : ℕ)
    (occ : ι → bf.VLab fp.Mc → Finset (ℤ × ℤ))
    (hocc : ∀ G v, ∀ I ∈ occ G v, fp.VOccOK l s d k (grp G) v I)
    (c : ι → bf.VLab fp.Mc → ℤ × ℤ → ℂ) {Mc' : ℝ} (hMc : 0 ≤ Mc') (hc : ∀ G v I, ‖c G v I‖ ≤ Mc')
    {K₀ : ℕ} (hK : ∀ G v, (occ G v).card ≤ K₀) {ra rb : ℝ}
    (hroot : ∀ G v, ∀ I ∈ occ G v, dyadicGridCell A.G I.1 I.2 ⊆ Set.Icc ra rb)
    {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hHed : Real.exp (A.Dg * (1 + Real.log A.Hsrc + Real.log τ⁻¹) ^ A.Dg) ≤ fp.Hed)
    {N : ℕ} (hN : ∀ y, ((Finset.univ : Finset (ι × bf.VLab fp.Mc)).filter
      (fun p => occCoef A.G occ c p.1 p.2 y ≠ 0)).card ≤ N) :
    ∫ y, ‖∑ G, groupOutput (bf.vPhi fp.Mc s) (bf.vEps fp.Mc) (occCoef A.G occ c G) y‖ ^ 2 ≤
      (1 + τ * N * A.colBudget ^ 2) *
        ∑ G, ∫ y, ‖groupOutput (bf.vPhi fp.Mc s) (bf.vEps fp.Mc) (occCoef A.G occ c G) y‖ ^ 2 := by
  set! S : bf.VLab fp.Mc → bf.VLab fp.Mc → Finset ℤ := fun v w =>
    (AttemptParams.occDepths occ).filter fun t =>
      ¬ (bf.tagDist fp.Hed).d t (bf.vTag fp.Mc s d v) (bf.vTag fp.Mc s d w) ≤ 1
  -- overlapping cross occurrences give a separating depth in `S`
  have hS : ∀ G G', G ≠ G' → ∀ v w, ∀ I ∈ occ G v, ∀ J ∈ occ G' w,
      (dyadicGridCell A.G I.1 I.2 ∩ dyadicGridCell A.G J.1 J.2).Nonempty →
      ∃ t ∈ S v w, I.1 ≤ t ∧ J.1 ≤ t := by
    intro G G' hne v w I hI J hJ hov
    obtain ⟨t, hIt, hJt, ht, hsep⟩ := fp.vocc_overlap_sep l s d (hgrp.ne hne) (hocc G v I hI)
      (hocc G' w J hJ) hov
    refine ⟨t, Finset.mem_filter.mpr ⟨?_, hsep⟩, hIt, hJt⟩
    simp only [AttemptParams.occDepths, Finset.mem_biUnion, Finset.mem_univ, true_and,
      Finset.mem_image]
    rcases ht with rfl | rfl
    · exact ⟨G, v, I, hI, rfl⟩
    · exact ⟨G', w, J, hJ, rfl⟩
  have hsepE : ∀ v w (h : (S v w).Nonempty), fp.vLastSep s d occ v w = (S v w).max' h :=
    fun v w h => dite_eq_left_of_eq_true (eq_true h)
  refine usableRangeBessel A.G (bf.vPhi fp.Mc s) (bf.vEps fp.Mc) (bf.vEps_pos fp.Mc)
    (W₀ := A.colBudget) (bf.one_le_colBudget_sq_vEps fp.Mc) (bf.vPhi_measurable fp.Mc s)
    (Mφ := 1) (bf.norm_vPhi_le fp.Mc s) occ c hMc hc hK hroot (fp.vLastSep s d occ)
    (fun G G' hne v w I hI J hJ hov => ?_) hτ.le (fun G G' hne v w hov n => ?_)
    (fun G G' hne v I hI J hJ => ?_) hN
  · -- the separating depths
    obtain ⟨t, ht, hIt, hJt⟩ := hS G G' hne v w I hI J hJ hov
    rw [hsepE v w ⟨t, ht⟩]
    exact ⟨hIt.trans ((S v w).le_max' t ht), hJt.trans ((S v w).le_max' t ht)⟩
  · -- the cell pairings at the separating depth
    obtain ⟨I, hI, J, hJ, hIJ⟩ := hov
    obtain ⟨t, ht, -, -⟩ := hS G G' hne v w I hI J hJ hIJ
    have hne' : (S v w).Nonempty := ⟨t, ht⟩
    rw [hsepE v w hne']
    set s₀ := (S v w).max' hne'
    have hs₀ := (Finset.mem_filter.mp ((S v w).max'_mem hne')).2
    have hnE := bf.not_tagEdge_of_dist fp.Hed hs₀
    obtain ⟨Bv, hBv, hBvb, hθv, hMv, hqv, hev⟩ := bf.vPhi_chart l s hT htag d
      (hocc G v I hI).2.1
    obtain ⟨Bw, hBw, hBwb, hθw, hMw, hqw, hew⟩ := bf.vPhi_chart l s hT htag d
      (hocc G' w J hJ).2.1
    have h := A.Dg_same A.Hsrc τ A.exp_two_le_Hsrc hτ hτ1 _ _ (slotCoeff l) (slotCoeff_ne_zero l)
      Bv Bw (quadraticChartComplexity_mono_order hBv (by omega))
      (quadraticChartComplexity_mono_order hBw (by omega)) hBvb hBwb hθv hMv hqv hθw hMw hqw
      (dyadicGridLeft A.G s₀ n) (dyadicGridLength A.G s₀) (dyadicGridLength_pos A.G s₀)
      (fun hE => hnE (tagEdge_mono hE hHed))
    rw [← hev, ← hew] at h
    exact norm_setIntegral_Ico_conj_le (dyadicGridLength_pos A.G s₀) h
  · -- the same label never occurs on overlapping cells of distinct groups
    rw [Set.disjoint_iff_inter_eq_empty]
    by_contra hne'
    obtain ⟨t, ht, -, -⟩ := hS G G' hne v v I hI J hJ (Set.nonempty_iff_ne_empty.mpr hne')
    have := (Finset.mem_filter.mp ht).2
    rw [(bf.tagDist fp.Hed).self] at this
    exact this (by simp)

end ActiveSetup.BasicFamilies.FamParams

section GroupOutputPush
variable {V W : Type*} [Fintype V] [Fintype W]

open scoped Classical in
/-- A group output with pushed-forward coefficients is the sum of the coefficients times the
columns of the image labels. -/
theorem groupOutput_pushforward (lab : V → W) (φ : W → ℝ → ℂ) (ε : W → ℝ) (a : V → ℝ → ℂ)
    (y : ℝ) :
    groupOutput φ ε (fun w y => ∑ v ∈ Finset.univ.filter (fun v => lab v = w), a v y) y =
      ∑ v, a v y • privateColumnValue φ ε (lab v) y := by
  unfold groupOutput
  simp_rw [Finset.sum_smul]
  rw [← Finset.sum_fiberwise (Finset.univ : Finset V) lab
    (fun v => a v y • privateColumnValue φ ε (lab v) y)]
  refine Finset.sum_congr rfl fun w _ => Finset.sum_congr rfl fun v hv => ?_
  rw [(Finset.mem_filter.mp hv).2]

end GroupOutputPush

namespace ActiveSetup.BasicFamilies
variable {κ : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ c₀} (bf : A.BasicFamilies)

/-- Finite sums of main columns on cells are, as functions, sums of indicator coefficients times
the private column values. -/
theorem sum_mainCols_ae (l : Fin 4) {Mc : ℕ} (s : List (CatCol bf.Vtx)) {κ' : Type*}
    (T : Finset κ') (u : κ' → ℤ × ℤ) (r : κ' → ℕ) (L : κ' → Finset (bf.Lab ⊕ Fin Mc))
    (hL : ∀ q ∈ T, L q ⊆ mainLabels A.G Mc (bf.origCols l) s (u q) (r q))
    (β : κ' → bf.Lab ⊕ Fin Mc → ℂ) :
    ((∑ q ∈ T, ∑ v ∈ L q, β q v • mainCol A.G Mc (bf.origCols l) s (u q) v :
      ColumnL2 (bf.Lab ⊕ Fin Mc)) : ℝ → ColumnHilbert (bf.Lab ⊕ Fin Mc)) =ᵐ[volume]
      fun y => ∑ q ∈ T, ∑ v ∈ L q, (dyadicGridCell A.G (u q).1 (u q).2).indicator
        (fun _ => β q v) y • privateColumnValue (mainScalar Mc (bf.origCols l) s)
          (mainWeight Mc (bf.origCols l)) v y := by
  have hall : ∀ᵐ y ∂volume, ∀ q ∈ T, ∀ v ∈ L q,
      ((β q v • mainCol A.G Mc (bf.origCols l) s (u q) v : ColumnL2 (bf.Lab ⊕ Fin Mc)) :
        ℝ → ColumnHilbert (bf.Lab ⊕ Fin Mc)) y =
        (dyadicGridCell A.G (u q).1 (u q).2).indicator (fun _ => β q v) y •
          privateColumnValue (mainScalar Mc (bf.origCols l) s) (mainWeight Mc (bf.origCols l))
            v y := by
    rw [Filter.eventually_all_finset]
    intro q hq
    rw [Filter.eventually_all_finset]
    intro v hv
    filter_upwards [Lp.coeFn_smul (β q v) (mainCol A.G Mc (bf.origCols l) s (u q) v),
      wColumn_coeFn (bf.mainLabel_memLp l s (u q) (r q) (hL q hq hv))] with y h1 h2
    rw [h1, Pi.smul_apply]
    change β q v • (wColumn _ _ _ v : ℝ → ColumnHilbert (bf.Lab ⊕ Fin Mc)) y = _
    rw [h2]
    by_cases hy : y ∈ dyadicGridCell A.G (u q).1 (u q).2
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy]
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, smul_zero, zero_smul]
  have hin : ∀ᵐ y ∂volume, ∀ q ∈ T, ((∑ v ∈ L q, β q v • mainCol A.G Mc (bf.origCols l) s
      (u q) v : ColumnL2 (bf.Lab ⊕ Fin Mc)) : ℝ → ColumnHilbert (bf.Lab ⊕ Fin Mc)) y =
        ∑ v ∈ L q, ((β q v • mainCol A.G Mc (bf.origCols l) s (u q) v :
          ColumnL2 (bf.Lab ⊕ Fin Mc)) : ℝ → ColumnHilbert (bf.Lab ⊕ Fin Mc)) y := by
    rw [Filter.eventually_all_finset]
    intro q _
    exact Lp.coeFn_fun_finsetSum _ _
  filter_upwards [Lp.coeFn_fun_finsetSum T (fun q => (∑ v ∈ L q, β q v •
    mainCol A.G Mc (bf.origCols l) s (u q) v : ColumnL2 (bf.Lab ⊕ Fin Mc))), hin, hall]
    with y h1 h2 h3
  rw [h1]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [h2 q hq]
  exact Finset.sum_congr rfl fun v hv => h3 q hq v hv

end ActiveSetup.BasicFamilies

namespace ActiveSetup.BasicFamilies.FamParams
variable {κ : LocalKernelClass} {c₀ : ℕ} {A : ActiveSetup κ c₀} {bf : A.BasicFamilies}
  (fp : bf.FamParams)



end ActiveSetup.BasicFamilies.FamParams
end TrilinearHT.Auto
end
