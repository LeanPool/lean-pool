/-
Copyright (c) 2026 Alejandro Soto Franco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alejandro Soto Franco
-/
module

public import LeanPool.EllipticPDE.Poincare.OneDim
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.Data.Fin.Tuple.Basic


/-!
# Per-coordinate-direction bound via Fubini (dependency-chain step 2)

Apply the one-dimensional Poincaré inequality (`MeasureTheory.poincare_1d`) on
each coordinate slice of a box and integrate the remaining variables out.

A box `Ω = B ×ˢ (a, b) ⊆ β × ℝ` is integrated over by Fubini as
`∫_Ω f = ∫_{y ∈ B} ∫_{x ∈ (a,b)} f (y, x)`. On each slice `x ↦ f (y, x)` the
one-dimensional Poincaré inequality controls the `L²` norm by the `L²` norm of
the slice derivative `∂_x f`. Integrating that estimate over the remaining
variables `y` gives the per-direction bound on the box.

* `poincare_slice_iterated`: the bound in iterated form, for a general measure
  on the remaining variables. This is the Fubini-decomposed statement.
* `poincare_slice_box`: the same bound written as a single integral over the box
  `B ×ˢ (a, b)`, obtained from the iterated form by Fubini (`setIntegral_prod`).
-/

@[expose] public section

open MeasureTheory Set intervalIntegral

namespace EllipticPdes.Poincare

/-- The per-direction Poincaré bound in iterated form. For a family of
one-dimensional slices `x ↦ Φ y x`, each satisfying the Poincaré hypotheses on
`[a, b]` (a derivative `Φ' y` continuous on `[a, b]`, vanishing at `a`), the
integral over the remaining variables `y` of the slice `L²` norms is bounded by
the same integral of the slice derivative `L²` norms. -/
theorem poincare_slice_iterated
    {β : Type*} [MeasurableSpace β] {ν : Measure β}
    {a b : ℝ} (hab : a ≤ b) {Φ Φ' : β → ℝ → ℝ}
    (hderiv : ∀ y, ∀ x ∈ uIcc a b, HasDerivAt (Φ y) (Φ' y x) x)
    (hcont : ∀ y, ContinuousOn (Φ' y) (uIcc a b))
    (hzero : ∀ y, Φ y a = 0)
    (hg : Integrable (fun y => ∫ x in a..b, (Φ y x) ^ 2) ν)
    (hh : Integrable (fun y => ∫ x in a..b, (Φ' y x) ^ 2) ν) :
    (∫ y, (∫ x in a..b, (Φ y x) ^ 2) ∂ν)
      ≤ (b - a) ^ 2 / 2 * ∫ y, (∫ x in a..b, (Φ' y x) ^ 2) ∂ν := by
  have hslice : (fun y => ∫ x in a..b, (Φ y x) ^ 2)
      ≤ fun y => (b - a) ^ 2 / 2 * ∫ x in a..b, (Φ' y x) ^ 2 :=
    fun y => poincare_1d hab (hderiv y) (hcont y) (hzero y)
  calc (∫ y, (∫ x in a..b, (Φ y x) ^ 2) ∂ν)
      ≤ ∫ y, ((b - a) ^ 2 / 2 * ∫ x in a..b, (Φ' y x) ^ 2) ∂ν :=
        MeasureTheory.integral_mono hg (hh.const_mul _) hslice
    _ = (b - a) ^ 2 / 2 * ∫ y, (∫ x in a..b, (Φ' y x) ^ 2) ∂ν :=
        MeasureTheory.integral_const_mul _ _

/-- The per-direction Poincaré bound on a box `B ×ˢ (a, b) ⊆ β × ℝ`, written as
a single integral over the box. For a function `Φ` whose one-dimensional slices
`x ↦ Φ (y, x)` are `C¹` on `[a, b]` with derivative `∂_x Φ = Φ'` continuous and
`Φ (y, a) = 0`,
`∫_{B ×ˢ (a,b)} Φ² ≤ (b - a)² / 2 * ∫_{B ×ˢ (a,b)} (∂_x Φ)²`.

Fubini (`setIntegral_prod`) reduces both sides to iterated integrals; the
one-dimensional Poincaré inequality bounds each slice; integrating over `B`
gives the result. -/
theorem poincare_slice_box
    {β : Type*} [MeasurableSpace β] {ν : Measure β} [SFinite ν]
    {a b : ℝ} (hab : a ≤ b) {s : Set β} (hs : MeasurableSet s) {Φ Φ' : β × ℝ → ℝ}
    (hderiv : ∀ y, ∀ x ∈ uIcc a b, HasDerivAt (fun t => Φ (y, t)) (Φ' (y, x)) x)
    (hcont : ∀ y, ContinuousOn (fun t => Φ' (y, t)) (uIcc a b))
    (hzero : ∀ y, Φ (y, a) = 0)
    (hΦ2 : IntegrableOn (fun p => (Φ p) ^ 2) (s ×ˢ Ioo a b) (ν.prod volume))
    (hΦ'2 : IntegrableOn (fun p => (Φ' p) ^ 2) (s ×ˢ Ioo a b) (ν.prod volume)) :
    (∫ p in s ×ˢ Ioo a b, (Φ p) ^ 2 ∂(ν.prod volume))
      ≤ (b - a) ^ 2 / 2 * ∫ p in s ×ˢ Ioo a b, (Φ' p) ^ 2 ∂(ν.prod volume) := by
  -- Per-slice Poincaré bound, in `Ioo`-integral form.
  have hslice : ∀ y, (∫ x in Ioo a b, (Φ (y, x)) ^ 2)
      ≤ (b - a) ^ 2 / 2 * ∫ x in Ioo a b, (Φ' (y, x)) ^ 2 := by
    intro y
    have hp := poincare_1d hab (hderiv y) (hcont y) (hzero y)
    rwa [intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo,
      intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo] at hp
  -- Marginal integrability of each slice integral, from product integrability.
  have hΦ2' : Integrable (fun p => (Φ p) ^ 2)
      ((ν.restrict s).prod (volume.restrict (Ioo a b))) := by
    rw [Measure.prod_restrict s (Ioo a b)]; exact hΦ2
  have hΦ'2' : Integrable (fun p => (Φ' p) ^ 2)
      ((ν.restrict s).prod (volume.restrict (Ioo a b))) := by
    rw [Measure.prod_restrict s (Ioo a b)]; exact hΦ'2
  have hgI : IntegrableOn (fun y => ∫ x in Ioo a b, (Φ (y, x)) ^ 2) s ν :=
    hΦ2'.integral_prod_left
  have hhI : IntegrableOn (fun y => ∫ x in Ioo a b, (Φ' (y, x)) ^ 2) s ν :=
    hΦ'2'.integral_prod_left
  -- Fubini both sides, then integrate the slice bound over `B`.
  rw [setIntegral_prod _ hΦ2, setIntegral_prod _ hΦ'2]
  calc (∫ y in s, ∫ x in Ioo a b, (Φ (y, x)) ^ 2 ∂volume ∂ν)
      ≤ ∫ y in s, ((b - a) ^ 2 / 2 * ∫ x in Ioo a b, (Φ' (y, x)) ^ 2) ∂ν :=
        setIntegral_mono_on hgI (hhI.const_mul _) hs (fun y _ => hslice y)
    _ = (b - a) ^ 2 / 2 * ∫ y in s, (∫ x in Ioo a b, (Φ' (y, x)) ^ 2) ∂ν :=
        MeasureTheory.integral_const_mul _ _

/-- The per-direction Poincaré bound on a box `(a, b) ×ˢ B ⊆ ℝ × β`, with the
Poincaré direction the **first** coordinate. This is `poincare_slice_box` with
the two factors swapped; it lets either coordinate of a binary product be the
distinguished Poincaré direction. -/
theorem poincare_slice_box_fst
    {β : Type*} [MeasurableSpace β] {ν : Measure β} [SFinite ν]
    {a b : ℝ} (hab : a ≤ b) {s : Set β} (hs : MeasurableSet s) {Φ Φ' : ℝ × β → ℝ}
    (hderiv : ∀ y, ∀ x ∈ uIcc a b, HasDerivAt (fun t => Φ (t, y)) (Φ' (x, y)) x)
    (hcont : ∀ y, ContinuousOn (fun t => Φ' (t, y)) (uIcc a b))
    (hzero : ∀ y, Φ (a, y) = 0)
    (hΦ2 : IntegrableOn (fun p => (Φ p) ^ 2) (Ioo a b ×ˢ s) (volume.prod ν))
    (hΦ'2 : IntegrableOn (fun p => (Φ' p) ^ 2) (Ioo a b ×ˢ s) (volume.prod ν)) :
    (∫ p in Ioo a b ×ˢ s, (Φ p) ^ 2 ∂(volume.prod ν))
      ≤ (b - a) ^ 2 / 2 * ∫ p in Ioo a b ×ˢ s, (Φ' p) ^ 2 ∂(volume.prod ν) := by
  have hmp : MeasurePreserving (Prod.swap : β × ℝ → ℝ × β) (ν.prod volume) (volume.prod ν) :=
    Measure.measurePreserving_swap
  have hme : MeasurableEmbedding (Prod.swap : β × ℝ → ℝ × β) :=
    MeasurableEquiv.prodComm.measurableEmbedding
  -- Transport an integral over `(a,b) ×ˢ s` to one over `s ×ˢ (a,b)` by swapping.
  have htr : ∀ F : ℝ × β → ℝ,
      (∫ p in Ioo a b ×ˢ s, F p ∂(volume.prod ν))
        = ∫ q in s ×ˢ Ioo a b, F (Prod.swap q) ∂(ν.prod volume) := by
    intro F
    rw [← Set.image_swap_prod s (Ioo a b)]
    exact hmp.setIntegral_image_emb hme F (s ×ˢ Ioo a b)
  rw [htr (fun p => (Φ p) ^ 2), htr (fun p => (Φ' p) ^ 2)]
  -- Integrability of the swapped integrands.
  have hΨ2 : IntegrableOn (fun q => (Φ (Prod.swap q)) ^ 2) (s ×ˢ Ioo a b) (ν.prod volume) := by
    have h := (hmp.integrableOn_image hme (f := fun p => (Φ p) ^ 2) (s := s ×ˢ Ioo a b)).mp
    rw [Set.image_swap_prod] at h
    exact h hΦ2
  have hΨ'2 : IntegrableOn (fun q => (Φ' (Prod.swap q)) ^ 2) (s ×ˢ Ioo a b) (ν.prod volume) := by
    have h := (hmp.integrableOn_image hme (f := fun p => (Φ' p) ^ 2) (s := s ×ˢ Ioo a b)).mp
    rw [Set.image_swap_prod] at h
    exact h hΦ'2
  exact poincare_slice_box (Φ := fun q => Φ (Prod.swap q)) (Φ' := fun q => Φ' (Prod.swap q))
    hab hs (fun y x hx => hderiv y x hx) (fun y => hcont y) (fun y => hzero y) hΨ2 hΨ'2

/-- **Per-direction Poincaré bound on a box in `Fin (n+1) → ℝ`.** Isolating
coordinate `i`, the slice through any point `y` of the remaining coordinates,
varying coordinate `i` over `[a i, b i]`, is `C¹` with derivative `u'` and
vanishes at the left face `i`-th coordinate `= a i`. Then
`∫_Ω u² ≤ (b i - a i)² / 2 * ∫_Ω (u')²` over the box `Ω = ∏ₖ (a k, b k)`.

The box integral is transported through `MeasurableEquiv.piFinSuccAbove`, which
isolates coordinate `i` as the first factor of `ℝ × (Fin n → ℝ)`, and the result
follows from `poincare_slice_box_fst`. -/
theorem poincare_box_dir {n : ℕ} (i : Fin (n + 1)) {a b : Fin (n + 1) → ℝ}
    (hab : a i ≤ b i) {u u' : (Fin (n + 1) → ℝ) → ℝ}
    (hderiv : ∀ y : Fin n → ℝ, ∀ t ∈ uIcc (a i) (b i),
        HasDerivAt (fun s => u (i.insertNth s y)) (u' (i.insertNth t y)) t)
    (hcont : ∀ y : Fin n → ℝ, ContinuousOn (fun s => u' (i.insertNth s y)) (uIcc (a i) (b i)))
    (hzero : ∀ y : Fin n → ℝ, u (i.insertNth (a i) y) = 0)
    (hu2 : IntegrableOn (fun x => (u x) ^ 2) (Set.univ.pi fun k => Ioo (a k) (b k)) volume)
    (hu'2 : IntegrableOn (fun x => (u' x) ^ 2) (Set.univ.pi fun k => Ioo (a k) (b k)) volume) :
    (∫ x in Set.univ.pi fun k => Ioo (a k) (b k), (u x) ^ 2)
      ≤ (b i - a i) ^ 2 / 2 * ∫ x in Set.univ.pi fun k => Ioo (a k) (b k), (u' x) ^ 2 := by
  classical
  set box : Set (Fin (n + 1) → ℝ) := Set.univ.pi fun k => Ioo (a k) (b k) with hbox
  set rest : Set (Fin n → ℝ) := Set.univ.pi fun j => Ioo (a (i.succAbove j)) (b (i.succAbove j))
    with hrest
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i with he
  set ν : Measure (Fin n → ℝ) := Measure.pi fun _ => (volume : Measure ℝ) with hν
  have hmp : MeasurePreserving e (volume : Measure (Fin (n + 1) → ℝ)) (volume.prod ν) :=
    volume_preserving_piFinSuccAbove (fun _ => ℝ) i
  have hme : MeasurableEmbedding e := e.measurableEmbedding
  have hsymm : ∀ (s : ℝ) (y : Fin n → ℝ), e.symm (s, y) = i.insertNth s y := by
    intro s y; rw [he]; rfl
  -- The image of the box under `e` is the slice box `(a i, b i) ×ˢ rest`.
  have himg : e '' box = Ioo (a i) (b i) ×ˢ rest := by
    rw [e.image_eq_preimage_symm]
    ext p
    obtain ⟨s, y⟩ := p
    simp only [Set.mem_preimage, hsymm, hbox, hrest, Set.mem_pi, Set.mem_univ, true_implies,
      Set.mem_prod]
    rw [Fin.forall_iff_succAbove i, Fin.insertNth_apply_same]
    simp only [Fin.insertNth_apply_succAbove]
  -- Transport any integral over the box to the slice box.
  have htr : ∀ F : (Fin (n + 1) → ℝ) → ℝ,
      (∫ x in box, F x) = ∫ p in Ioo (a i) (b i) ×ˢ rest, F (e.symm p) ∂(volume.prod ν) := by
    intro F
    rw [← himg, hmp.setIntegral_image_emb hme (fun p => F (e.symm p)) box]
    simp only [MeasurableEquiv.symm_apply_apply]
  rw [htr (fun x => (u x) ^ 2), htr (fun x => (u' x) ^ 2)]
  -- Integrability transfer through the same equivalence.
  have hI2 : IntegrableOn (fun p => (u (e.symm p)) ^ 2)
      (Ioo (a i) (b i) ×ˢ rest) (volume.prod ν) := by
    rw [← himg, hmp.integrableOn_image hme]
    have hfun : (fun p => (u (e.symm p)) ^ 2) ∘ ⇑e = fun x => (u x) ^ 2 := by
      funext x; simp only [Function.comp_apply, MeasurableEquiv.symm_apply_apply]
    rw [hfun]; exact hu2
  have hI'2 : IntegrableOn (fun p => (u' (e.symm p)) ^ 2)
      (Ioo (a i) (b i) ×ˢ rest) (volume.prod ν) := by
    rw [← himg, hmp.integrableOn_image hme]
    have hfun : (fun p => (u' (e.symm p)) ^ 2) ∘ ⇑e = fun x => (u' x) ^ 2 := by
      funext x; simp only [Function.comp_apply, MeasurableEquiv.symm_apply_apply]
    rw [hfun]; exact hu'2
  -- The remaining-coordinate box is measurable.
  have hrest_meas : MeasurableSet rest :=
    MeasurableSet.univ_pi fun j => measurableSet_Ioo
  exact poincare_slice_box_fst (Φ := fun p => u (e.symm p)) (Φ' := fun p => u' (e.symm p))
    hab hrest_meas
    (fun y t ht => by simp only [hsymm]; exact hderiv y t ht)
    (fun y => by simp only [hsymm]; exact hcont y)
    (fun y => by simp only [hsymm]; exact hzero y)
    hI2 hI'2

end EllipticPdes.Poincare
