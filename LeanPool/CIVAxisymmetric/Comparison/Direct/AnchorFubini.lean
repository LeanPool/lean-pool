/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/

module

public import LeanPool.CIVAxisymmetric.Comparison.JointMeasurable

/-!
# Reference times of the mollified equation, in both Fubini orders

For each spatial point `x`, the mollified slice `q_ε(x, ·)` satisfies the primitive identity of
`eq:aniso:comparison:mollified` between almost every pair of times
(`CIV.mollifySlice_ae_ae_sub_eq_intervalIntegral`). The comparison argument anchors the identity
at a reference time `τ₀` and needs it, from that anchor, both for almost every `x` along almost
every later time, and for almost every later time at almost every `x`. This file proves that
almost every `τ₀ ∈ I` is such an anchor, by crossing the per-point statement into a statement on
the triple product `Vec m × I × I` (as `CIV.mollifySlice_ae_prod_sub_eq_intervalIntegral` does)
and reading it off in both orders.

The set of anchors depends on `q` (it is defined through `q`'s own slices), which is the
manuscript's choice of a reference time of `q`: a function obtained from `q` by redefining one
slice has a different set of anchors.
-/

public section

open MeasureTheory Set Filter Topology
open CKN

noncomputable section
namespace CIV

variable {m : ℕ}

/-- The right side of `eq:aniso:comparison:mollified` at the point `(x, s)`. -/
@[expose] def mollifiedRHS (m d : ℕ) (ε : ℝ) (B : Vec m × ℝ → Vec m) (divB q : Vec m × ℝ → ℝ)
    (x : Vec m) (s : ℝ) : ℝ :=
  partialLaplacian m d (mollifySlice m ε q) (x, s)
    - gradPair m (mollifySlice m ε q) (x, s) (B (x, s))
    + diPernaLionsCommutator m ε (fun y => B (y, s)) (fun y => divB (y, s))
        (fun y => q (y, s)) x

theorem setIntegral_restrict_eq_of_subset {g : ℝ → ℝ} {S I : Set ℝ} (hI : MeasurableSet I)
    (hSI : S ⊆ I) : ∫ s in S, g s ∂(volume.restrict I) = ∫ s in S, g s := by
  show ∫ s, g s ∂((volume.restrict I).restrict S) = ∫ s, g s ∂(volume.restrict S)
  rw [Measure.restrict_restrict' hI, Set.inter_eq_left.mpr hSI]

theorem intervalIntegral_restrict_eq_of_mem {g : ℝ → ℝ} {I : Set ℝ} (hI : IsOpen I)
    (hIoc : I.OrdConnected) {τ1 τ2 : ℝ} (hτ1 : τ1 ∈ I) (hτ2 : τ2 ∈ I) :
    (∫ s in τ1..τ2, g s ∂(volume.restrict I)) = ∫ s in τ1..τ2, g s := by
  have hUIcc : Set.uIcc τ1 τ2 ⊆ I := hIoc.uIcc_subset hτ1 hτ2
  have hsub1 : Set.Ioc τ1 τ2 ⊆ I := (Ioc_subset_uIoc.trans uIoc_subset_uIcc).trans hUIcc
  have hsub2 : Set.Ioc τ2 τ1 ⊆ I := (Ioc_subset_uIoc'.trans uIoc_subset_uIcc).trans hUIcc
  have h1 := setIntegral_restrict_eq_of_subset (g := g) hI.measurableSet hsub1
  have h2 := setIntegral_restrict_eq_of_subset (g := g) hI.measurableSet hsub2
  show (∫ s in Set.Ioc τ1 τ2, g s ∂(volume.restrict I))
      - ∫ s in Set.Ioc τ2 τ1, g s ∂(volume.restrict I)
      = (∫ s in Set.Ioc τ1 τ2, g s) - ∫ s in Set.Ioc τ2 τ1, g s
  rw [h1, h2]

/-- The primitive identity of the mollified equation holds almost everywhere on the triple
product `Vec m × I × I`. -/
theorem mollifySlice_sub_eq_intervalIntegral_ae_prod {d : ℕ} {I : Set ℝ} (hI : IsOpen I)
    (hIoc : I.OrdConnected) {B : Vec m × ℝ → Vec m} {divB q : Vec m × ℝ → ℝ}
    (hB : IsAdmissibleDrift m I B divB) (hq : IsLocallyBoundedOn m I q)
    (heq : IsDistributionalDriftDiffusion m d I B divB q) {ε : ℝ} (hε : 0 < ε)
    {τ₀ : ℝ} (hτ₀ : τ₀ ∈ I) :
    ∀ᵐ p ∂((volume : Measure (Vec m)).prod ((volume.restrict I).prod (volume.restrict I))),
      mollifySlice m ε q (p.1, p.2.2) - mollifySlice m ε q (p.1, p.2.1)
        = ∫ s in p.2.1..p.2.2, mollifiedRHS m d ε B divB q p.1 s := by
  set μx : Measure (Vec m) := (volume : Measure (Vec m)) with hμx_def
  set μI : Measure ℝ := volume.restrict I with hμI_def
  set f : Vec m × ℝ × ℝ → ℝ :=
    fun p => mollifySlice m ε q (p.1, p.2.2) - mollifySlice m ε q (p.1, p.2.1) with hfdef
  set g : Vec m × ℝ × ℝ → ℝ :=
    fun p => ∫ s in p.2.1..p.2.2, mollifiedRHS m d ε B divB q p.1 s with hgdef
  have hqmeas : AEStronglyMeasurable q (μx.prod μI) := by
    have heq2 : μx.prod μI = volume.restrict (univ ×ˢ I) := by
      rw [hμx_def, hμI_def, ← Measure.restrict_univ (μ := (volume : Measure (Vec m))),
        Measure.prod_restrict, ← Measure.volume_eq_prod]
    rw [heq2]; exact hq.1
  have hmoll : AEStronglyMeasurable (fun z : Vec m × ℝ => mollifySlice m ε q z) (μx.prod μI) :=
    aestronglyMeasurable_mollifySlice hqmeas
  have hproj2 : Measure.QuasiMeasurePreserving (fun p : Vec m × ℝ × ℝ => (p.1, p.2.2))
      (μx.prod (μI.prod μI)) (μx.prod μI) :=
    QuasiMeasurePreserving.prodMap (Measure.QuasiMeasurePreserving.id μx)
      Measure.quasiMeasurePreserving_snd
  have hproj1 : Measure.QuasiMeasurePreserving (fun p : Vec m × ℝ × ℝ => (p.1, p.2.1))
      (μx.prod (μI.prod μI)) (μx.prod μI) :=
    QuasiMeasurePreserving.prodMap (Measure.QuasiMeasurePreserving.id μx)
      Measure.quasiMeasurePreserving_fst
  have hf : AEStronglyMeasurable f (μx.prod (μI.prod μI)) :=
    (hmoll.comp_quasiMeasurePreserving hproj2).sub (hmoll.comp_quasiMeasurePreserving hproj1)
  have hRHSmeas : AEStronglyMeasurable (fun z : Vec m × ℝ => mollifiedRHS m d ε B divB q z.1 z.2)
      (μx.prod μI) := aestronglyMeasurable_comparisonRHS hε hI hB hq
  have hg0 : AEStronglyMeasurable
      (fun p : Vec m × ℝ × ℝ => ∫ s in p.2.1..p.2.2, mollifiedRHS m d ε B divB q p.1 s ∂μI)
      (μx.prod (μI.prod μI)) := aestronglyMeasurable_intervalIntegral hRHSmeas
  have hsubset : {p : Vec m × ℝ × ℝ |
      (∫ s in p.2.1..p.2.2, mollifiedRHS m d ε B divB q p.1 s ∂μI)
        ≠ ∫ s in p.2.1..p.2.2, mollifiedRHS m d ε B divB q p.1 s}
      ⊆ Set.univ ×ˢ (Iᶜ ×ˢ (univ : Set ℝ) ∪ univ ×ˢ Iᶜ) := by
    rintro ⟨x, τ1, τ2⟩ hp
    simp only [Set.mem_ofPred_eq] at hp
    refine ⟨Set.mem_univ _, ?_⟩
    by_contra hcon
    simp only [Set.mem_union, Set.mem_prod, Set.mem_compl_iff, Set.mem_univ, and_true,
      true_and, not_or] at hcon
    exact hp (intervalIntegral_restrict_eq_of_mem hI hIoc
      (not_not.mp hcon.1) (not_not.mp hcon.2))
  have hnull : μx.prod (μI.prod μI)
      (Set.univ ×ˢ (Iᶜ ×ˢ (univ : Set ℝ) ∪ univ ×ˢ Iᶜ)) = 0 := by
    rw [Measure.prod_prod]
    have hIcI : Iᶜ ∩ I = (∅ : Set ℝ) := by
      ext τ; simp only [Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_empty_iff_false, iff_false]
      tauto
    have hz1 : (μI.prod μI) (Iᶜ ×ˢ (univ : Set ℝ)) = 0 := by
      rw [Measure.prod_prod, hμI_def]
      simp only [Measure.restrict_apply' hI.measurableSet, hIcI, measure_empty, zero_mul]
    have hz2 : (μI.prod μI) ((univ : Set ℝ) ×ˢ Iᶜ) = 0 := by
      rw [Measure.prod_prod, hμI_def]
      simp only [Measure.restrict_apply' hI.measurableSet, hIcI, measure_empty, mul_zero]
    rw [measure_union_null hz1 hz2, mul_zero]
  have hg0eq : (fun p : Vec m × ℝ × ℝ =>
      ∫ s in p.2.1..p.2.2, mollifiedRHS m d ε B divB q p.1 s ∂μI) =ᵐ[μx.prod (μI.prod μI)] g := by
    rw [Filter.EventuallyEq, ae_iff]
    exact measure_mono_null hsubset hnull
  have hg : AEStronglyMeasurable g (μx.prod (μI.prod μI)) := hg0.congr hg0eq
  have hforall : ∀ x : Vec m, ∀ᵐ τ1 ∂μI, ∀ᵐ τ2 ∂μI, f (x, τ1, τ2) = g (x, τ1, τ2) := by
    intro x
    have hx := mollifySlice_ae_ae_sub_eq_intervalIntegral hI hIoc hB hq heq hε x hτ₀
    filter_upwards [hx] with τ1 hτ1
    filter_upwards [hτ1] with τ2 hτ2
    exact hτ2
  exact ae_prod_prod_eq_of_forall_ae_ae hf hg hforall

/-- Almost every `τ₀ ∈ I` is a reference time of the mollified equation in both Fubini orders,
simultaneously for every `ε` of a given sequence of positive mollification radii. -/
theorem ae_isReferenceTime_mollifySlice {d : ℕ} {I : Set ℝ} (hI : IsOpen I)
    (hIoc : I.OrdConnected) {B : Vec m × ℝ → Vec m} {divB q : Vec m × ℝ → ℝ}
    (hB : IsAdmissibleDrift m I B divB) (hq : IsLocallyBoundedOn m I q)
    (heq : IsDistributionalDriftDiffusion m d I B divB q) {εs : ℕ → ℝ} (hεs : ∀ n, 0 < εs n) :
    ∀ᵐ τ₀ ∂(volume.restrict I), ∀ n : ℕ,
      (∀ᵐ x : Vec m, ∀ᵐ τ ∂(volume.restrict I),
        mollifySlice m (εs n) q (x, τ) - mollifySlice m (εs n) q (x, τ₀)
          = ∫ s in τ₀..τ, mollifiedRHS m d (εs n) B divB q x s) ∧
      (∀ᵐ τ ∂(volume.restrict I), ∀ᵐ x : Vec m,
        mollifySlice m (εs n) q (x, τ) - mollifySlice m (εs n) q (x, τ₀)
          = ∫ s in τ₀..τ, mollifiedRHS m d (εs n) B divB q x s) := by
  rcases I.eq_empty_or_nonempty with hIe | ⟨τ₀, hτ₀⟩
  · subst hIe; simp
  rw [ae_all_iff]
  intro n
  set μx : Measure (Vec m) := (volume : Measure (Vec m))
  set μI : Measure ℝ := volume.restrict I
  have hcross := mollifySlice_sub_eq_intervalIntegral_ae_prod (d := d) hI hIoc hB hq heq
    (hεs n) hτ₀
  set P : Vec m × ℝ × ℝ → Prop := fun p =>
    mollifySlice m (εs n) q (p.1, p.2.2) - mollifySlice m (εs n) q (p.1, p.2.1)
      = ∫ s in p.2.1..p.2.2, mollifiedRHS m d (εs n) B divB q p.1 s with hPdef
  -- order `τ₁, x, τ₂`
  have hmp : MeasurePreserving (fun w : ℝ × Vec m × ℝ => (w.2.1, (w.1, w.2.2)))
      (μI.prod (μx.prod μI)) (μx.prod (μI.prod μI)) := by
    have e1 := (measurePreserving_prodAssoc μI μx μI).symm
    have e2 : MeasurePreserving (Prod.map (Prod.swap : ℝ × Vec m → Vec m × ℝ) id)
        ((μI.prod μx).prod μI) ((μx.prod μI).prod μI) :=
      (Measure.measurePreserving_swap (μ := μI) (ν := μx)).prod (MeasurePreserving.id μI)
    have e3 := measurePreserving_prodAssoc μx μI μI
    exact (e3.comp e2).comp e1
  have hA : ∀ᵐ w ∂(μI.prod (μx.prod μI)), P (w.2.1, (w.1, w.2.2)) :=
    hmp.quasiMeasurePreserving.ae hcross
  have hA' := Measure.ae_ae_of_ae_prod hA
  -- order `τ₁, τ₂, x`
  have hswap : ∀ᵐ w ∂((μI.prod μI).prod μx), P w.swap := by
    refine ae_of_ae_map (f := (Prod.swap : (ℝ × ℝ) × Vec m → Vec m × ℝ × ℝ))
      (p := P) (measurable_swap.aemeasurable (μ := (μI.prod μI).prod μx)) ?_
    rw [Measure.prod_swap]
    exact hcross
  have hB' := Measure.ae_ae_of_ae_prod (Measure.ae_ae_of_ae_prod hswap)
  filter_upwards [hA', hB'] with τ1 h1 h2
  refine ⟨?_, ?_⟩
  · filter_upwards [Measure.ae_ae_of_ae_prod h1] with x hx
    filter_upwards [hx] with τ hτ
    exact hτ
  · filter_upwards [h2] with τ hτ
    filter_upwards [hτ] with x hx
    exact hx

end CIV
