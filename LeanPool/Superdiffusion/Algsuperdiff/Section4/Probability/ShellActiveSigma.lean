/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Probability.LayerIndependence
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Cutoff.CutoffSampleRange
public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.BadEvents.LambdaLocal

/-!
# ShellActiveSigma

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Independence of local functionals read at index-dependent truncation levels

## Why a level-uniform producer is not enough

The proved cross-shell and spatial-range results fix **one** truncation index
for the whole family:
`Cutoff.indep_lowerShellLocalCompletion_of_cutoff_separation` compares two
observation regions read by the *same* cutoff `k_m`, and asks for the
separation threshold `sqrt d * 3 ^ m`.  ABK26's Section 4.1 atoms are not of
that shape.  The `G_0` atom

```
Y_n = gamma^{-4} sum_{k <= n} 3^{-gamma(n-k)/4}
        max_{z in 3^{k-2} Z^d cap (Box_n \ Box_{n-1})}
          ( sigmabar_{k-3} * lambda_{gamma,2}^{-1}(z + Box_{k-2}; a_{k-2}) - C )_+
```

reads the field `a_{n-2}` on the annulus `Box_n \ Box_{n-1}`: **both** the read
region and the truncation level move with the index, `Lidx n = n - 2`.  At a
fixed level `L` the separation hypothesis of a level-uniform producer is
*unsatisfiable* -- annuli far below `L` have diameter much smaller than
`sqrt d * 3 ^ L`.

## The true geometry and the mechanism

For `n' < n` the shells `n' - 2 < i <= n - 2` are read by `Y_n` **alone** and
drop out for free by the cross-shell independence of ABK26 -- at *any*
spatial position.  Only the **shared** shells `i <= n' - 2` need decorrelating,
and their range of dependence is `sqrt d * 3 ^ (n' - 2)
= sqrt d * 3 ^ (min (Lidx n) (Lidx n'))`.  Hence the honest separation
threshold is

```
sqrt d * 3 ^ (min (Lidx i) (Lidx j))
```

which the annuli do satisfy.  This module proves the independence statement at
exactly that threshold.

## The carrier translation

On this repository's carriers the bi-infinite truncation floor is `-infinity`
rather than a finite `L_0`: the genuine cutoff `Cutoff.cutoff m` sums *all*
shells at or below `m`.  Consequently the per-index join of the per-shell read
sigma-fields collapses onto a proved object,

```
sup over l of (activeShellSigma Lidx U i l)  >=  lowerShellLocalSigma (Lidx i) (U i),
```

and the varying-level producer is exactly the statement that the family
`(lowerShellLocalSigma (Lidx i) (U i))_i` is mutually independent.  The
row decomposition indexed by the shell `l` is still needed -- it is what feeds
`iIndep_iSup_of_iIndep_rows` -- so `activeShellRegion` / `activeShellSigma` are
kept as the per-`(index, shell)` read region and its sigma-field.

* the local information of a shell is CoarseGraining's integral-generated
  `Homogenization.LocalSigmaR`, pulled back by
  `Frozen.Assumptions.ShellField.lihLocalSigma`, not a point-value restriction
  sigma-field; it takes no measurability argument, so `activeShellSigma` needs
  none either;
* the genuine lower-infinite cutoff is only an almost-everywhere limit of its
  finite truncations, so the statement usable by Section 4 lives on the
  completed sigma-field `Cutoff.lowerShellLocalCompletion` and, after transport
  through the full-measure subtype, on `Cutoff.cutoffSampleLocalSigma`.  The
  completion and subtype steps mirror the proved two-set results
  `Cutoff.indep_lowerShellLocalCompletion_of_indep` and
  `Cutoff.indep_cutoffSampleLocalSigma_of_indep_completion` in the mutual
  (`iIndep`) form.

## Main definitions

* `SeparatedBy`: two regions at Euclidean distance at least `r`, in the exact
  spelling consumed by `Frozen.Assumptions.ShellLawJ1.range_dependence`.
* `activeShellRegion`, `activeShellSigma`: the region index `i` reads of shell
  `l`, and the sigma-field it generates.

## Main results

* `iIndep_shellLocalSigma_of_pairwise_separated`: at one shell, pairwise
  separated regions generate mutually independent local sigma-fields.
* `iIndep_activeShellSigma_row`: the row statement at the honest threshold.
* `iIndep_lowerShellLocalSigma_of_varyingLevel`: the producer, sigma-field form
  on the shell sequence.
* `iIndep_cutoffSampleLocalSigma_of_varyingLevel`: the producer on the genuine
  cutoff carrier.
* `iIndepFun_of_local_cutoffSample`: **the producer**, observable form.
-/

namespace Algsuperdiff.Section4.Probability

open MeasureTheory ProbabilityTheory
open HCPolySupport
open Algsuperdiff.Frozen.Assumptions
open Algsuperdiff.Section3 Algsuperdiff.Section3.Cutoff

noncomputable section

variable {d : ℕ} {iota : Type*}

/-! ## Separation in the manuscript's metric -/

/-- Two observation regions are `r`-separated: every pair of points is at Euclidean
distance at least `r`.  This is the exact predicate carried by
`ShellLawJ1.range_dependence` and by the proved cutoff-range results. -/
def SeparatedBy (r : ℝ) (U V : Set (Vec d)) : Prop :=
  ∀ ⦃x y : Vec d⦄, x ∈ U → y ∈ V → r ≤ HCPolySupport.Book.Ch02.vecNorm (x - y)

/-! ## Auxiliary monotonicity and almost-everywhere bookkeeping -/

/-- The pulled-back integral-local sigma-field of a shell grows with the
observation region.  This is CoarseGraining's `localSigmaR_mono` transported
along `ShellField.forgetShell`. -/
private theorem lihLocalSigma_mono {U V : Set (Vec d)} (hUV : U ⊆ V) :
    ShellField.lihLocalSigma (d := d) U ≤ ShellField.lihLocalSigma V := by
  unfold ShellField.lihLocalSigma
  exact MeasurableSpace.comap_mono (HCPolySupport.localSigmaR_mono hUV)

/-- A finite intersection respects almost-everywhere equality of its members. -/
private theorem aeEq_biInter {alpha : Type*} [MeasurableSpace alpha]
    {mu : Measure alpha} (s : Finset iota) {f g : iota → Set alpha}
    (h : ∀ i ∈ s, f i =ᵐ[mu] g i) :
    (⋂ i ∈ s, f i) =ᵐ[mu] (⋂ i ∈ s, g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.set_biInter_insert, Finset.set_biInter_insert]
      exact (h a (Finset.mem_insert_self a s)).inter
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

private theorem ae_preimage_cutoffSampleLaw (M : ABKModel d) {s t : Set (ShellSeq d)}
    (hst : s =ᵐ[M.P.toMeasure] t) :
    (Subtype.val : CutoffSample d → ShellSeq d) ⁻¹' s
        =ᵐ[(cutoffSampleLaw M).toMeasure]
      (Subtype.val : CutoffSample d → ShellSeq d) ⁻¹' t := by
  rw [← map_cutoffSampleLaw_val M] at hst
  exact (Measure.tendsto_ae_map measurable_subtype_coe.aemeasurable).eventually hst

private theorem measure_preimage_cutoffSampleLaw (M : ABKModel d)
    {s : Set (ShellSeq d)} (hs : MeasurableSet s) :
    (cutoffSampleLaw M).toMeasure ((Subtype.val : CutoffSample d → ShellSeq d) ⁻¹' s)
      = M.P.toMeasure s := by
  rw [← Measure.map_apply_of_aemeasurable measurable_subtype_coe.aemeasurable hs,
    map_cutoffSampleLaw_val]

/-! ## Mutual independence at one shell -/

/-- **Pairwise separation gives mutual independence at one shell.**  This is the
`iIndep` form of the proved two-set result
`Cutoff.indep_shellLocal_of_cutoff_separation`: the two-set statement is
applied to one region against the union of the remaining ones along a `Finset`
induction, which is legitimate because the local sigma-field is monotone in the
region. -/
theorem iIndep_shellLocalSigma_of_pairwise_separated (M : ABKModel d) (l : ℤ)
    {V : iota → Set (Vec d)} (hV : ∀ i, MeasurableSet (V i))
    (hsep : Pairwise fun i j =>
      SeparatedBy (Real.sqrt (d : ℝ) * (3 : ℝ) ^ l) (V i) (V j)) :
    iIndep (fun i => (ShellField.lihLocalSigma (V i)).comap
      (fun omega : ShellSeq d => omega l)) M.P.toMeasure := by
  classical
  rw [iIndep_iff]
  intro s f hf
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      have hUnion : MeasurableSet (⋃ j ∈ s, V j) :=
        Finset.measurableSet_biUnion _ fun j _ => hV j
      have hsepUnion : SeparatedBy (Real.sqrt (d : ℝ) * (3 : ℝ) ^ l)
          (V i) (⋃ j ∈ s, V j) := by
        intro x y hx hy
        obtain ⟨j, hj, hyj⟩ := Set.mem_iUnion₂.1 hy
        have hne : i ≠ j := by
          rintro rfl
          exact hi hj
        exact hsep hne hx hyj
      have hmeas : MeasurableSet[(ShellField.lihLocalSigma (⋃ j ∈ s, V j)).comap
          (fun omega : ShellSeq d => omega l)] (⋂ j ∈ s, f j) := by
        refine @Finset.measurableSet_biInter _ _
          ((ShellField.lihLocalSigma (⋃ j ∈ s, V j)).comap
            (fun omega : ShellSeq d => omega l)) _ _ (fun j hj => ?_)
        exact MeasurableSpace.comap_mono
          (lihLocalSigma_mono (fun x hx => Set.mem_iUnion₂.2 ⟨j, hj, hx⟩)) _
          (hf j (Finset.mem_insert_of_mem hj))
      have hindep := indep_shellLocal_of_cutoff_separation M l l le_rfl
        (V i) (⋃ j ∈ s, V j) (hV i) hUnion hsepUnion
      have hprod := (Indep_iff _ _ M.P.toMeasure).1 hindep (f i) (⋂ j ∈ s, f j)
        (hf i (Finset.mem_insert_self i s)) hmeas
      rw [Finset.set_biInter_insert, hprod, Finset.prod_insert hi,
        ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))]

/-! ## The per-`(index, shell)` read region -/

/-- **The read region of index `i` at shell `l`.**  Index `i` truncates at level
`Lidx i`, so it reads shell `l` only when `l ≤ Lidx i`; there it reads `U i`,
and elsewhere nothing. -/
def activeShellRegion (Lidx : iota → ℤ) (U : iota → Set (Vec d)) (i : iota) (l : ℤ) :
    Set (Vec d) :=
  if l ≤ Lidx i then U i else ∅

theorem activeShellRegion_of_le {Lidx : iota → ℤ} {U : iota → Set (Vec d)} {i : iota}
    {l : ℤ} (hl : l ≤ Lidx i) : activeShellRegion Lidx U i l = U i :=
  ite_eq_left hl

theorem measurableSet_activeShellRegion {Lidx : iota → ℤ} {U : iota → Set (Vec d)}
    (hU : ∀ i, MeasurableSet (U i)) (i : iota) (l : ℤ) :
    MeasurableSet (activeShellRegion Lidx U i l) := by
  unfold activeShellRegion
  split_ifs
  · exact hU i
  · exact MeasurableSet.empty

/-- **The `(index, shell)` sigma-field**: what index `i` can see of shell `l`. -/
def activeShellSigma (Lidx : iota → ℤ) (U : iota → Set (Vec d)) (i : iota) (l : ℤ) :
    MeasurableSpace (ShellSeq d) :=
  (ShellField.lihLocalSigma (activeShellRegion Lidx U i l)).comap
    (fun omega : ShellSeq d => omega l)

/-- The `(index, shell)` sigma-field is contained in the whole information of
shell `l`. -/
theorem activeShellSigma_le (Lidx : iota → ℤ) (U : iota → Set (Vec d)) (i : iota)
    (l : ℤ) :
    activeShellSigma Lidx U i l ≤
      MeasurableSpace.comap (fun omega : ShellSeq d => omega l) inferInstance :=
  MeasurableSpace.comap_mono (ShellField.lihLocalSigma_le_borel _)

/-- **The varying-level locality, in the direction the producer needs.**  Every
shell at or below `Lidx i` is read on `U i`, so the proved lower-shell local
sigma-field of index `i` sits inside the single join of its `(index, shell)`
sigma-fields. -/
theorem lowerShellLocalSigma_le_iSup_activeShellSigma (Lidx : iota → ℤ)
    (U : iota → Set (Vec d)) (i : iota) :
    lowerShellLocalSigma (Lidx i) (U i) ≤ ⨆ l : ℤ, activeShellSigma Lidx U i l := by
  refine iSup_le fun r => ?_
  have hle : Lidx i - (r : ℤ) ≤ Lidx i := by omega
  have hEq : activeShellSigma Lidx U i (Lidx i - (r : ℤ))
      = (ShellField.lihLocalSigma (U i)).comap
        (fun omega : ShellSeq d => omega (Lidx i - (r : ℤ))) := by
    unfold activeShellSigma
    rw [activeShellRegion_of_le hle]
  rw [← hEq]
  exact le_iSup (fun l : ℤ => activeShellSigma Lidx U i l) (Lidx i - (r : ℤ))

/-! ## The producer -/

/-- **Row independence at a fixed shell.**  For each shell `l` the family of
`(index, shell)` sigma-fields is mutually independent.

The regions active at `l` are pairwise `(sqrt d * 3 ^ l)`-separated: if both `i`
and `j` read shell `l` then `l ≤ Lidx i` and `l ≤ Lidx j`, hence
`l ≤ min (Lidx i) (Lidx j)` and the hypothesis supplies the larger threshold
`sqrt d * 3 ^ min`; if either is inactive its region is empty and separation is
vacuous. -/
theorem iIndep_activeShellSigma_row (M : ABKModel d) (Lidx : iota → ℤ)
    {U : iota → Set (Vec d)} (hU : ∀ i, MeasurableSet (U i))
    (hsep : Pairwise fun i j =>
      SeparatedBy (Real.sqrt (d : ℝ) * (3 : ℝ) ^ (min (Lidx i) (Lidx j))) (U i) (U j))
    (l : ℤ) :
    iIndep (fun i => activeShellSigma Lidx U i l) M.P.toMeasure := by
  have hsepA : Pairwise fun i j =>
      SeparatedBy (Real.sqrt (d : ℝ) * (3 : ℝ) ^ l)
        (activeShellRegion Lidx U i l) (activeShellRegion Lidx U j l) := by
    intro i j hij x y hx hy
    by_cases hi : l ≤ Lidx i
    · by_cases hj : l ≤ Lidx j
      · have hmono : Real.sqrt (d : ℝ) * (3 : ℝ) ^ l
            ≤ Real.sqrt (d : ℝ) * (3 : ℝ) ^ (min (Lidx i) (Lidx j)) :=
          mul_le_mul_of_nonneg_left
            (zpow_le_zpow_right₀ (by norm_num) (le_min hi hj)) (Real.sqrt_nonneg _)
        refine le_trans hmono (hsep hij ?_ ?_)
        · rwa [activeShellRegion_of_le hi] at hx
        · rwa [activeShellRegion_of_le hj] at hy
      · rw [activeShellRegion, ite_eq_right hj] at hy
        exact absurd hy (Set.notMem_empty y)
    · rw [activeShellRegion, ite_eq_right hi] at hx
      exact absurd hx (Set.notMem_empty x)
  exact iIndep_shellLocalSigma_of_pairwise_separated M l
    (fun i => measurableSet_activeShellRegion hU i l) hsepA

/-- **The producer, sigma-field form on the shell sequence.**  At the honest
threshold `sqrt d * 3 ^ (min (Lidx i) (Lidx j))`, the lower-shell local
sigma-fields read at the index-dependent levels `Lidx i` are mutually
independent.

The cross-shell assumption of ABK26 supplies the mutual independence of the shells;
`iIndep_activeShellSigma_row` supplies each row; `iIndep_iSup_of_iIndep_rows` assembles
the joins, and each join dominates the corresponding lower-shell local sigma-field. -/
theorem iIndep_lowerShellLocalSigma_of_varyingLevel (M : ABKModel d) (Lidx : iota → ℤ)
    {U : iota → Set (Vec d)} (hU : ∀ i, MeasurableSet (U i))
    (hsep : Pairwise fun i j =>
      SeparatedBy (Real.sqrt (d : ℝ) * (3 : ℝ) ^ (min (Lidx i) (Lidx j))) (U i) (U j)) :
    iIndep (fun i => lowerShellLocalSigma (Lidx i) (U i)) M.P.toMeasure := by
  have hjoin : iIndep (fun i => ⨆ l : ℤ, activeShellSigma Lidx U i l) M.P.toMeasure :=
    iIndep_iSup_of_iIndep_rows
      (kappa := fun l : ℤ =>
        MeasurableSpace.comap (fun omega : ShellSeq d => omega l) inferInstance)
      M.shellPrefix.independent.iIndep
      (fun l => (ShellField.measurable_shellCoordinate l).comap_le)
      (fun i l => activeShellSigma_le Lidx U i l)
      (fun l => iIndep_activeShellSigma_row M Lidx hU hsep l)
  exact iIndep_of_le hjoin fun i => lowerShellLocalSigma_le_iSup_activeShellSigma Lidx U i

/-- **Mutual independence survives completion by ambient null sets.**  The genuine
lower-infinite cutoff is measurable only for the completed lower-shell
sigma-field, so this is the form in which the varying-level producer can be
consumed.  It is the mutual analogue of the proved two-set result
`Cutoff.indep_lowerShellLocalCompletion_of_indep`. -/
theorem iIndep_lowerShellLocalCompletion_of_iIndep (M : ABKModel d) (Lidx : iota → ℤ)
    (U : iota → Set (Vec d))
    (h : iIndep (fun i => lowerShellLocalSigma (Lidx i) (U i)) M.P.toMeasure) :
    iIndep (fun i => lowerShellLocalCompletion M (Lidx i) (U i)) M.P.toMeasure := by
  classical
  rw [iIndep_iff]
  intro s f hf
  have hchoice : ∀ i ∈ s, ∃ t : Set (ShellSeq d),
      MeasurableSet[lowerShellLocalSigma (Lidx i) (U i)] t ∧
        f i =ᵐ[M.P.toMeasure] t := fun i hi => hf i hi
  choose! t ht hft using hchoice
  rw [measure_congr (aeEq_biInter s hft), h.meas_biInter ht]
  exact Finset.prod_congr rfl fun i hi => (measure_congr (hft i hi)).symm

/-- **The producer, sigma-field form on the genuine cutoff carrier.**  The
completed statement descends faithfully to the full-measure cutoff subtype
through Borel local representatives, so no containment of a completion in the
ambient Borel sigma-field is claimed.  This is the mutual analogue of the
proved two-set result
`Cutoff.indep_cutoffSampleLocalSigma_of_indep_completion`. -/
theorem iIndep_cutoffSampleLocalSigma_of_iIndep_completion (M : ABKModel d)
    (Lidx : iota → ℤ) (U : iota → Set (Vec d))
    (h : iIndep (fun i => lowerShellLocalCompletion M (Lidx i) (U i)) M.P.toMeasure) :
    iIndep (fun i => cutoffSampleLocalSigma M (Lidx i) (U i))
      (cutoffSampleLaw M).toMeasure := by
  classical
  rw [iIndep_iff]
  intro s f hf
  have hchoice : ∀ i ∈ s, ∃ t : Set (ShellSeq d), MeasurableSet t ∧
      MeasurableSet[lowerShellLocalCompletion M (Lidx i) (U i)] t ∧
        f i =ᵐ[(cutoffSampleLaw M).toMeasure]
          (Subtype.val : CutoffSample d → ShellSeq d) ⁻¹' t := by
    intro i hi
    obtain ⟨s', hs', hpre⟩ := MeasurableSpace.measurableSet_comap.1 (hf i hi)
    obtain ⟨s0, hs0, hs0eq⟩ := hs'
    refine ⟨s0, lowerShellLocalSigma_le_borel (Lidx i) (U i) s0 hs0,
      ⟨s0, hs0, Filter.EventuallyEq.rfl⟩, ?_⟩
    rw [← hpre]
    exact ae_preimage_cutoffSampleLaw M hs0eq
  choose! t htmeas htcomp hft using hchoice
  have hpre : (⋂ i ∈ s, (Subtype.val : CutoffSample d → ShellSeq d) ⁻¹' t i)
      = (Subtype.val : CutoffSample d → ShellSeq d) ⁻¹' (⋂ i ∈ s, t i) := by
    rw [Set.preimage_iInter₂]
  rw [measure_congr (aeEq_biInter s hft), hpre,
    measure_preimage_cutoffSampleLaw M (Finset.measurableSet_biInter s htmeas),
    h.meas_biInter htcomp]
  refine Finset.prod_congr rfl fun i hi => ?_
  rw [measure_congr (hft i hi), measure_preimage_cutoffSampleLaw M (htmeas i hi)]

/-- **The producer on the genuine cutoff carrier**, assembled from the honest
separation geometry alone. -/
theorem iIndep_cutoffSampleLocalSigma_of_varyingLevel (M : ABKModel d)
    (Lidx : iota → ℤ) {U : iota → Set (Vec d)} (hU : ∀ i, MeasurableSet (U i))
    (hsep : Pairwise fun i j =>
      SeparatedBy (Real.sqrt (d : ℝ) * (3 : ℝ) ^ (min (Lidx i) (Lidx j))) (U i) (U j)) :
    iIndep (fun i => cutoffSampleLocalSigma M (Lidx i) (U i))
      (cutoffSampleLaw M).toMeasure :=
  iIndep_cutoffSampleLocalSigma_of_iIndep_completion M Lidx U
    (iIndep_lowerShellLocalCompletion_of_iIndep M Lidx U
      (iIndep_lowerShellLocalSigma_of_varyingLevel M Lidx hU hsep))

/-- **The producer, observable form.**  Real observables of the genuine cutoff sample that
are local in `U i` and read only truncations at or below their own level `Lidx
i` are mutually independent, provided the observation regions are pairwise
separated at the honest threshold `sqrt d * 3 ^ (min (Lidx i) (Lidx j))`.

The atom `Phi i` is an arbitrary functional of the whole sample that is
measurable for `cutoffSampleLocalSigma M (Lidx i) (U i)`; it may therefore read
*every* truncation `k_{L'}` with `L' ≤ Lidx i`, each only on `U i`, which is
exactly what ABK26's atoms do (ABK26: one truncation per inner scale). -/
theorem iIndepFun_of_local_cutoffSample (M : ABKModel d) (Lidx : iota → ℤ)
    {U : iota → Set (Vec d)} (hU : ∀ i, MeasurableSet (U i))
    (hsep : Pairwise fun i j =>
      SeparatedBy (Real.sqrt (d : ℝ) * (3 : ℝ) ^ (min (Lidx i) (Lidx j))) (U i) (U j))
    {Phi : iota → CutoffSample d → ℝ}
    (hPhi : ∀ i, Measurable[cutoffSampleLocalSigma M (Lidx i) (U i)] (Phi i)) :
    iIndepFun Phi (cutoffSampleLaw M).toMeasure :=
  iIndepFun_of_iIndep_sigma
    (iIndep_cutoffSampleLocalSigma_of_varyingLevel M Lidx hU hsep) hPhi

/-! ## Placing a read of any lower truncation inside the one sigma-field -/

end

end Algsuperdiff.Section4.Probability
