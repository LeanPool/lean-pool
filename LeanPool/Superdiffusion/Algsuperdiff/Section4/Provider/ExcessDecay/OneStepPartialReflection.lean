/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepOddPackaging
public import LeanPool.Superdiffusion.Algsuperdiff.Section4.Provider.ExcessDecay.OneStepOddMultiFace

/-!
# OneStepPartialReflection

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# The multi-face odd reflection, unconditional

## The iteration

`exists_h1_oddReflection_chain` runs the Finset induction over the met set.  At
each stage `B_T → B_{T∪{i}}` it invokes

* the packaging (`OneStepOddPackaging.exists_h1Function_oddFaceExtend`) at the
  proved stage geometry (`faceHalf_partialReflectedWindow_insert_*`,
  `mem_partialReflectedWindow_coordFaceReflection_iff_*`),
* the zero-trace transport
  (`OneStepOddPackaging.localizedZeroTraceFunctionOn_oddFaceExtend`),

carrying four invariants: weak harmonicity on `B_T`; the restriction pinning
(`w = v` pointwise on the window); pointwise oddness under every already
unfolded met-face reflection; and the face-only zero trace of the stage
function, localized in the full box `B_S`.  The oddness invariant is *exact*
(no null sets): the newly unfolded face is odd by the very shape of
`oddFaceExtend`, and the previously unfolded faces stay odd because distinct
coordinate reflections commute and each stage box is invariant under them.

## The endpoint

`exists_h1_oddReflection_reflectedWindow`: for **any** met configuration
(interior, one face, edge, corner), a weakly harmonic `v ∈ H¹((x+□_k) ∩ □_m)`
with face-only zero trace has a weakly harmonic `H¹` extension to
`reflectedWindow x m k` that restricts to `v` on the window and is pointwise
odd under every met-face reflection.  The met set is realized as the
`Finset.filter` of the met-face predicates (`metSet`), so the one-face
hypothesis `hother` of the proved transfer is *gone*.

The operator reconciliation (the extension is a fixed point of the proved
partial odd reflection `oddExtend`, a.e.) and the composition into the proved
Schauder consumers are in `OneStepPartialReflectionCompose`.
-/

namespace Algsuperdiff.Section4.Provider.ExcessDecay

open HCPolySupport Algsuperdiff.Section4.Support MeasureTheory Filter Topology

noncomputable section

variable {d : ℕ}

/-! ## 1. Distinct coordinate reflections commute -/

/-- Face reflections in distinct coordinates commute, for arbitrary pivots. -/
theorem coordFaceReflection_comm {i j : Fin d} (hij : i ≠ j) (a b : ℝ) (y : Vec d) :
    coordFaceReflection a i (coordFaceReflection b j y)
      = coordFaceReflection b j (coordFaceReflection a i y) := by
  funext l
  simp only [coordFaceReflection_apply]
  by_cases hli : l = i
  · subst hli
    simp [hij]
  · by_cases hlj : l = j
    · subst hlj
      simp [hli]
    · simp [hli, hlj]

/-! ## 2. Monotonicity of the intermediate boxes -/

/-- The intermediate boxes grow with the reflected set: reflecting more faces
only enlarges the box.  Proved pointwise (the endpoint comparisons fail for
degenerate windows, exactly as in `truncatedWindow_subset_reflectedWindow`). -/
theorem partialReflectedWindow_subset_of_subset (x : Vec d) (m k : ℤ)
    {T T' : Finset (Fin d)} (hTT' : T ⊆ T') :
    partialReflectedWindow x m k T ⊆ partialReflectedWindow x m k T' := by
  intro y hy
  rw [mem_partialReflectedWindow_iff] at hy ⊢
  intro j
  have hj := hy j
  by_cases hjT : j ∈ T
  · have hjT' : j ∈ T' := hTT' hjT
    rw [partialReflectedLo, ite_eq_left hjT, partialReflectedHi, ite_eq_left hjT] at hj
    rw [partialReflectedLo, ite_eq_left hjT', partialReflectedHi, ite_eq_left hjT']
    exact hj
  · rw [partialReflectedLo, ite_eq_right hjT, partialReflectedHi, ite_eq_right hjT] at hj
    by_cases hjT' : j ∈ T'
    · rw [partialReflectedLo, ite_eq_left hjT', partialReflectedHi, ite_eq_left hjT']
      have hlo := hj.1
      have hhi := hj.2
      have hlo' : -(1 / 2 : ℝ) * (3 : ℝ) ^ m < y j :=
        lt_of_le_of_lt (neg_half_zpow_le_windowLo x m k j) hlo
      have hhi' : y j < (1 / 2 : ℝ) * (3 : ℝ) ^ m :=
        lt_of_lt_of_le hhi (windowHi_le_half_zpow x m k j)
      constructor
      · by_cases h : MeetsLowerFace x m k j
        · rw [reflectedLo_of_meetsLowerFace h]
          linarith only [hhi, hlo']
        · rw [reflectedLo_of_not_meetsLowerFace h]
          exact hlo
      · by_cases h : MeetsUpperFace x m k j
        · rw [reflectedHi_of_meetsUpperFace h]
          linarith only [hlo, hhi']
        · rw [reflectedHi_of_not_meetsUpperFace h]
          exact hhi
    · rw [partialReflectedLo, ite_eq_right hjT', partialReflectedHi, ite_eq_right hjT']
      exact hj

/-- The window sits inside every intermediate box. -/
theorem truncatedWindow_subset_partialReflectedWindow (x : Vec d) (m k : ℤ)
    (T : Finset (Fin d)) :
    truncatedWindow x m k ⊆ partialReflectedWindow x m k T := by
  rw [← partialReflectedWindow_empty x m k]
  exact partialReflectedWindow_subset_of_subset x m k (Finset.empty_subset T)

/-! ## 3. The met set -/

/-- **The met set** of the window `(x+□_k) ∩ □_m`: the coordinates whose upper
or lower face of `∂□_m` is met.  Classical choice supplies the decidability of
the two real inequalities. -/
def metSet (x : Vec d) (m k : ℤ) : Finset (Fin d) :=
  @Finset.filter (Fin d)
    (fun i => MeetsUpperFace x m k i ∨ MeetsLowerFace x m k i)
    (Classical.decPred _) Finset.univ

theorem mem_metSet_iff {x : Vec d} {m k : ℤ} {i : Fin d} :
    i ∈ metSet x m k ↔ MeetsUpperFace x m k i ∨ MeetsLowerFace x m k i := by
  let : DecidablePred fun i : Fin d =>
      MeetsUpperFace x m k i ∨ MeetsLowerFace x m k i := Classical.decPred _
  unfold metSet
  exact ⟨fun h => (Finset.mem_filter.1 h).2,
    fun h => Finset.mem_filter.2 ⟨Finset.mem_univ i, h⟩⟩

/-- At the met set, the last intermediate box is the fully reflected window. -/
theorem partialReflectedWindow_metSet (x : Vec d) (m k : ℤ) :
    partialReflectedWindow x m k (metSet x m k) = reflectedWindow x m k :=
  partialReflectedWindow_eq_reflectedWindow fun i hi =>
    ⟨fun h => hi ((mem_metSet_iff (i := i)).2 (Or.inl h)),
     fun h => hi ((mem_metSet_iff (i := i)).2 (Or.inr h))⟩

/-! ## 4. The chain: the per-stage packaging, constructed -/

private theorem oddReflection_upperFaceExtension :
    ∀ {d : ℕ} {x : Vec d} {m k : ℤ} (_ : k < m) {S : Finset (Fin d)}
      (v : H1Function (truncatedWindow x m k)) (i : Fin d) (T : Finset (Fin d)) (_ : i ∉ T) (_ :
        insert i T ⊆ S)
      (_ : i ∈ S) (w : H1Function (partialReflectedWindow x m k T))
      (_ : IsWeaklyHarmonicOn (partialReflectedWindow x m k T) w)
      (_ : ∀ y ∈ truncatedWindow x m k, w.toFun y = v.toFun y)
      (_ :
        ∀ j ∈ T,
          (MeetsUpperFace x m k j →
              ∀ (z : Vec d), w.toFun (coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) j z) =
                -w.toFun z) ∧
            (MeetsLowerFace x m k j →
              ∀ (z : Vec d), w.toFun (coordFaceReflection (-(1 / 2 : ℝ) * (3 : ℝ) ^ m) j z) =
                -w.toFun z))
      (_ : LocalizedZeroTraceFunctionOn (partialReflectedWindow x m k T) (partialReflectedWindow x
        m k S) w.toFun)
      (_ : partialReflectedWindow x m k (insert i T) ⊆ partialReflectedWindow x m k S)
      (_ :
        LocalizedZeroTraceFunctionOn (partialReflectedWindow x m k T) (partialReflectedWindow x m
          k (insert i T)) w.toFun)
      (_ : MeetsUpperFace x m k i),
      ∃ (w : H1Function (partialReflectedWindow x m k (insert i T))),
        IsWeaklyHarmonicOn (partialReflectedWindow x m k (insert i T)) w ∧
          (∀ y ∈ truncatedWindow x m k, w.toFun y = v.toFun y) ∧
            (∀ j ∈ insert i T,
                (MeetsUpperFace x m k j →
                    ∀ (z : Vec d), w.toFun (coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) j z) =
                      -w.toFun z) ∧
                  (MeetsLowerFace x m k j →
                    ∀ (z : Vec d), w.toFun (coordFaceReflection (-(1 / 2 : ℝ) * (3 : ℝ) ^ m) j z)
                      = -w.toFun z)) ∧
              LocalizedZeroTraceFunctionOn (partialReflectedWindow x m k (insert i T))
                (partialReflectedWindow x m k S)
                w.toFun := by
  intro d x m k hkm S v i T hiT _ hiS w hwharm hwpin hwodd hwzt _ hztT hup
  -- unfold the upper `i`-face
  have hset : faceHalf (partialReflectedWindow x m k (insert i T)) i
      ((1 / 2 : ℝ) * (3 : ℝ) ^ m) 1 = partialReflectedWindow x m k T :=
    faceHalf_partialReflectedWindow_insert_upper hkm hup hiT
  have hsymmB := mem_partialReflectedWindow_coordFaceReflection_iff_upper
    hkm hup (Finset.mem_insert_self i T)
  have hsymmS := mem_partialReflectedWindow_coordFaceReflection_iff_upper
    hkm hup hiS
  obtain ⟨w', hval', hgrad'⟩ := exists_h1Function_oddFaceExtend
    (isOpenBoundedConvexDomain_partialReflectedWindow x m k (insert i T))
    hsymmB (h1FunctionOfSetEq hset.symm w)
    (by rw [h1FunctionOfSetEq_toFun, hset]; exact hztT)
  have hval : ∀ y, w'.toFun y = oddFaceExtend ((1 / 2 : ℝ) * (3 : ℝ) ^ m) i
      (zeroExtend (partialReflectedWindow x m k T) w.toFun) y := by
    intro y
    rw [hval' y, h1FunctionOfSetEq_toFun, hset]
  have hgrad : ∀ y, w'.grad y = oddFaceExtendGrad ((1 / 2 : ℝ) * (3 : ℝ) ^ m) i
      (zeroExtendGrad (partialReflectedWindow x m k T) w.grad) y := by
    intro y
    rw [hgrad' y, h1FunctionOfSetEq_grad, hset]
  refine ⟨w', isWeaklyHarmonicOn_partialReflectedWindow_insert_upper hkm hup hiT
    w hwharm w' hgrad, ?_, ?_, ?_⟩
  · -- restriction pinning
    intro y hy
    have hyT : y ∈ partialReflectedWindow x m k T :=
      truncatedWindow_subset_partialReflectedWindow x m k T hy
    have hry : coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) i y
        ∉ partialReflectedWindow x m k T := by
      rw [← hset] at hyT ⊢
      exact coordFaceReflection_notMem_faceHalf hyT
    rw [hval y, oddFaceExtend_zeroExtend_of_mem w.toFun _ i hyT hry]
    exact hwpin y hy
  · -- oddness under every unfolded reflection
    intro j hj
    rcases Finset.mem_insert.1 hj with hji | hjT
    · subst hji
      refine ⟨fun _ z => ?_, fun hlowi => absurd hlowi
        (not_meetsLowerFace_of_meetsUpperFace hkm hup)⟩
      rw [hval (coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) j z), hval z]
      exact oddFaceExtend_comp_coordFaceReflection _ j _ z
    · have hji : j ≠ i := fun h => hiT (h ▸ hjT)
      constructor
      · intro hjup z
        have hjinv := mem_partialReflectedWindow_coordFaceReflection_iff_upper
          (T := T) hkm hjup hjT
        have hZodd : ∀ u : Vec d,
            zeroExtend (partialReflectedWindow x m k T) w.toFun
              (coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) j u)
            = -zeroExtend (partialReflectedWindow x m k T) w.toFun u := by
          intro u
          by_cases hu : u ∈ partialReflectedWindow x m k T
          · rw [zeroExtend_of_mem _ ((hjinv u).2 hu), zeroExtend_of_mem _ hu]
            exact (hwodd j hjT).1 hjup u
          · rw [zeroExtend_of_notMem _ (fun hc => hu ((hjinv u).1 hc)),
              zeroExtend_of_notMem _ hu, neg_zero]
        rw [hval (coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) j z), hval z]
        change zeroExtend (partialReflectedWindow x m k T) w.toFun
              (coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) j z)
            - zeroExtend (partialReflectedWindow x m k T) w.toFun
                (coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) i
                  (coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) j z))
          = -(zeroExtend (partialReflectedWindow x m k T) w.toFun z
            - zeroExtend (partialReflectedWindow x m k T) w.toFun
                (coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) i z))
        rw [hZodd z, coordFaceReflection_comm hji.symm _ _ z,
          hZodd (coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) i z)]
        ring
      · intro hjlow z
        have hjinv := mem_partialReflectedWindow_coordFaceReflection_iff_lower
          (T := T) hkm hjlow hjT
        have hZodd : ∀ u : Vec d,
            zeroExtend (partialReflectedWindow x m k T) w.toFun
              (coordFaceReflection (-(1 / 2 : ℝ) * (3 : ℝ) ^ m) j u)
            = -zeroExtend (partialReflectedWindow x m k T) w.toFun u := by
          intro u
          by_cases hu : u ∈ partialReflectedWindow x m k T
          · rw [zeroExtend_of_mem _ ((hjinv u).2 hu), zeroExtend_of_mem _ hu]
            exact (hwodd j hjT).2 hjlow u
          · rw [zeroExtend_of_notMem _ (fun hc => hu ((hjinv u).1 hc)),
              zeroExtend_of_notMem _ hu, neg_zero]
        rw [hval (coordFaceReflection (-(1 / 2 : ℝ) * (3 : ℝ) ^ m) j z), hval z]
        change zeroExtend (partialReflectedWindow x m k T) w.toFun
              (coordFaceReflection (-(1 / 2 : ℝ) * (3 : ℝ) ^ m) j z)
            - zeroExtend (partialReflectedWindow x m k T) w.toFun
                (coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) i
                  (coordFaceReflection (-(1 / 2 : ℝ) * (3 : ℝ) ^ m) j z))
          = -(zeroExtend (partialReflectedWindow x m k T) w.toFun z
            - zeroExtend (partialReflectedWindow x m k T) w.toFun
                (coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) i z))
        rw [hZodd z, coordFaceReflection_comm hji.symm _ _ z,
          hZodd (coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) i z)]
        ring
  · -- the transported face-only zero trace
    have htrans := localizedZeroTraceFunctionOn_oddFaceExtend
      (isOpen_partialReflectedWindow x m k T).measurableSet
      (isOpen_partialReflectedWindow x m k (insert i T))
      (partialReflectedWindow_subset_of_subset x m k
        (Finset.subset_insert i T))
      hsymmB hsymmS hwzt
    have hfun : w'.toFun = oddFaceExtend ((1 / 2 : ℝ) * (3 : ℝ) ^ m) i
        (zeroExtend (partialReflectedWindow x m k T) w.toFun) := funext hval
    rw [hfun]
    exact htrans


/-- **The multi-face chain, unconditional.**  From a weakly harmonic
`v ∈ H¹((x+□_k) ∩ □_m)` with face-only zero trace (localized in `B_S`), every
intermediate box `B_T`, `T ⊆ S`, carries a weakly harmonic `H¹` function that
restricts to `v` on the window, is pointwise odd under every unfolded met-face
reflection, and again has face-only zero trace localized in `B_S`. -/
theorem exists_h1_oddReflection_chain {x : Vec d} {m k : ℤ} (hkm : k < m)
    {S : Finset (Fin d)}
    (hSup : ∀ i ∈ S, MeetsUpperFace x m k i ∨ MeetsLowerFace x m k i)
    (v : H1Function (truncatedWindow x m k))
    (hv : IsWeaklyHarmonicOn (truncatedWindow x m k) v)
    (hzt : LocalizedZeroTraceFunctionOn (truncatedWindow x m k)
      (partialReflectedWindow x m k S) v.toFun) :
    ∀ T : Finset (Fin d), T ⊆ S →
      ∃ w : H1Function (partialReflectedWindow x m k T),
        IsWeaklyHarmonicOn (partialReflectedWindow x m k T) w ∧
        (∀ y ∈ truncatedWindow x m k, w.toFun y = v.toFun y) ∧
        (∀ j ∈ T,
          (MeetsUpperFace x m k j → ∀ z : Vec d,
            w.toFun (coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) j z)
              = -w.toFun z) ∧
          (MeetsLowerFace x m k j → ∀ z : Vec d,
            w.toFun (coordFaceReflection (-(1 / 2 : ℝ) * (3 : ℝ) ^ m) j z)
              = -w.toFun z)) ∧
        LocalizedZeroTraceFunctionOn (partialReflectedWindow x m k T)
          (partialReflectedWindow x m k S) w.toFun := by
  classical
  intro T
  induction T using Finset.induction_on with
  | empty =>
      intro _
      have hset0 : partialReflectedWindow x m k ∅ = truncatedWindow x m k :=
        partialReflectedWindow_empty x m k
      refine ⟨h1FunctionOfSetEq hset0.symm v,
        isWeaklyHarmonicOn_h1FunctionOfSetEq hset0.symm hv, ?_, ?_, ?_⟩
      · intro y _
        rw [h1FunctionOfSetEq_toFun]
      · intro j hj
        exact absurd hj (Finset.notMem_empty j)
      · rw [h1FunctionOfSetEq_toFun, hset0]
        exact hzt
  | @insert i T hiT ih =>
      intro hsub
      have hTsub : T ⊆ S := fun j hj => hsub (Finset.mem_insert_of_mem hj)
      have hiS : i ∈ S := hsub (Finset.mem_insert_self i T)
      obtain ⟨w, hwharm, hwpin, hwodd, hwzt⟩ := ih hTsub
      have hBsub : partialReflectedWindow x m k (insert i T)
          ⊆ partialReflectedWindow x m k S :=
        partialReflectedWindow_subset_of_subset x m k hsub
      have hztT : LocalizedZeroTraceFunctionOn (partialReflectedWindow x m k T)
          (partialReflectedWindow x m k (insert i T)) w.toFun :=
        localizedZeroTraceFunctionOn_mono_window hBsub hwzt
      by_cases hup : MeetsUpperFace x m k i
      · exact @oddReflection_upperFaceExtension (d) (x) (m) (k) (hkm) (S) (v) (i) (T) (hiT) (hsub)
          (hiS) (w) (hwharm) (hwpin) (hwodd) (hwzt) (hBsub) (hztT) (hup)
      · -- unfold the lower `i`-face
        have hlow : MeetsLowerFace x m k i := (hSup i hiS).resolve_left hup
        have hset : faceHalf (partialReflectedWindow x m k (insert i T)) i
            (-(1 / 2 : ℝ) * (3 : ℝ) ^ m) (-1) = partialReflectedWindow x m k T :=
          faceHalf_partialReflectedWindow_insert_lower hkm hlow hiT
        have hsymmB := mem_partialReflectedWindow_coordFaceReflection_iff_lower
          hkm hlow (Finset.mem_insert_self i T)
        have hsymmS := mem_partialReflectedWindow_coordFaceReflection_iff_lower
          hkm hlow hiS
        obtain ⟨w', hval', hgrad'⟩ := exists_h1Function_oddFaceExtend
          (isOpenBoundedConvexDomain_partialReflectedWindow x m k (insert i T))
          hsymmB (h1FunctionOfSetEq hset.symm w)
          (by rw [h1FunctionOfSetEq_toFun, hset]; exact hztT)
        have hval : ∀ y, w'.toFun y = oddFaceExtend (-(1 / 2 : ℝ) * (3 : ℝ) ^ m) i
            (zeroExtend (partialReflectedWindow x m k T) w.toFun) y := by
          intro y
          rw [hval' y, h1FunctionOfSetEq_toFun, hset]
        have hgrad : ∀ y, w'.grad y = oddFaceExtendGrad (-(1 / 2 : ℝ) * (3 : ℝ) ^ m) i
            (zeroExtendGrad (partialReflectedWindow x m k T) w.grad) y := by
          intro y
          rw [hgrad' y, h1FunctionOfSetEq_grad, hset]
        refine ⟨w', isWeaklyHarmonicOn_partialReflectedWindow_insert_lower hkm hlow hiT
          w hwharm w' hgrad, ?_, ?_, ?_⟩
        · intro y hy
          have hyT : y ∈ partialReflectedWindow x m k T :=
            truncatedWindow_subset_partialReflectedWindow x m k T hy
          have hry : coordFaceReflection (-(1 / 2 : ℝ) * (3 : ℝ) ^ m) i y
              ∉ partialReflectedWindow x m k T := by
            rw [← hset] at hyT ⊢
            exact coordFaceReflection_notMem_faceHalf hyT
          rw [hval y, oddFaceExtend_zeroExtend_of_mem w.toFun _ i hyT hry]
          exact hwpin y hy
        · intro j hj
          rcases Finset.mem_insert.1 hj with hji | hjT
          · subst hji
            refine ⟨fun hupi => absurd hlow
              (not_meetsLowerFace_of_meetsUpperFace hkm hupi), fun _ z => ?_⟩
            rw [hval (coordFaceReflection (-(1 / 2 : ℝ) * (3 : ℝ) ^ m) j z), hval z]
            exact oddFaceExtend_comp_coordFaceReflection _ j _ z
          · have hji : j ≠ i := fun h => hiT (h ▸ hjT)
            constructor
            · intro hjup z
              have hjinv := mem_partialReflectedWindow_coordFaceReflection_iff_upper
                (T := T) hkm hjup hjT
              have hZodd : ∀ u : Vec d,
                  zeroExtend (partialReflectedWindow x m k T) w.toFun
                    (coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) j u)
                  = -zeroExtend (partialReflectedWindow x m k T) w.toFun u := by
                intro u
                by_cases hu : u ∈ partialReflectedWindow x m k T
                · rw [zeroExtend_of_mem _ ((hjinv u).2 hu), zeroExtend_of_mem _ hu]
                  exact (hwodd j hjT).1 hjup u
                · rw [zeroExtend_of_notMem _ (fun hc => hu ((hjinv u).1 hc)),
                    zeroExtend_of_notMem _ hu, neg_zero]
              rw [hval (coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) j z), hval z]
              change zeroExtend (partialReflectedWindow x m k T) w.toFun
                    (coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) j z)
                  - zeroExtend (partialReflectedWindow x m k T) w.toFun
                      (coordFaceReflection (-(1 / 2 : ℝ) * (3 : ℝ) ^ m) i
                        (coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) j z))
                = -(zeroExtend (partialReflectedWindow x m k T) w.toFun z
                  - zeroExtend (partialReflectedWindow x m k T) w.toFun
                      (coordFaceReflection (-(1 / 2 : ℝ) * (3 : ℝ) ^ m) i z))
              rw [hZodd z, coordFaceReflection_comm hji.symm _ _ z,
                hZodd (coordFaceReflection (-(1 / 2 : ℝ) * (3 : ℝ) ^ m) i z)]
              ring
            · intro hjlow z
              have hjinv := mem_partialReflectedWindow_coordFaceReflection_iff_lower
                (T := T) hkm hjlow hjT
              have hZodd : ∀ u : Vec d,
                  zeroExtend (partialReflectedWindow x m k T) w.toFun
                    (coordFaceReflection (-(1 / 2 : ℝ) * (3 : ℝ) ^ m) j u)
                  = -zeroExtend (partialReflectedWindow x m k T) w.toFun u := by
                intro u
                by_cases hu : u ∈ partialReflectedWindow x m k T
                · rw [zeroExtend_of_mem _ ((hjinv u).2 hu), zeroExtend_of_mem _ hu]
                  exact (hwodd j hjT).2 hjlow u
                · rw [zeroExtend_of_notMem _ (fun hc => hu ((hjinv u).1 hc)),
                    zeroExtend_of_notMem _ hu, neg_zero]
              rw [hval (coordFaceReflection (-(1 / 2 : ℝ) * (3 : ℝ) ^ m) j z), hval z]
              change zeroExtend (partialReflectedWindow x m k T) w.toFun
                    (coordFaceReflection (-(1 / 2 : ℝ) * (3 : ℝ) ^ m) j z)
                  - zeroExtend (partialReflectedWindow x m k T) w.toFun
                      (coordFaceReflection (-(1 / 2 : ℝ) * (3 : ℝ) ^ m) i
                        (coordFaceReflection (-(1 / 2 : ℝ) * (3 : ℝ) ^ m) j z))
                = -(zeroExtend (partialReflectedWindow x m k T) w.toFun z
                  - zeroExtend (partialReflectedWindow x m k T) w.toFun
                      (coordFaceReflection (-(1 / 2 : ℝ) * (3 : ℝ) ^ m) i z))
              rw [hZodd z, coordFaceReflection_comm hji.symm _ _ z,
                hZodd (coordFaceReflection (-(1 / 2 : ℝ) * (3 : ℝ) ^ m) i z)]
              ring
        · have htrans := localizedZeroTraceFunctionOn_oddFaceExtend
            (isOpen_partialReflectedWindow x m k T).measurableSet
            (isOpen_partialReflectedWindow x m k (insert i T))
            (partialReflectedWindow_subset_of_subset x m k
              (Finset.subset_insert i T))
            hsymmB hsymmS hwzt
          have hfun : w'.toFun = oddFaceExtend (-(1 / 2 : ℝ) * (3 : ℝ) ^ m) i
              (zeroExtend (partialReflectedWindow x m k T) w.toFun) := funext hval
          rw [hfun]
          exact htrans

/-! ## 5. The endpoint: the reflected window, any met configuration -/

/-- ** B at the `H¹` level.**  For any met configuration of the window `(x+□_k) ∩
□_m` — interior, one face, edge or corner — a weakly harmonic `v ∈ H¹` with
face-only zero trace extends to a weakly harmonic `H¹(reflectedWindow x m k)`
function that restricts to `v` on the window and is pointwise odd under every
met-face reflection.  The one-met-face hypothesis of the proved transfer is
gone. -/
theorem exists_h1_oddReflection_reflectedWindow {x : Vec d} {m k : ℤ} (hkm : k < m)
    (v : H1Function (truncatedWindow x m k))
    (hv : IsWeaklyHarmonicOn (truncatedWindow x m k) v)
    (hzt : LocalizedZeroTraceFunctionOn (truncatedWindow x m k)
      (reflectedWindow x m k) v.toFun) :
    ∃ w : H1Function (reflectedWindow x m k),
      IsWeaklyHarmonicOn (reflectedWindow x m k) w ∧
      (∀ y ∈ truncatedWindow x m k, w.toFun y = v.toFun y) ∧
      (∀ i : Fin d,
        (MeetsUpperFace x m k i → ∀ z : Vec d,
          w.toFun (coordFaceReflection ((1 / 2 : ℝ) * (3 : ℝ) ^ m) i z)
            = -w.toFun z) ∧
        (MeetsLowerFace x m k i → ∀ z : Vec d,
          w.toFun (coordFaceReflection (-(1 / 2 : ℝ) * (3 : ℝ) ^ m) i z)
            = -w.toFun z)) := by
  have hBS : partialReflectedWindow x m k (metSet x m k) = reflectedWindow x m k :=
    partialReflectedWindow_metSet x m k
  have hzt' : LocalizedZeroTraceFunctionOn (truncatedWindow x m k)
      (partialReflectedWindow x m k (metSet x m k)) v.toFun := by
    rw [hBS]
    exact hzt
  obtain ⟨w₀, hharm, hpin, hodd, -⟩ := exists_h1_oddReflection_chain hkm
    (fun i hi => mem_metSet_iff.1 hi) v hv hzt' (metSet x m k) (subset_refl _)
  refine ⟨h1FunctionOfSetEq hBS w₀, isWeaklyHarmonicOn_h1FunctionOfSetEq hBS hharm,
    ?_, ?_⟩
  · intro y hy
    rw [h1FunctionOfSetEq_toFun]
    exact hpin y hy
  · intro i
    constructor
    · intro hupI z
      rw [h1FunctionOfSetEq_toFun]
      exact (hodd i (mem_metSet_iff.2 (Or.inl hupI))).1 hupI z
    · intro hlowI z
      rw [h1FunctionOfSetEq_toFun]
      exact (hodd i (mem_metSet_iff.2 (Or.inr hlowI))).2 hlowI z

end

end Algsuperdiff.Section4.Provider.ExcessDecay
