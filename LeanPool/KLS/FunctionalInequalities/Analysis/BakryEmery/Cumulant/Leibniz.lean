/-
Copyright (c) 2026 kls-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: kls-lean contributors
-/
module

public import LeanPool.KLS.FunctionalInequalities.Analysis.BakryEmery.Cumulant.Local
public import LeanPool.KLS.FunctionalInequalities.Analysis.IteratedDerivative.Symmetry
public import LeanPool.KLS.FunctionalInequalities.Analysis.IteratedDerivative.InnerProduct

/-!
# Leibniz expansion of the quadratic form of the centred CGF gradient

For a compactly supported probability law `μ` with `Λ = logLaplace μ` and the centred gradient
`v(z) = ∇Λ(z) − ∇Λ(0)`: `directional_centeredGradient_logLaplace_zero_of_compact` evaluates the
directional
derivatives of `v` at `0` (`0` for the empty list, the cumulant Riesz vector `κ_{|l|+1}(l, ·)`
otherwise), and
`iteratedFDeriv_inner_centeredGradient_zero_of_compact` is the raw expansion behind BKL
arXiv:2610.05474v1 (74): for ANY
continuous linear `M`, `Dᵐ⟪v, M v⟫(0)[h]` is the sum over the nonempty proper subset allocations `q`
of
`⟪κ_{|q|+1}(h_q,·), M κ_{m−|q|+1}(h_{¬q},·)⟫`, each with coefficient `1` (no factorial).
`iteratedFDeriv_inner_centeredGradient_zero_grouped_of_compact` is the grouping (72)–(74) for `M =
Cov⁻¹` with
invertible covariance: `2m κ_m` from the singleton allocations plus twice the middle allocations
containing a
fixed slot. No stochastic statement ((71), (73), Lemma 4.3) is in this module.
-/

@[expose] public section

noncomputable section
open MeasureTheory
open FunctionalInequalities.Analysis
open scoped RealInnerProductSpace ContDiff

namespace FunctionalInequalities.Analysis.BakryEmery

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

/--
Directional derivatives at `0` of the centred CGF gradient: `0` for the empty list, `κ_{|l|+1}(l,
·)` otherwise. -/
theorem directional_centeredGradient_logLaplace_zero_of_compact (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (l : List E) :
    directional l
        (fun z : E =>
          gradient (logLaplace (μ : Measure E)) z - gradient (logLaplace (μ : Measure E)) 0)
        0 =
      if l = [] then 0 else cumulantVector (μ : Measure E) l := by
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hΛ : ContDiff ℝ ∞ (logLaplace (μ : Measure E)) :=
    contDiff_logLaplace _ (compact_support_integrable_exp _ hc)
  have hg : ContDiff ℝ ∞ (gradient (logLaplace (μ : Measure E))) := by
    change
      ContDiff ℝ ∞ ((InnerProductSpace.toDual ℝ E).symm ∘ fderiv ℝ (logLaplace (μ : Measure E)))
    exact
      (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearMap.contDiff.comp
        (hΛ.fderiv_right (by simp))
  have hv :
    ContDiff ℝ ∞
      (fun z : E =>
        gradient (logLaplace (μ : Measure E)) z - gradient (logLaplace (μ : Measure E)) 0) :=
    hg.sub contDiff_const
  split_ifs with hl
  · subst hl
    change _ - _ = 0
    exact sub_self _
  · have h1 := directional_ofFn hv l.length l.get 0
    rw [List.ofFn_get] at h1
    rw [h1,
      iteratedFDeriv_centeredGradient_logLaplace_zero_of_compact μ hc _
        (List.length_pos_iff.mpr hl) _,
      List.ofFn_get]

/--
**Raw (74) expansion**: `Dᵐ⟪v, M v⟫(0)[h] = Σ_{∅ ≠ q ≠ [m]} ⟪κ_{|q|+1}(h_q,·), M
κ_{m−|q|+1}(h_{¬q},·)⟫`. -/
theorem iteratedFDeriv_inner_centeredGradient_zero_of_compact (μ : ProbabilityMeasure E)
    (hc : IsCompact (μ : Measure E).support) (M : E →L[ℝ] E) (m : ℕ) (h : Fin m → E) :
    iteratedFDeriv ℝ m
        (fun z : E =>
          ⟪gradient (logLaplace (μ : Measure E)) z - gradient (logLaplace (μ : Measure E)) 0,
            M
              (gradient (logLaplace (μ : Measure E)) z -
                gradient (logLaplace (μ : Measure E)) 0)⟫)
        0 h =
      ∑ q ∈ (Finset.univ.filter fun q : Fin m → Bool => (∃ i, q i = true) ∧ (∃ i, q i = false)),
        ⟪cumulantVector (μ : Measure E) (selected h q),
          M (cumulantVector (μ : Measure E) (selected h (fun i => !(q i))))⟫ := by
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hΛ : ContDiff ℝ ∞ (logLaplace (μ : Measure E)) :=
    contDiff_logLaplace _ (compact_support_integrable_exp _ hc)
  have hg : ContDiff ℝ ∞ (gradient (logLaplace (μ : Measure E))) := by
    change
      ContDiff ℝ ∞ ((InnerProductSpace.toDual ℝ E).symm ∘ fderiv ℝ (logLaplace (μ : Measure E)))
    exact
      (InnerProductSpace.toDual ℝ E).symm.toContinuousLinearMap.contDiff.comp
        (hΛ.fderiv_right (by simp))
  have hv :
    ContDiff ℝ ∞
      (fun z : E =>
        gradient (logLaplace (μ : Measure E)) z - gradient (logLaplace (μ : Measure E)) 0) :=
    hg.sub contDiff_const
  rw [iteratedFDeriv_inner_clm hv hv M m h 0]
  simp_rw [directional_centeredGradient_logLaplace_zero_of_compact μ hc]
  rw [←
    Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun q : Fin m → Bool => (∃ i, q i = true) ∧ (∃ i, q i = false))]
  have hzero :
    (Finset.univ.filter (fun q : Fin m → Bool => ¬((∃ i, q i = true) ∧ (∃ i, q i = false)))).sum
        (fun q =>
          ⟪if selected h q = [] then 0 else cumulantVector (μ : Measure E) (selected h q),
            M
              (if selected h (fun i => !(q i)) = [] then 0
              else cumulantVector (μ : Measure E) (selected h (fun i => !(q i))))⟫) =
      0 := by
    apply Finset.sum_eq_zero
    intro q hq
    have hn := (Finset.mem_filter.mp hq).2
    have hor : (∀ i, q i = false) ∨ (∀ i, q i = true) := by
      by_cases hf : ∀ i, q i = false
      · exact Or.inl hf
      · right
        obtain ⟨i, hi⟩ : ∃ i, q i ≠ false := not_forall.mp hf
        have ht : q i = true := by
          cases hqi : q i with
          | false => exact False.elim (hi hqi)
          | true => rfl
        have hnf : ¬∃ i, q i = false := by
          intro hfalse
          exact hn ⟨⟨i, ht⟩, hfalse⟩
        intro j
        cases hqj : q j with
        | false => exact False.elim (hnf ⟨j, hqj⟩)
        | true => rfl
    rcases hor with hf | ht
    · have hs : selected h q = [] := (selected_eq_nil_iff h q).2 hf
      rw [hs]
      simp
    · have hs : selected h (fun i => !(q i)) = [] :=
        (selected_eq_nil_iff h (fun i => !(q i))).2
          (by
            intro i
            simp [ht i])
      rw [hs]
      simp
  rw [hzero, add_zero]
  apply Finset.sum_congr rfl
  intro q hq
  have hmem := (Finset.mem_filter.mp hq).2
  have hqne : selected h q ≠ [] := by
    intro hs
    have hall := (selected_eq_nil_iff h q).1 hs
    obtain ⟨i, hi⟩ := hmem.1
    have hfalse := hall i
    rw [hi] at hfalse
    cases hfalse
  have hqne' : selected h (fun i => !(q i)) ≠ [] := by
    intro hs
    have hall := (selected_eq_nil_iff h (fun i => !(q i))).1 hs
    obtain ⟨i, hi⟩ := hmem.2
    have hfalse := hall i
    simp [hi] at hfalse
  simp [hqne, hqne']

private theorem one_le_selected_length_iff {α : Type*} {m : ℕ} (h : Fin m → α) (q : Fin m → Bool) :
    1 ≤ (selected h q).length ↔ ∃ i : Fin m, q i = true := by
  constructor
  · intro hq
    by_contra hno
    push Not at hno
    have hall : ∀ i : Fin m, q i = false := by
      intro i
      cases hi : q i with
      | false => rfl
      | true => exact False.elim (hno i hi)
    have he : selected h q = [] := (selected_eq_nil_iff h q).2 hall
    have hz : (selected h q).length = 0 := by simp [he]
    omega
  · rintro ⟨i, hi⟩
    have hz : (selected h q).length ≠ 0 := by
      intro hz
      have he : selected h q = [] := List.length_eq_zero_iff.mp hz
      have hall := (selected_eq_nil_iff h q).mp he
      simpa [hi] using hall i
    omega

private theorem inner_inverse_covariance_comm (mu : ProbabilityMeasure E) (x y : E) :
    ⟪x, Ring.inverse (Covariance.operator (mu : Measure E)) y⟫ =
      ⟪y, Ring.inverse (Covariance.operator (mu : Measure E)) x⟫ := by
  have : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hs := (Covariance.operator_isSelfAdjoint (mu : Measure E)).ringInverse
  have hsym := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hs
  calc
    ⟪x, Ring.inverse (Covariance.operator (mu : Measure E)) y⟫ =
        ⟪Ring.inverse (Covariance.operator (mu : Measure E)) x, y⟫ :=
      (hsym x y).symm
    _ = ⟪y, Ring.inverse (Covariance.operator (mu : Measure E)) x⟫ := real_inner_comm _ _

/-- Exact deterministic grouping of BKL arXiv:2610.05474v1, (72)–(74), at a fixed law: the `2m`
singleton/complement allocations give `2m * kappa_m`, and all middle allocations pair to twice the
sum over the
middle masks containing the slot `i0` (72). It assumes only compact support and invertibility of the
actual
covariance, for every `m ≥ 3`; it contains no stochastic process, Itô formula or cumulant evolution
conclusion.
-/
theorem iteratedFDeriv_inner_centeredGradient_zero_grouped_of_compact
    (mu : ProbabilityMeasure E) (hc : IsCompact (mu : Measure E).support)
    (hA : IsUnit (Covariance.operator (mu : Measure E))) {m : ℕ} (hm : 3 ≤ m) (h : Fin m → E)
    (i0 : Fin m) :
    iteratedFDeriv ℝ m
        (fun z : E =>
          ⟪gradient (logLaplace (mu : Measure E)) z - gradient (logLaplace (mu : Measure E)) 0,
            Ring.inverse (Covariance.operator (mu : Measure E))
              (gradient (logLaplace (mu : Measure E)) z -
                gradient (logLaplace (mu : Measure E)) 0)⟫)
        0 h =
      (2 * (m : ℝ)) * cumulant (mu : Measure E) m h +
        2 *
          ∑
            q ∈
              Finset.univ.filter
                (fun q : Fin m → Bool =>
                  q i0 = true ∧
                    2 ≤ (selected h q).length ∧ 2 ≤ (selected h (fun i => !(q i))).length),
            ⟪cumulantVector (mu : Measure E) (selected h q),
              Ring.inverse (Covariance.operator (mu : Measure E))
                (cumulantVector (mu : Measure E) (selected h (fun i => !(q i))))⟫ := by
  classical
  -- Index the Leibniz terms by the two complementary derivative slots.
  let F : (Fin m → Bool) → ℝ := fun q =>
    ⟪cumulantVector (mu : Measure E) (selected h q),
      Ring.inverse (Covariance.operator (mu : Measure E))
        (cumulantVector (mu : Measure E) (selected h (fun i => !(q i))))⟫
  let l : (Fin m → Bool) → ℕ := fun q => (selected h q).length
  let r : (Fin m → Bool) → ℕ := fun q => (selected h (fun i => !(q i))).length
  let U := Finset.univ.filter (fun q : Fin m → Bool => 1 ≤ l q ∧ 1 ≤ r q)
  let A := Finset.univ.filter (fun q : Fin m → Bool => l q = 1)
  let B := Finset.univ.filter (fun q : Fin m → Bool => r q = 1)
  let C := fun q : Fin m → Bool => 2 ≤ l q ∧ 2 ≤ r q
  let M := Finset.univ.filter C
  let T := Finset.univ.filter (fun q : Fin m → Bool => q i0 = true ∧ C q)
  have hlen (q : Fin m → Bool) : l q + r q = m := by exact (selected_mask_partition h q).1
  have hFcomp (q : Fin m → Bool) : F (fun i => !(q i)) = F q := by
    dsimp [F]
    simp only [Bool.not_not]
    exact
      (inner_inverse_covariance_comm mu
        (cumulantVector (mu : Measure E) (selected h q))
          (cumulantVector (mu : Measure E) (selected h (fun i => !(q i))))).symm
  have hpos (q : Fin m → Bool) : 1 ≤ l q ↔ ∃ i : Fin m, q i = true :=
    one_le_selected_length_iff h q
  have hposFalse (q : Fin m → Bool) : 1 ≤ r q ↔ ∃ i : Fin m, q i = false := by
    constructor
    · intro hq
      have ht : ∃ i : Fin m, (fun j => !(q j)) i = true :=
        (hpos (fun j => !(q j))).1 (by simpa [r] using hq)
      obtain ⟨i, hi⟩ := ht
      cases hqi : q i with
      | false => exact ⟨i, hqi⟩
      | true => simp [hqi] at hi
    · rintro ⟨i, hi⟩
      apply (hpos (fun j => !(q j))).2
      refine ⟨i, ?_⟩
      simp [hi]
  have hfilter :
    Finset.univ.filter (fun q : Fin m → Bool => (∃ i, q i = true) ∧ ∃ i, q i = false) = U := by
    ext q
    simp only [U, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨ht, hf⟩
      exact ⟨(hpos q).2 ht, (hposFalse q).2 hf⟩
    · intro hq
      exact ⟨(hpos q).1 hq.1, (hposFalse q).1 hq.2⟩
  -- Identify the singleton contractions before grouping the Boolean partition.
  have bridge :
    ∀ {k : ℕ} (f g : Fin k → E),
      (List.ofFn f).Perm (List.ofFn g) → ∃ σ : Equiv.Perm (Fin k), g ∘ σ = f := by
    intro k f g hp
    have hm : (Finset.univ.val.map f : Multiset E) = Finset.univ.val.map g := by
      rw [Fin.univ_val_map, Fin.univ_val_map]
      exact Multiset.coe_eq_coe.mpr hp
    have hcard : ∀ a, Fintype.card { i // f i = a } = Fintype.card { i // g i = a } := by
      intro a
      have hc := congrArg (Multiset.count a) hm
      rw [Multiset.count_map, Multiset.count_map] at hc
      simp only [Fintype.card_subtype]
      simpa [Finset.card, Finset.filter_val, eq_comm] using hc
    exact
      ⟨Equiv.ofFiberEquiv (fun a => Fintype.equivOfCardEq (hcard a)),
        funext fun j => Equiv.ofFiberEquiv_map _ j⟩
  have hsingleTerm (i : Fin m) : F (fun j => decide (j = i)) = cumulant (mu : Measure E) m h := by
    dsimp [F]
    obtain ⟨hlen', hperm, hsing, -⟩ := selected_mask_partition h (fun j => decide (j = i))
    set rest := selected h (fun j => !decide (j = i)) with hrest
    rw [hsing i] at hlen' hperm ⊢
    rw [inner_cumulantVector_single_ringInverse_cumulantVector mu hc hA rest (h i)]
    have hl : rest.length + 1 = m := by simpa [Nat.add_comm] using hlen'
    have key :
      ∀ (k : ℕ) (hk : k = m) (v : Fin k → E),
        (List.ofFn v).Perm (List.ofFn h) →
          cumulant (mu : Measure E) k v = cumulant (mu : Measure E) m h := by
      rintro k rfl v hv
      obtain ⟨σ, hσ⟩ := bridge v h hv
      rw [← hσ, cumulant_comp_perm_of_compact mu hc]
    apply key _ hl
    rw [List.ofFn_succ']
    simp only [Fin.snoc_castSucc, Fin.snoc_last, List.concat_eq_append, List.ofFn_get]
    exact (List.perm_append_comm).trans hperm
  have hraw :
    iteratedFDeriv ℝ m
        (fun z : E =>
          ⟪gradient (logLaplace (mu : Measure E)) z - gradient (logLaplace (mu : Measure E)) 0,
            Ring.inverse (Covariance.operator (mu : Measure E))
              (gradient (logLaplace (mu : Measure E)) z -
                gradient (logLaplace (mu : Measure E)) 0)⟫)
        0 h =
      ∑ q ∈ U, F q := by
    calc
      iteratedFDeriv ℝ m
            (fun z : E =>
              ⟪gradient (logLaplace (mu : Measure E)) z -
                  gradient (logLaplace (mu : Measure E)) 0,
                Ring.inverse (Covariance.operator (mu : Measure E))
                  (gradient (logLaplace (mu : Measure E)) z -
                    gradient (logLaplace (mu : Measure E)) 0)⟫)
            0 h =
          ∑
            q ∈
              Finset.univ.filter (fun q : Fin m → Bool => (∃ i, q i = true) ∧ ∃ i, q i = false),
            F q := by
        simpa [F] using
          (iteratedFDeriv_inner_centeredGradient_zero_of_compact mu hc
            (Ring.inverse (Covariance.operator (mu : Measure E))) m h)
      _ = ∑ q ∈ U, F q := by rw [hfilter]
  -- Partition the surviving terms and sum each contraction class.
  have hUA : U.filter (fun q => l q = 1) = A := by
    ext q
    simp only [U, A, Finset.mem_filter, Finset.mem_univ, true_and]
    have hh := hlen q
    omega
  have hUB : (U.filter (fun q => l q ≠ 1)).filter (fun q => r q = 1) = B := by
    ext q
    simp only [U, B, Finset.mem_filter, Finset.mem_univ, true_and]
    have hh := hlen q
    omega
  have hUM : (U.filter (fun q => l q ≠ 1)).filter (fun q => r q ≠ 1) = M := by
    ext q
    simp only [U, M, Finset.mem_filter, Finset.mem_univ, true_and]
    have hh := hlen q
    omega
  have hdecomp : (∑ q ∈ U, F q) = (∑ q ∈ A, F q) + (∑ q ∈ B, F q) + ∑ q ∈ M, F q := by
    have hs₁ := Finset.sum_filter_add_sum_filter_not U (fun q => l q = 1) F
    have hs₂ :=
      Finset.sum_filter_add_sum_filter_not (U.filter (fun q => l q ≠ 1)) (fun q => r q = 1) F
    calc
      (∑ q ∈ U, F q) =
          (∑ q ∈ U.filter (fun q => l q = 1), F q) + ∑ q ∈ U.filter (fun q => l q ≠ 1), F q :=
        hs₁.symm
      _ =
          (∑ q ∈ A, F q) +
            ((∑ q ∈ (U.filter (fun q => l q ≠ 1)).filter (fun q => r q = 1), F q) +
              ∑ q ∈ (U.filter (fun q => l q ≠ 1)).filter (fun q => r q ≠ 1), F q) := by
        rw [hUA, ← hs₂]
      _ = (∑ q ∈ A, F q) + (∑ q ∈ B, F q) + ∑ q ∈ M, F q := by
        rw [hUB, hUM]
        ring
  have hAsingle : (∑ q ∈ A, F q) = ∑ i : Fin m, F (fun j => decide (j = i)) := by
    symm
    refine Finset.sum_bij (fun i _ => fun j => decide (j = i)) ?_ ?_ ?_ ?_
    · intro i _
      simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
      change (selected h (fun j => decide (j = i))).length = 1
      rw [(selected_mask_partition h (fun j => decide (j = i))).2.2.1 i]
      rfl
    · intro a _ b _ hab
      simpa using congrFun hab a
    · intro q hq
      obtain ⟨i, rfl⟩ := (selected_mask_partition h q).2.2.2 (Finset.mem_filter.mp hq).2
      exact ⟨i, Finset.mem_univ _, rfl⟩
    · intro i _
      rfl
  have hAsum : (∑ q ∈ A, F q) = (m : ℝ) * cumulant (mu : Measure E) m h := by
    calc
      (∑ q ∈ A, F q) = ∑ i : Fin m, F (fun j => decide (j = i)) := hAsingle
      _ = ∑ _i : Fin m, cumulant (mu : Measure E) m h := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hsingleTerm i
      _ = (m : ℝ) * cumulant (mu : Measure E) m h := by simp
  have hcomp_inj : ∀ {a b : Fin m → Bool}, (fun i => !(a i)) = (fun i => !(b i)) → a = b := by
    intro a b hab
    have hinvol : Function.Involutive (fun q : Fin m → Bool => fun i => !(q i)) := by
      intro q
      funext i
      simp only [Bool.not_not]
    exact hinvol.injective hab
  have hBsum : (∑ q ∈ B, F q) = (∑ q ∈ A, F q) := by
    refine Finset.sum_bij (fun q _ => fun i => !(q i)) ?_ ?_ ?_ ?_
    · intro q hq
      simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
      simpa [l, r] using (Finset.mem_filter.mp hq).2
    · intro a _ b _ hab
      exact hcomp_inj hab
    · intro q hq
      refine ⟨fun i => !(q i), ?_, ?_⟩
      · simp only [B, Finset.mem_filter, Finset.mem_univ, true_and]
        simpa [l, r] using (Finset.mem_filter.mp hq).2
      · funext i
        simp
    · intro q hq
      exact (hFcomp q).symm
  have hCcomp (q : Fin m → Bool) : C (fun i => !(q i)) ↔ C q := by simp [C, l, r, and_comm]
  have hMsum : (∑ q ∈ M, F q) = 2 * ∑ q ∈ T, F q := by
    exact sum_filter_eq_two_mul_sum_filter_of_compl_invariant C hCcomp F hFcomp i0
  rw [hraw, hdecomp]
  simp only [hBsum, hAsum, hMsum]
  dsimp [T, F, C, l, r]
  ring

end FunctionalInequalities.Analysis.BakryEmery
