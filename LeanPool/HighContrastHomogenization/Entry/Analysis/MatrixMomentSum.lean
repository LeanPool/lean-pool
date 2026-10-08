/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi, Amélie Loher
-/

module

public import LeanPool.HighContrastHomogenization.Entry.Analysis.SchattenHolderInequalities
public import LeanPool.HighContrastHomogenization.Entry.Source.BoundedWindowFiniteness
public import LeanPool.HighContrastHomogenization.Support.Book.Ch04.Internal.CoarseObservableMeasurability.Basic
public import LeanPool.HighContrastHomogenization.Entry.Analysis.SchattenNormIntegrability
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.List.OfFn
public import Mathlib.Probability.Independence.Integration
public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.MeasureTheory.SpecificCodomains.Pi

/-!
# High-contrast homogenization: Entry.Analysis.MatrixMomentSum

Imported from the Apache-2.0 HighContrastHomogenization development at commit
`7a13dbcd8d6609264a713373f5c69ceeac870472`.
-/

public section

/-!
# The independent centered symmetric matrix sum estimate

`l.fixed.geometry.matrix.averaging`:

> Expanding the power gives
> `tr E[(∑_{i ∈ I} Y_i)^N] = ∑_{i_1,…,i_N ∈ I} tr E[Y_{i_1} ⋯ Y_{i_N}]`.

* `pow_sum_eq_sum_prod_ofFn` — the underlying algebraic identity in an arbitrary (in general
  **noncommutative**) ring: `(∑ i ∈ s, M i)^N = ∑_{f : Fin N → s} (List.ofFn (M ∘ f)).prod`.
  The factors are kept in an **ordered** `List.ofFn … |>.prod`; a `Finset.prod` of matrices is
  not available and inventing a commutative structure would be a false statement.  Commutativity
  is not used anywhere in the proof, which is a bare induction on `N` through `Fin.consEquiv`.
* The same identity after `Matrix.trace`, in the shape the printed display uses: the trace of the
  power expands as the sum of the traces of the ordered words.
The operator-norm entry bound in `SchattenNormIntegrability` is public and is used in the
product-integrability bridge.
The proof uses grouped independence to cancel singleton words, exact trace Hölder from K1,
Hölder in probability, and at most `N^N` singleton-free equality patterns.
Taking the even N-th root gives exactly the printed coefficient `N`, without a dimension loss.
-/

open HCPolySupport.HighContrast (CoeffSpace toFullBlockMat_eq_blockMatEntry)
namespace HCPolySupport.HighContrast.Analysis

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators Matrix.Norms.L2Operator

noncomputable section

/-- Each entry of a Hermitian block is bounded by its Schatten norm, for real index at least one. -/
theorem abs_blockMatEntry_le_absSchattenNorm {d : ℕ} (H : BlockMat d)
    (hH : (toFullBlockMat H).IsHermitian) {N : ℝ} (hN : 1 ≤ N)
    (α β : BlockCoord d) : |blockMatEntry H α β| ≤ absSchattenNorm N H :=
  (SchattenMemLp.abs_blockMatEntry_le_blockOpNorm H α β).trans
    (blockOpNorm_le_absSchattenNorm hH hN)

/-! ## The ordered expansion of a power of a finite sum -/

/-- **The noncommutative multinomial expansion.**  In any ring,
`(∑ i ∈ s, M i) ^ N = ∑_{f : Fin N → s} (M (f 0) * M (f 1) * ⋯ * M (f (N-1)))`, the factors
taken in the order of `Fin N`.

Commutativity is nowhere used: the right-hand side is an ordered `List.ofFn … |>.prod`, and the
induction step splits `Fin (N+1)` into its head and tail through `Fin.consEquiv`. -/
theorem pow_sum_eq_sum_prod_ofFn {R : Type*} [Ring R] {ι : Type*}
    (s : Finset ι) (M : ι → R) (N : ℕ) :
    (∑ i ∈ s, M i) ^ N
      = ∑ f : Fin N → {x // x ∈ s}, (List.ofFn fun k => M ((f k : ι))).prod := by
  classical
  induction N with
  | zero => simp
  | succ n ih =>
      have hsplit :
          ∑ f : Fin (n + 1) → {x // x ∈ s}, (List.ofFn fun k => M ((f k : ι))).prod
            = ∑ p : {x // x ∈ s} × (Fin n → {x // x ∈ s}),
                M ((p.1 : ι)) * (List.ofFn fun k => M ((p.2 k : ι))).prod := by
        refine (Fintype.sum_equiv (Fin.consEquiv (fun _ => {x // x ∈ s})) _ _ ?_).symm
        intro p
        change M ((p.1 : ι)) * (List.ofFn fun k => M ((p.2 k : ι))).prod
          = (List.ofFn fun k => M (((Fin.cons p.1 p.2 : Fin (n + 1) → {x // x ∈ s}) k : ι))).prod
        rw [List.ofFn_succ, List.prod_cons]
        simp
      rw [pow_succ', ih, hsplit, Fintype.sum_prod_type]
      rw [Finset.sum_coe_sort s M |>.symm, Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => (Finset.mul_sum _ _ _)

/-- The trace expansion for doubled blocks, in the `toFullBlockMat` picture. -/
theorem trace_pow_sum_toFullBlockMat {d : ℕ} {ι : Type*}
    (s : Finset ι) (Y : ι → BlockMat d) (N : ℕ) :
    Matrix.trace ((∑ i ∈ s, toFullBlockMat (Y i)) ^ N)
      = ∑ f : Fin N → {x // x ∈ s},
          Matrix.trace ((List.ofFn fun k => toFullBlockMat (Y ((f k : ι)))).prod) := by
  rw [pow_sum_eq_sum_prod_ofFn s (fun i => toFullBlockMat (Y i)) N, Matrix.trace_sum]

/-- Hölder membership for an ordered product in a normed ring; the exponent is the reciprocal sum.
-/
theorem memLp_list_prod {Ω E ι : Type*} [MeasurableSpace Ω] [NormedRing E]
    {μ : Measure Ω} [IsFiniteMeasure μ] {p : ℝ≥0∞}
    (l : List ι) (f : ι → Ω → E) (hf : ∀ i ∈ l, MemLp (f i) p μ) :
    MemLp (fun a => (l.map (fun i => f i a)).prod) ((l.length : ℝ≥0∞) * p⁻¹)⁻¹ μ := by
  induction l with
  | nil => simpa using (memLp_const (1 : E) : MemLp (fun _ : Ω => (1 : E)) ⊤ μ)
  | cons i l ih =>
    have hi := hf i (by simp)
    have ht := ih (fun j hj => hf j (by simp [hj]))
    have htriple : ENNReal.HolderTriple p (((l.length : ℝ≥0∞) * p⁻¹)⁻¹)
        ((((i :: l).length : ℝ≥0∞) * p⁻¹)⁻¹) := ⟨by simp [add_mul, add_comm]⟩
    simpa only [List.map_cons, List.prod_cons, List.length_cons, Nat.cast_add, Nat.cast_one]
      using (hi.fun_mul ht (hpqr := htriple))

/-- A Schatten moment controls the full matrix operator-norm moment. -/
theorem memLp_toFullBlockMat {d : ℕ} {P : Measure (CoeffSpace d)} {N : ℝ} {H : CoeffSpace d →
  BlockMat d}
    (hH : SchattenMemLp P N H) (hN : 1 ≤ N) :
    MemLp (fun a => toFullBlockMat (H a)) (ENNReal.ofReal N) P := by
  change MemLp (fun a α β => toFullBlockMat (H a) α β) (ENNReal.ofReal N) P
  refine memLp_pi_iff.mpr fun α => memLp_pi_iff.mpr fun β => ?_
  refine (hH.memLp_absSchattenNorm hN).mono'
    (by simpa only [toFullBlockMat_eq_blockMatEntry] using hH.measurable α β) ?_
  filter_upwards [hH.symmetric] with a ha
  rw [Real.norm_eq_abs, toFullBlockMat_eq_blockMatEntry]
  exact abs_blockMatEntry_le_absSchattenNorm (H a) ((toFullBlockMat_isHermitian_iff _).2 ha) hN α β

/-- Each entry of an ordered matrix product has the Hölder exponent for its length. -/
theorem memLp_prod_entry {d : ℕ} {ι : Type*} {P : Measure (CoeffSpace d)}
    [IsFiniteMeasure P] {N : ℝ} (hN : 1 ≤ N) (l : List ι)
    (Y : ι → CoeffSpace d → BlockMat d)
    (hY : ∀ i ∈ l, SchattenMemLp P N (Y i)) (α β : BlockCoord d) :
    MemLp (fun a => (l.map (fun i => toFullBlockMat (Y i a))).prod α β)
      ((l.length : ℝ≥0∞) * (ENNReal.ofReal N)⁻¹)⁻¹ P := by
  have hp := memLp_list_prod l (fun i a => toFullBlockMat (Y i a))
    (fun i hi => by
      have hm : AEStronglyMeasurable (fun a => toFullBlockMat (Y i a)) P := by
        change AEStronglyMeasurable (fun a α β => toFullBlockMat (Y i a) α β) P
        apply AEMeasurable.aestronglyMeasurable
        exact AEMeasurable.of_eval fun α => AEMeasurable.of_eval fun β =>
          by simpa only [toFullBlockMat_eq_blockMatEntry] using
            ((hY i hi).measurable α β).aemeasurable
      refine ((hY i hi).memLp_absSchattenNorm hN).mono' hm ?_
      filter_upwards [(hY i hi).symmetric] with a ha
      exact blockOpNorm_le_absSchattenNorm ((toFullBlockMat_isHermitian_iff _).2 ha) hN)
  have hm : AEMeasurable (fun a => (l.map (fun i => toFullBlockMat (Y i a))).prod α β) P := by
    let : ContinuousENorm (FullBlockMat d) := SeminormedAddGroup.toContinuousENorm
    exact (measurable_pi_apply β).comp_aemeasurable
      ((measurable_pi_apply α).comp_aemeasurable hp.aestronglyMeasurable.aemeasurable)
  refine hp.norm.mono' hm.aestronglyMeasurable (Filter.Eventually.of_forall fun a => ?_)
  simpa only [toFullBlockMat_ofFullBlockMat, blockMatEntry_ofFullBlockMat,
    blockOpNorm, Real.norm_eq_abs] using
    SchattenMemLp.abs_blockMatEntry_le_blockOpNorm
      (ofFullBlockMat (l.map (fun i => toFullBlockMat (Y i a))).prod) α β

/-- Products of at most N factors in L^N have integrable entries on a finite measure space. -/
theorem integrable_prod_entry {d : ℕ} {ι : Type*} {P : Measure (CoeffSpace d)}
    [IsFiniteMeasure P] {N : ℕ} (hN : 1 ≤ N) (l : List ι) (hlen : l.length ≤ N)
    (Y : ι → CoeffSpace d → BlockMat d)
    (hY : ∀ i ∈ l, SchattenMemLp P (N : ℝ) (Y i)) (α β : BlockCoord d) :
    Integrable (fun a => (l.map (fun i => toFullBlockMat (Y i a))).prod α β) P := by
  apply (memLp_prod_entry (by exact_mod_cast hN) l Y hY α β).integrable
  apply ENNReal.one_le_inv.mpr
  have hc : (l.length : ℝ≥0∞) ≤ (N : ℝ≥0∞) := by exact_mod_cast hlen
  simpa only [ENNReal.ofReal_natCast] using
    (mul_le_mul' hc (le_refl ((N : ℝ≥0∞)⁻¹))).trans (ENNReal.mul_inv_le_one _)

/-- Measurable factors give a measurable ordered product. -/
theorem measurable_list_prod {Ω ι M : Type*} [MeasurableSpace Ω] [Monoid M]
    [MeasurableSpace M] [MeasurableMul₂ M] (l : List ι) (f : ι → Ω → M)
    (hf : ∀ i ∈ l, Measurable (f i)) :
    Measurable (fun a => (l.map (fun i => f i a)).prod) := by
  simpa only [List.map_map, Function.comp_def] using
    (l.map f).measurable_fun_prod (by
      rintro _ h
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp h
      exact hf i hi)

/-- A grouped tuple of other indices, and every ordered product of it, is independent of one
index. -/
theorem indepFun_list_prod_of_notMem {Ω ι M : Type*} [MeasurableSpace Ω] [Monoid M]
    [MeasurableSpace M] [MeasurableMul₂ M] {μ : Measure Ω} {f : ι → Ω → M}
    (hindep : iIndepFun f μ) (hf : ∀ i, AEMeasurable (f i) μ)
    (i : ι) (l : List ι) (hi : i ∉ l) :
    IndepFun (f i) (fun a => (l.map (fun j => f j a)).prod) μ := by
  classical
  let S : Finset ι := {i}
  let T : Finset ι := l.toFinset
  have hdis : Disjoint S T := by simpa [S, T] using hi
  have hg := hindep.indepFun_finset₀ S T hdis hf
  let g : (T → M) → M := fun x =>
    (l.map (fun j => if hj : j ∈ T then x ⟨j, hj⟩ else 1)).prod
  have hgm : Measurable g := by
    apply measurable_list_prod
    intro j _
    by_cases hj : j ∈ T <;> simp only [hj, dite_true, dite_false]
    · exact measurable_pi_apply _
    · exact measurable_const
  have h := hg.comp (measurable_pi_apply (⟨i, by simp [S]⟩ : S)) hgm
  convert h using 1 <;> try rfl
  funext a
  apply congrArg List.prod
  apply List.map_congr_left
  intro j hj
  simp [T, List.mem_toFinset.mpr hj]

/-- Centering annihilates the expected trace after a singleton factor is moved to the front. -/
theorem integral_trace_mul_prod_eq_zero {d : ℕ} {ι : Type*}
    {P : Measure (CoeffSpace d)} [IsFiniteMeasure P] {N : ℕ} (hN : 1 ≤ N)
    (Y : ι → CoeffSpace d → BlockMat d) (hY : ∀ i, SchattenMemLp P (N : ℝ) (Y i))
    (hindep : iIndepFun (fun i a => toFullBlockMat (Y i a)) P)
    (i : ι) (l : List ι) (hlen : l.length ≤ N) (hi : i ∉ l)
    (hcent : ∀ α β, ∫ a, blockMatEntry (Y i a) α β ∂P = 0) :
    (∫ a, Matrix.trace (toFullBlockMat (Y i a) *
      (l.map (fun j => toFullBlockMat (Y j a))).prod) ∂P) = 0 := by
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hm := fun j => (memLp_toFullBlockMat (hY j) hNR).aestronglyMeasurable.aemeasurable
  have hind := indepFun_list_prod_of_notMem hindep hm i l hi
  have he (α β : BlockCoord d) : IndepFun
      (fun a => blockMatEntry (Y i a) α β)
      (fun a => (l.map (fun j => toFullBlockMat (Y j a))).prod β α) P := by
    exact hind.comp
      ((measurable_pi_apply β).comp (measurable_pi_apply α))
      ((measurable_pi_apply α).comp (measurable_pi_apply β))
  have hI (α β : BlockCoord d) : Integrable (fun a => blockMatEntry (Y i a) α β *
      (l.map (fun j => toFullBlockMat (Y j a))).prod β α) P :=
    (he α β).integrable_mul ((hY i).integrable_entry hNR α β)
      (integrable_prod_entry hN l hlen Y (fun j _ => hY j) β α)
  have hz (α β : BlockCoord d) : (∫ a, blockMatEntry (Y i a) α β *
      (l.map (fun j => toFullBlockMat (Y j a))).prod β α ∂P) = 0 := by
    have h := (he α β).integral_mul_eq_mul_integral
      ((hY i).measurable α β)
      (integrable_prod_entry hN l hlen Y (fun j _ => hY j) β α).1
    simpa only [Pi.mul_apply, hcent α β, zero_mul] using h
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, toFullBlockMat_eq_blockMatEntry]
  rw [integral_finsetSum _ (fun α _ => integrable_finsetSum _ (fun β _ => hI α β))]
  simp_rw [integral_finsetSum _ (fun β _ => hI _ β), hz]
  simp

/-- A word with an index occurring exactly once has zero expected trace, by grouped independence
and cyclicity. -/
theorem integral_trace_prod_eq_zero_of_count_eq_one {d : ℕ} {ι : Type*} [DecidableEq ι]
    {P : Measure (CoeffSpace d)} [IsFiniteMeasure P] {N : ℕ} (hN : 1 ≤ N)
    (Y : ι → CoeffSpace d → BlockMat d) (hY : ∀ i, SchattenMemLp P (N : ℝ) (Y i))
    (hindep : iIndepFun (fun i a => toFullBlockMat (Y i a)) P)
    (l : List ι) (hlen : l.length ≤ N) (i : ι) (hi : l.count i = 1)
    (hcent : ∀ α β, ∫ a, blockMatEntry (Y i a) α β ∂P = 0) :
    (∫ a, Matrix.trace (l.map (fun j => toFullBlockMat (Y j a))).prod ∂P) = 0 := by
  obtain ⟨l₁, l₂, rfl, hi₁⟩ := List.eq_append_cons_of_mem
    (List.count_pos_iff.mp (by omega : 0 < l.count i))
  have hi₂ : i ∉ l₂ := by
    rw [List.count_append, List.count_cons_self] at hi
    exact List.count_eq_zero.mp (by omega)
  have hz := integral_trace_mul_prod_eq_zero hN Y hY hindep i (l₂ ++ l₁)
    (by simp only [List.length_append, List.length_cons] at hlen ⊢; omega)
    (by simp [hi₁, hi₂]) hcent
  convert hz using 1
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro a
  simp only [List.map_append, List.map_cons, List.prod_append, List.prod_cons]
  rw [Matrix.trace_mul_comm, mul_assoc]

/-- The occurrence count in an ordered finite word equals the cardinality of its equality fiber. -/
theorem count_ofFn_eq_card_fiber {ι : Type*} [DecidableEq ι] {N : ℕ}
    (f : Fin N → ι) (i : ι) :
    (List.ofFn f).count i = (Finset.univ.filter (fun k => f k = i)).card := by
  have hsum : ∀ {n : ℕ} (g : Fin n → ι),
      (List.ofFn g).count i = ∑ k, if g k = i then 1 else 0 := by
    intro n
    induction n with
    | zero => intro g; simp
    | succ n ih =>
      intro g
      rw [List.ofFn_succ, List.count_cons, Fin.sum_univ_succ, ih]
      simp only [beq_iff_eq, add_comm]
  rw [hsum, Finset.card_eq_sum_ones, Finset.sum_filter]

/-- Hölder in probability for N nonnegative factors with finite N-th moments. -/
theorem integral_prod_le_prod_eLpNorm {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {N : ℕ} (hN : 0 < N) (f : Fin N → Ω → ℝ)
    (hmem : ∀ k, MemLp (f k) (ENNReal.ofReal (N : ℝ)) μ)
    (hnn : ∀ k, 0 ≤ᵐ[μ] f k) :
    (∫ a, ∏ k, f k a ∂μ) ≤ ∏ k, (eLpNorm (f k) (ENNReal.ofReal (N : ℝ)) μ).toReal := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hp0 : ENNReal.ofReal (N : ℝ) ≠ 0 := (ENNReal.ofReal_pos.mpr hNR).ne'
  have hw : ∑ _k : Fin N, (N : ℝ)⁻¹ = 1 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact mul_inv_cancel₀ hNR.ne'
  have h := ENNReal.lintegral_prod_norm_pow_le (Finset.univ : Finset (Fin N))
    (f := fun k a => ‖f k a‖ₑ ^ (N : ℝ))
    (fun k _ => (hmem k).aestronglyMeasurable.enorm.pow_const _)
    hw (fun _ _ => inv_nonneg.mpr hNR.le)
  have he (k : Fin N) :
      (∫⁻ a, ‖f k a‖ₑ ^ (N : ℝ) ∂μ) ^ ((N : ℝ)⁻¹) =
        eLpNorm (f k) (ENNReal.ofReal (N : ℝ)) μ := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 ENNReal.ofReal_ne_top
      (hmem k).aestronglyMeasurable, ENNReal.toReal_ofReal hNR.le, one_div]
  simp only [← ENNReal.rpow_mul, mul_inv_cancel₀ hNR.ne', ENNReal.rpow_one, he] at h
  have hr := ENNReal.toReal_mono (ENNReal.prod_ne_top (fun k _ => (hmem k).eLpNorm_ne_top)) h
  rw [ENNReal.toReal_prod] at hr
  have hprodmeas : AEStronglyMeasurable (fun a => ∏ k, f k a) μ :=
    (Finset.univ.aemeasurable_fun_prod (fun k _ => (hmem
      k).aestronglyMeasurable.aemeasurable)).aestronglyMeasurable
  have hprodnn : 0 ≤ᵐ[μ] fun a => ∏ k, f k a :=
    (ae_all_iff.mpr hnn).mono fun a ha => Finset.prod_nonneg (fun k _ => ha k)
  rw [integral_eq_lintegral_of_nonneg_ae hprodnn hprodmeas]
  convert hr using 1
  apply congrArg ENNReal.toReal
  apply lintegral_congr_ae
  filter_upwards [ae_all_iff.mpr hnn] with a ha
  rw [ENNReal.ofReal_prod_of_nonneg (fun k _ => ha k)]
  apply Finset.prod_congr rfl
  intro k _
  rw [← ofReal_norm, Real.norm_of_nonneg (ha k)]

/-- A fixed equality partition without singleton blocks contributes at most the N-th power of the
quadratic sum. -/
theorem sum_prod_eqPattern_le {κ β ι : Type*} [Fintype κ] [Fintype ι]
    [DecidableEq κ] [DecidableEq β] [DecidableEq ι]
    (q : κ → β) (hq : Function.Surjective q)
    (hb : ∀ b, 2 ≤ Fintype.card {k // q k = b})
    (u : ι → ℝ) (hu : ∀ i, 0 ≤ u i) :
    (∑ f ∈ Finset.univ.filter (fun f : κ → ι => ∀ k l, f k = f l ↔ q k = q l),
      ∏ k, u (f k)) ≤ ((∑ i, u i ^ 2) ^ ((1 : ℝ) / 2)) ^ Fintype.card κ := by
  classical
  let : Fintype β := Fintype.ofSurjective q hq
  let t := Finset.univ.filter (fun f : κ → ι => ∀ k l, f k = f l ↔ q k = q l)
  let r : β → κ := fun b => Classical.choose (hq b)
  have hr : ∀ b, q (r b) = b := fun b => Classical.choose_spec (hq b)
  let g : (κ → ι) → (β → ι) := fun f b => f (r b)
  let m : β → ℕ := fun b => Fintype.card {k // q k = b}
  let W : (β → ι) → ℝ := fun x => ∏ b, u (x b) ^ m b
  have hrec (f : κ → ι) (hf : f ∈ t) (k : κ) : f k = g f (q k) :=
    ((Finset.mem_filter.mp hf).2 k (r (q k))).2 (by rw [hr])
  have hginj : Set.InjOn g t := by
    intro f hf f' hf' heq
    funext k
    rw [hrec f hf k, hrec f' hf' k, heq]
  have hweight (f : κ → ι) (hf : f ∈ t) : (∏ k, u (f k)) = W (g f) := by
    calc
      (∏ k, u (f k)) = ∏ k, u (g f (q k)) := by
        apply Finset.prod_congr rfl
        intro k _
        rw [hrec f hf k]
      _ = W (g f) := by
        simpa only [Finset.prod_const, Finset.card_univ, W, m] using
          (Fintype.prod_fiberwise' q (fun b => u (g f b))).symm
  let σ : ℝ := (∑ i, u i ^ 2) ^ ((1 : ℝ) / 2)
  have hS : 0 ≤ ∑ i, u i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hblock (b : β) : (∑ i, u i ^ m b) ≤ σ ^ m b := by
    have hx (i : ι) : (u i ^ 2) ^ ((m b : ℝ) / 2) = u i ^ m b := by
      rw [← Real.rpow_natCast (u i) 2, ← Real.rpow_natCast (u i) (m b),
        ← Real.rpow_mul (hu i)]
      congr 1
      ring
    have hσ : σ ^ m b = (∑ i, u i ^ 2) ^ ((m b : ℝ) / 2) := by
      rw [← Real.rpow_natCast σ (m b), ← Real.rpow_mul hS]
      congr 1
      ring
    rw [hσ]
    simpa only [hx] using sum_rpow_le_rpow_sum Finset.univ (fun i => u i ^ 2)
      (fun i _ => sq_nonneg _) (show (1 : ℝ) ≤ (m b : ℝ) / 2 by
        have hmb : (2 : ℝ) ≤ (m b : ℝ) := by exact_mod_cast hb b
        linarith only [hmb])
  have htotal : ∑ b, m b = Fintype.card κ := by
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, m] using!
      (Fintype.sum_fiberwise q (fun _ => (1 : ℕ)))
  calc
    (∑ f ∈ t, ∏ k, u (f k)) = ∑ f ∈ t, W (g f) := Finset.sum_congr rfl hweight
    _ = ∑ x ∈ t.image g, W x := (Finset.sum_image hginj).symm
    _ ≤ ∑ x : β → ι, W x := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ _) (fun x _ _ => Finset.prod_nonneg (fun b _ => pow_nonneg (hu _) _))
    _ = ∏ b, ∑ i, u i ^ m b := (Fintype.prod_sum (fun b i => u i ^ m b)).symm
    _ ≤ ∏ b, σ ^ m b := Finset.prod_le_prod₀
      (fun b _ => Finset.sum_nonneg (fun i _ => pow_nonneg (hu _) _)) (fun b _ => hblock b)
    _ = σ ^ Fintype.card κ := by rw [Finset.prod_pow_eq_pow_sum, htotal]

/-- Each equality partition admits a representative map on its original index type. -/
theorem exists_equality_pattern {κ ι : Type*} (f : κ → ι) :
    ∃ q : κ → κ, ∀ k l, q k = q l ↔ f k = f l := by
  classical
  let q : κ → κ := fun k => Classical.choose (show ∃ j, f j = f k from ⟨k, rfl⟩)
  have hq : ∀ k, f (q k) = f k := fun k => Classical.choose_spec
    (show ∃ j, f j = f k from ⟨k, rfl⟩)
  refine ⟨q, fun k l => ⟨fun h => ?_, fun h => ?_⟩⟩
  · rw [← hq k, ← hq l, h]
  · simp only [q, h]

/-- There are at most N^N equality patterns; sum their singleton-free contributions. -/
theorem sum_prod_noSingleton_le {N : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u : ι → ℝ) (hu : ∀ i, 0 ≤ u i) :
    (∑ f ∈ Finset.univ.filter (fun f : Fin N → ι =>
      ∀ i, (Finset.univ.filter (fun k => f k = i)).card ≠ 1), ∏ k, u (f k)) ≤
      (N : ℝ) ^ N * ((∑ i, u i ^ 2) ^ ((1 : ℝ) / 2)) ^ N := by
  classical
  let t := Finset.univ.filter (fun f : Fin N → ι =>
    ∀ i, (Finset.univ.filter (fun k => f k = i)).card ≠ 1)
  let pat : (Fin N → ι) → (Fin N → Fin N) := fun f =>
    Classical.choose (exists_equality_pattern f)
  have hpat (f : Fin N → ι) : ∀ k l, pat f k = pat f l ↔ f k = f l :=
    Classical.choose_spec (exists_equality_pattern f)
  let σ : ℝ := (∑ i, u i ^ 2) ^ ((1 : ℝ) / 2)
  have hσ : 0 ≤ σ := Real.rpow_nonneg (Finset.sum_nonneg (fun i _ => sq_nonneg _)) _
  have hclass (q : Fin N → Fin N) :
      (∑ f ∈ t.filter (fun f => pat f = q), ∏ k, u (f k)) ≤ σ ^ N := by
    by_cases hempty : (t.filter (fun f => pat f = q)) = ∅
    · rw [hempty, Finset.sum_empty]
      exact pow_nonneg hσ _
    obtain ⟨f₀, hf₀⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
    have hf₀t : f₀ ∈ t := (Finset.mem_filter.mp hf₀).1
    have hf₀q : pat f₀ = q := (Finset.mem_filter.mp hf₀).2
    let B := Set.range q
    let q' : Fin N → B := fun k => ⟨q k, Set.mem_range_self k⟩
    have hq' : Function.Surjective q' := by
      rintro ⟨b, k, hk⟩
      exact ⟨k, Subtype.ext hk⟩
    have hb (b : B) : 2 ≤ Fintype.card {k // q' k = b} := by
      obtain ⟨k₀, hk₀⟩ := hq' b
      have heq : (Finset.univ.filter (fun k => q' k = b)) =
          Finset.univ.filter (fun k => f₀ k = f₀ k₀) := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rw [← hk₀]
        simp only [q', Subtype.mk.injEq]
        rw [← hf₀q]
        exact hpat f₀ k k₀
      have hne : (Finset.univ.filter (fun k => f₀ k = f₀ k₀)).card ≠ 1 :=
        (Finset.mem_filter.mp hf₀t).2 (f₀ k₀)
      have hpos : 0 < (Finset.univ.filter (fun k => f₀ k = f₀ k₀)).card :=
        Finset.card_pos.mpr ⟨k₀, by simp⟩
      rw [Fintype.card_subtype, heq]
      omega
    have hsub : t.filter (fun f => pat f = q) ⊆
        Finset.univ.filter (fun f : Fin N → ι => ∀ k l, f k = f l ↔ q' k = q' l) := by
      intro f hf
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun k l => ?_⟩
      have hfq : pat f = q := (Finset.mem_filter.mp hf).2
      simp only [q', Subtype.mk.injEq]
      rw [← hfq]
      exact (hpat f k l).symm
    calc
      _ ≤ ∑ f ∈ Finset.univ.filter (fun f : Fin N → ι =>
          ∀ k l, f k = f l ↔ q' k = q' l), ∏ k, u (f k) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          (fun f _ _ => Finset.prod_nonneg (fun k _ => hu _))
      _ ≤ σ ^ N := by
        convert sum_prod_eqPattern_le q' hq' hb u hu using 1
        · apply Finset.sum_congr
          · ext f
            simp
          · intro f _
            rfl
        · simp only [σ, Fintype.card_fin]
  calc
    (∑ f ∈ t, ∏ k, u (f k)) =
        ∑ q : Fin N → Fin N, ∑ f ∈ t.filter (fun f => pat f = q), ∏ k, u (f k) :=
      (Finset.sum_fiberwise t pat (fun f => ∏ k, u (f k))).symm
    _ ≤ ∑ _q : Fin N → Fin N, σ ^ N := Finset.sum_le_sum (fun q _ => hclass q)
    _ = (N : ℝ) ^ N * σ ^ N := by simp

/-- The trace of an N-fold ordered product is integrable. -/
theorem integrable_trace_prod {d N : ℕ} {P : Measure (CoeffSpace d)}
    [IsFiniteMeasure P] (hN : 1 ≤ N) (Y : Fin N → CoeffSpace d → BlockMat d)
    (hY : ∀ k, SchattenMemLp P (N : ℝ) (Y k)) :
    Integrable (fun a => Matrix.trace (List.ofFn (fun k => toFullBlockMat (Y k a))).prod) P := by
  simp only [Matrix.trace, Matrix.diag]
  apply integrable_finsetSum
  intro α _
  have h := integrable_prod_entry hN (List.ofFn (fun k : Fin N => k)) (by simp)
    Y (fun k _ => hY k) α α
  simpa only [List.map_ofFn] using! h

/-- Trace Hölder followed by Hölder in probability bounds each word. -/
theorem abs_integral_trace_prod_le_prod_lqSchattenNorm {d N : ℕ}
    {P : Measure (CoeffSpace d)} [IsFiniteMeasure P] (hN : 2 ≤ N)
    (Y : Fin N → CoeffSpace d → BlockMat d)
    (hY : ∀ k, SchattenMemLp P (N : ℝ) (Y k)) :
    |∫ a, Matrix.trace (List.ofFn (fun k => toFullBlockMat (Y k a))).prod ∂P| ≤
      ∏ k, lqSchattenNorm P (N : ℝ) (Y k) := by
  have hN1 : 1 ≤ N := by omega
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hmem := fun k => (hY k).memLp_absSchattenNorm hNR
  have hnn : ∀ k, 0 ≤ᵐ[P] fun a => absSchattenNorm (N : ℝ) (Y k a) := by
    intro k
    filter_upwards [(hY k).symmetric] with a ha
    exact absSchattenNorm_nonneg ((toFullBlockMat_isHermitian_iff _).2 ha) hNR
  have hprod : Integrable (fun a => ∏ k, absSchattenNorm (N : ℝ) (Y k a)) P := by
    have hp := MemLp.fun_prod (s := Finset.univ) (p := fun _ : Fin N => ENNReal.ofReal (N : ℝ))
      (fun k _ => hmem k)
    have hne : (N : ℝ≥0∞) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      ENNReal.ofReal_natCast, ENNReal.mul_inv_cancel hne (by simp), inv_one] at hp
    exact hp.integrable (by rfl)
  have hpt : (fun a => |Matrix.trace (List.ofFn (fun k => toFullBlockMat (Y k a))).prod|) ≤ᵐ[P]
      (fun a => ∏ k, absSchattenNorm (N : ℝ) (Y k a)) := by
    filter_upwards [ae_all_iff.mpr (fun k => (hY k).symmetric)] with a ha
    exact abs_trace_prod_le_prod_absSchattenNorm hN (fun k => Y k a)
      (fun k => (toFullBlockMat_isHermitian_iff _).2 (ha k))
  calc
    _ ≤ ∫ a, |Matrix.trace (List.ofFn (fun k => toFullBlockMat (Y k a))).prod| ∂P :=
      abs_integral_le_integral_abs
    _ ≤ ∫ a, ∏ k, absSchattenNorm (N : ℝ) (Y k a) ∂P :=
      integral_mono_ae (integrable_trace_prod hN1 Y hY).abs hprod hpt
    _ ≤ ∏ k, (eLpNorm (fun a => absSchattenNorm (N : ℝ) (Y k a))
        (ENNReal.ofReal (N : ℝ)) P).toReal :=
      integral_prod_le_prod_eLpNorm (by omega) _ hmem hnn
    _ = ∏ k, lqSchattenNorm P (N : ℝ) (Y k) := by
      apply Finset.prod_congr rfl
      intro k _
      exact ((hY k).lqSchattenNorm_eq_eLpNorm_toReal hNR).2.2.symm

/-- The even mixed moment is the expected trace power; membership rules out junk integrals. -/
theorem lqSchattenNorm_pow_eq_integral_trace {d N : ℕ} {P : Measure (CoeffSpace d)}
    (hN : 2 ≤ N) (hNeven : Even N) {H : CoeffSpace d → BlockMat d}
    (hH : SchattenMemLp P (N : ℝ) H) :
    lqSchattenNorm P (N : ℝ) H ^ N =
      ∫ a, Matrix.trace ((toFullBlockMat (H a)) ^ N) ∂P := by
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hnn : 0 ≤ᵐ[P] fun a => absSchattenNorm (N : ℝ) (H a) ^ (N : ℝ) := by
    filter_upwards [hH.symmetric] with a ha
    exact Real.rpow_nonneg (absSchattenNorm_nonneg ((toFullBlockMat_isHermitian_iff _).2 ha) hNR) _
  unfold lqSchattenNorm
  rw [← Real.rpow_natCast, ← Real.rpow_mul (integral_nonneg_of_ae hnn),
    inv_mul_cancel₀ hn, Real.rpow_one]
  apply integral_congr_ae
  filter_upwards [hH.symmetric] with a ha
  rw [trace_even_pow_eq_absSchattenNorm_pow ((toFullBlockMat_isHermitian_iff _).2 ha) hN hNeven,
    Real.rpow_natCast]

/-- The independent centered symmetric matrix sum bound with coefficient exactly N.
The proof also covers the empty finset: its word sum is empty since N is positive. -/
theorem lqSchattenNorm_finset_sum_le_of_iIndepFun {d : ℕ} {ι : Type*}
    (P : Measure (CoeffSpace d)) (hP : IsProbabilityMeasure P)
    {N : ℕ} (hN : 2 ≤ N) (hNeven : Even N)
    (s : Finset ι) (Y : ι → CoeffSpace d → BlockMat d)
    (hmem : ∀ i ∈ s, SchattenMemLp P (N : ℝ) (Y i))
    (hcent : ∀ i ∈ s,
      ofFullBlockMat (Matrix.of fun α β => ∫ a, blockMatEntry (Y i a) α β ∂P)
        = ofFullBlockMat (0 : FullBlockMat d))
    (hindep : ProbabilityTheory.iIndepFun
      (fun (i : {x // x ∈ s}) a => toFullBlockMat (Y (i : ι) a)) P) :
    lqSchattenNorm P (N : ℝ)
        (fun a => ofFullBlockMat (∑ i ∈ s, toFullBlockMat (Y i a))) ≤
      (N : ℝ) * (∑ i ∈ s, lqSchattenNorm P (N : ℝ) (Y i) ^ 2) ^ ((1 : ℝ) / 2) := by
  classical
  let := hP
  let : BEq s := instBEqOfDecidableEq
  have hN1 : 1 ≤ N := by omega
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  let X : s → CoeffSpace d → BlockMat d := fun i => Y i
  let u : s → ℝ := fun i => lqSchattenNorm P (N : ℝ) (X i)
  have hX : ∀ i, SchattenMemLp P (N : ℝ) (X i) := fun i => hmem i i.property
  have hu : ∀ i, 0 ≤ u i := fun i => ((hX i).lqSchattenNorm_eq_eLpNorm_toReal hNR).2.1
  have hc : ∀ i α β, ∫ a, blockMatEntry (X i a) α β ∂P = 0 := by
    intro i α β
    have h := congrArg (fun H => blockMatEntry H α β) (hcent i i.property)
    simpa only [blockMatEntry_ofFullBlockMat, Matrix.of_apply, Matrix.zero_apply] using h
  let W : (Fin N → s) → ℝ := fun f =>
    ∫ a, Matrix.trace (List.ofFn (fun k => toFullBlockMat (X (f k) a))).prod ∂P
  have hw (f : Fin N → s) : |W f| ≤ ∏ k, u (f k) :=
    abs_integral_trace_prod_le_prod_lqSchattenNorm hN (fun k => X (f k)) (fun k => hX (f k))
  let t := Finset.univ.filter (fun f : Fin N → s =>
    ∀ i, (Finset.univ.filter (fun k => f k = i)).card ≠ 1)
  have hzero (f : Fin N → s) (hf : f ∉ t) : W f = 0 := by
    have hn : ¬ ∀ i, (Finset.univ.filter (fun k => f k = i)).card ≠ 1 := by
      simpa only [t, Finset.mem_filter, Finset.mem_univ, true_and] using hf
    obtain ⟨i, hi⟩ := not_forall.mp hn
    have hi' : (List.ofFn f).count i = 1 := by
      rw [count_ofFn_eq_card_fiber]
      exact not_ne_iff.mp hi
    have h := integral_trace_prod_eq_zero_of_count_eq_one hN1 X hX hindep
      (List.ofFn f) (by simp) i hi' (hc i)
    simpa only [List.map_ofFn] using! h
  have hsum : SchattenMemLp P (N : ℝ)
      (fun a => ofFullBlockMat (∑ i ∈ s, toFullBlockMat (Y i a))) := by
    simpa using Source.memLqSchatten_finset_sum hNR s (fun _ => (1 : ℝ)) Y hmem
  have hexp : lqSchattenNorm P (N : ℝ)
      (fun a => ofFullBlockMat (∑ i ∈ s, toFullBlockMat (Y i a))) ^ N = ∑ f, W f := by
    rw [lqSchattenNorm_pow_eq_integral_trace hN hNeven hsum]
    simp only [toFullBlockMat_ofFullBlockMat, trace_pow_sum_toFullBlockMat]
    exact integral_finsetSum _ (fun f _ => integrable_trace_prod hN1
      (fun k => X (f k)) (fun k => hX (f k)))
  have hfilter : (∑ f, W f) = ∑ f ∈ t, W f :=
    (Finset.sum_subset (Finset.filter_subset _ _) (fun f _ hf => hzero f hf)).symm
  have hbound : (∑ f, W f) ≤ (N : ℝ) ^ N * ((∑ i : s, u i ^ 2) ^ ((1 : ℝ) / 2)) ^ N := by
    rw [hfilter]
    calc
      (∑ f ∈ t, W f) ≤ ∑ f ∈ t, ∏ k, u (f k) :=
        Finset.sum_le_sum (fun f _ => (le_abs_self _).trans (hw f))
      _ ≤ _ := sum_prod_noSingleton_le u hu
  have hpow : lqSchattenNorm P (N : ℝ)
      (fun a => ofFullBlockMat (∑ i ∈ s, toFullBlockMat (Y i a))) ^ N ≤
      ((N : ℝ) * (∑ i ∈ s, lqSchattenNorm P (N : ℝ) (Y i) ^ 2) ^ ((1 : ℝ) / 2)) ^ N := by
    rw [hexp, mul_pow]
    have hsumu : (∑ i : s, u i ^ 2) =
        ∑ i ∈ s, lqSchattenNorm P (N : ℝ) (Y i) ^ 2 :=
      Finset.sum_coe_sort s (fun i => lqSchattenNorm P (N : ℝ) (Y i) ^ 2)
    rwa [hsumu] at hbound
  exact le_of_pow_le_pow_left₀ (by omega)
    (mul_nonneg (by positivity) (Real.rpow_nonneg (Finset.sum_nonneg (fun i _ => sq_nonneg _))
      _)) hpow

end

end HCPolySupport.HighContrast.Analysis
