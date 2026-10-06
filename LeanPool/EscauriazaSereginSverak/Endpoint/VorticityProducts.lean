/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.EscauriazaSereginSverak.Endpoint.VorticityProductsSmooth
public import LeanPool.CaffarelliKohnNirenberg.Foundation.LocalSobolevCalculus
public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.VorticityL2Tools
public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.VorticityWeakLimit
public import LeanPool.CaffarelliKohnNirenberg.Foundation.LocalSobolevLeibniz
public import LeanPool.CaffarelliKohnNirenberg.Leray.Support.VorticityCutoff

/-!
# Products in the integer Sobolev spaces used for vorticity regularity

The whole-space estimates of `lem:vorticity-products` follow by completing
their smooth bilinear estimates in the Sobolev norm.
-/

public section

open Filter MeasureTheory Set Topology
open scoped ENNReal
open CKN CKN.Foundation.Parabolic


noncomputable section

namespace ESS

private theorem vorticityProducts_wordDeriv_translate
    (α : List (Fin 3)) (g : Vec3 → ℝ) (x₀ : Vec3) :
    wordDeriv α (fun x => g (x - x₀)) = fun x => wordDeriv α g (x - x₀) := by
  induction α generalizing g with
  | nil => rfl
  | cons j α ih =>
      change wordDeriv α (spatialDeriv (fun x => g (x - x₀)) j) = _
      rw [show spatialDeriv (fun x => g (x - x₀)) j =
        (fun x => spatialDeriv g j (x - x₀)) from
          funext fun x => vorticitySpatialDeriv_translate g x₀ x j]
      exact ih (spatialDeriv g j)

private theorem vorticityProducts_tsupport_wordDeriv_subset
    (α : List (Fin 3)) (g : Vec3 → ℝ) :
    tsupport (wordDeriv α g) ⊆ tsupport g := by
  induction α generalizing g with
  | nil => exact subset_rfl
  | cons j α ih =>
      exact (ih (spatialDeriv g j)).trans
        (tsupport_fderiv_apply_subset ℝ (basisVec j))

@[expose] def vorticityProducts_vectorSq (m : ℕ) (u : Fin 3 → Vec3 → ℝ) : ℝ :=
  ∑ i, sobolevNormSqOn m univ (fun α => wordDeriv α (u i))

private theorem vorticityProducts_memLp_word {f : Vec3 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f)
    (α : List (Fin 3)) : MemLp (wordDeriv α f) 2 volume := by
  exact (contDiff_wordDeriv hf α).continuous.memLp_of_hasCompactSupport (p := 2)
    (by
      induction α generalizing f with
      | nil => simpa only [wordDeriv] using hfc
      | cons j α ih =>
          simpa only [wordDeriv] using
            ih (contDiff_spatialDeriv_smooth hf j)
              (hfc.fderiv_apply (𝕜 := ℝ) (basisVec j)))

private theorem vorticityProducts_sobolevNormSq_tendsto
    {m : ℕ} {g : ℕ → Vec3 → ℝ} {D : List (Fin 3) → Vec3 → ℝ}
    (hg : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (g n))
    (hgc : ∀ n, HasCompactSupport (g n))
    (hD : ∀ α : List (Fin 3), α.length ≤ m → MemLp (D α) 2 volume)
    (hconv : ∀ α : List (Fin 3), α.length ≤ m →
      Tendsto (fun n => eLpNorm (wordDeriv α (g n) - D α) 2 volume) atTop (𝓝 0)) :
    Tendsto (fun n => sobolevNormSqOn m univ (fun α => wordDeriv α (g n))) atTop
      (𝓝 (sobolevNormSqOn m univ D)) := by
  simp only [sobolevNormSqOn, Measure.restrict_univ]
  apply tendsto_finsetSum (sobolevWords m)
  intro α hα
  exact vorticity_tendsto_integral_sq
    (fun n => vorticityProducts_memLp_word (hg n) (hgc n) α)
    (hD α (mem_sobolevWords.mp hα))
    (hconv α (mem_sobolevWords.mp hα))

private theorem vorticityProducts_l2_cauchy {f : ℕ → Vec3 → ℝ}
    {g : Vec3 → ℝ} (hf : ∀ n, MemLp (f n) 2 volume) (hg : MemLp g 2 volume)
    (hconv : Tendsto (fun n => eLpNorm (f n - g) 2 volume) atTop (𝓝 0)) :
    Tendsto (fun p : ℕ × ℕ => eLpNorm (f p.1 - f p.2) 2 volume) atTop (𝓝 0) := by
  let F : ℕ → Lp ℝ 2 volume := fun n => (hf n).toLp (f n)
  have hF : Tendsto F atTop (𝓝 (hg.toLp g)) :=
    (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f hf g hg).2 hconv
  have hc : CauchySeq F := hF.cauchySeq
  have hd : Tendsto (fun p : ℕ × ℕ => dist (F p.1) (F p.2)) atTop (𝓝 0) :=
    cauchySeq_iff_tendsto_dist_atTop_0.mp hc
  have hE : Tendsto
      (fun p : ℕ × ℕ => ENNReal.ofReal (dist (F p.1) (F p.2))) atTop (𝓝 0) := by
    simpa only [ENNReal.ofReal_zero] using ENNReal.tendsto_ofReal hd
  refine hE.congr fun p => ?_
  rw [Lp.dist_def]
  have hmem := (hf p.1).sub (hf p.2)
  have hnorm : eLpNorm (f p.1 - f p.2) 2 volume ≠ ⊤ := hmem.eLpNorm_ne_top
  have heq : eLpNorm ((F p.1) - (F p.2) : Vec3 → ℝ) 2 volume =
      eLpNorm (f p.1 - f p.2) 2 volume := by
    apply eLpNorm_congr_ae
    filter_upwards [(hf p.1).coeFn_toLp, (hf p.2).coeFn_toLp] with x hx hy
    simp only [F, Pi.sub_apply, hx, hy]
  rw [heq, ENNReal.ofReal_toReal hnorm]

private theorem vorticityProducts_wordDeriv_sub_at
    (α : List (Fin 3)) {f g : Vec3 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (x : Vec3) :
    wordDeriv α (fun y => f y - g y) x = wordDeriv α f x - wordDeriv α g x := by
  induction α generalizing f g with
  | nil => rfl
  | cons j α ih =>
      have hsub : spatialDeriv (fun y => f y - g y) j =
          fun y => spatialDeriv f j y - spatialDeriv g j y := by
        funext y
        have h := congrArg (fun L : Vec3 →L[ℝ] ℝ => L (basisVec j))
          (fderiv_fun_sub ((hf.differentiable (by simp)) y)
            ((hg.differentiable (by simp)) y))
        simpa [spatialDeriv] using h
      simp only [wordDeriv, hsub]
      exact ih (contDiff_spatialDeriv_smooth hf j)
        (contDiff_spatialDeriv_smooth hg j)

private theorem vorticityProducts_wordDeriv_sub
    (α : List (Fin 3)) {f g : Vec3 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    wordDeriv α (fun y => f y - g y) =
      fun x => wordDeriv α f x - wordDeriv α g x := by
  funext x
  exact vorticityProducts_wordDeriv_sub_at α hf hg x

private theorem vorticityProducts_sobolevNormSq_diff_tendsto
    {m : ℕ} {g : ℕ → Vec3 → ℝ} {D : List (Fin 3) → Vec3 → ℝ}
    (hg : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (g n))
    (hgc : ∀ n, HasCompactSupport (g n))
    (hD : ∀ α : List (Fin 3), α.length ≤ m → MemLp (D α) 2 volume)
    (hconv : ∀ α : List (Fin 3), α.length ≤ m →
      Tendsto (fun n => eLpNorm (wordDeriv α (g n) - D α) 2 volume)
        atTop (𝓝 0)) :
    Tendsto (fun p : ℕ × ℕ => sobolevNormSqOn m univ
      (fun α => wordDeriv α (fun x => g p.1 x - g p.2 x))) atTop (𝓝 0) := by
  have hzero : ∀ α : List (Fin 3), α.length ≤ m →
      Tendsto (fun p : ℕ × ℕ =>
        ∫ x, (wordDeriv α (g p.1) x - wordDeriv α (g p.2) x) ^ 2)
        atTop (𝓝 0) := by
    intro α hα
    let a : ℕ → Vec3 → ℝ := fun n => wordDeriv α (g n)
    have ha : ∀ n, MemLp (a n) 2 volume :=
      fun n => vorticityProducts_memLp_word (hg n) (hgc n) α
    have hc : Tendsto (fun p : ℕ × ℕ =>
        eLpNorm (a p.1 - a p.2) 2 volume) atTop (𝓝 0) :=
      vorticityProducts_l2_cauchy ha (hD α hα) (hconv α hα)
    have hd : ∀ p : ℕ × ℕ, MemLp (a p.1 - a p.2) 2 volume :=
      fun p => (ha p.1).sub (ha p.2)
    exact vorticity_integral_sq_tendsto_zero hd hc
  simp only [sobolevNormSqOn, Measure.restrict_univ]
  have hsum := tendsto_finsetSum (sobolevWords m) fun α hα => hzero α
    (mem_sobolevWords.mp hα)
  simpa only [Finset.sum_const_zero] using hsum.congr (fun p => by
    apply Finset.sum_congr rfl
    intro α _
    rw [vorticityProducts_wordDeriv_sub α (hg p.1) (hg p.2)])

private theorem vorticityProducts_sequence_limit
    {ι : Type*} [Fintype ι] {m : ℕ}
    {g : ℕ → ι → Vec3 → ℝ} {f : ι → Vec3 → ℝ}
    (hg : ∀ n i, ContDiff ℝ (⊤ : ℕ∞) (g n i))
    (hgc : ∀ n i, HasCompactSupport (g n i))
    (hcau : ∀ i (α : List (Fin 3)), α.length ≤ m →
      Tendsto (fun p : ℕ × ℕ =>
        eLpNorm (wordDeriv α (g p.1 i) - wordDeriv α (g p.2 i)) 2 volume)
        atTop (𝓝 0))
    (hzero : ∀ i, TendstoInMeasure volume (fun n => g n i) atTop (f i)) :
    ∃ D : ι → List (Fin 3) → Vec3 → ℝ,
      (∀ i, IsSobolevFamilyOn m univ (f i) (D i)) ∧
      (∀ i (α : List (Fin 3)), α.length ≤ m →
        Tendsto (fun n => eLpNorm (wordDeriv α (g n i) - D i α) 2 volume)
          atTop (𝓝 0)) ∧
      Tendsto (fun n => ∑ i, sobolevNormSqOn m univ
        (fun α => wordDeriv α (g n i))) atTop
          (𝓝 (∑ i, sobolevNormSqOn m univ (D i))) := by
  classical
  have hex (i : ι) (α : List (Fin 3)) (hα : α.length ≤ m) :
      ∃ d : Vec3 → ℝ, MemLp d 2 volume ∧
        Tendsto (fun n => eLpNorm (wordDeriv α (g n i) - d) 2 volume)
          atTop (𝓝 0) := by
    exact vorticityL2_exists_limit
      (fun n => vorticityProducts_memLp_word (hg n i) (hgc n i) α)
      (hcau i α hα)
  let D : ι → List (Fin 3) → Vec3 → ℝ :=
    fun i α => if h : α.length ≤ m then Classical.choose (hex i α h) else 0
  have hDmem (i : ι) (α : List (Fin 3)) (hα : α.length ≤ m) :
      MemLp (D i α) 2 volume := by
    dsimp [D]
    simp only [dite_eq_left hα]
    exact (Classical.choose_spec (hex i α hα)).1
  have hDconv (i : ι) (α : List (Fin 3)) (hα : α.length ≤ m) :
      Tendsto (fun n => eLpNorm (wordDeriv α (g n i) - D i α) 2 volume)
        atTop (𝓝 0) := by
    dsimp [D]
    simp only [dite_eq_left hα]
    exact (Classical.choose_spec (hex i α hα)).2
  have hDzero (i : ι) : D i [] =ᵐ[volume] f i := by
    have h0 : TendstoInMeasure volume (fun n => g n i) atTop (D i []) := by
      apply tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      simpa only [wordDeriv] using hDconv i [] (by simp)
    exact tendstoInMeasure_ae_unique h0 (hzero i)
  have hFam (i : ι) : IsSobolevFamilyOn m univ (f i) (D i) := by
    have h := IsSobolevFamilyOn.of_tendsto isOpen_univ
      (Dn := fun n α => wordDeriv α (g n i)) (D := D i)
      (fun n => by
        simpa only [wordDeriv] using
          (isSobolevFamilyOn_wordDeriv (m := m) isOpen_univ (hg n i)
            (fun α hα => by
              simpa only [Measure.restrict_univ] using
                vorticityProducts_memLp_word (hg n i) (hgc n i) α)))
      (fun α hα => by simpa only [Measure.restrict_univ] using hDmem i α hα)
      (fun α hα => by simpa only [Measure.restrict_univ] using hDconv i α hα)
    exact h.congr_ae (by simpa only [Measure.restrict_univ] using hDzero i)
      (fun _ _ => Filter.EventuallyEq.rfl)
  have hlim (i : ι) :
      Tendsto (fun n => sobolevNormSqOn m univ
        (fun α => wordDeriv α (g n i))) atTop
        (𝓝 (sobolevNormSqOn m univ (D i))) :=
    vorticityProducts_sobolevNormSq_tendsto
      (fun n => hg n i) (fun n => hgc n i) (hDmem i) (hDconv i)
  exact ⟨D, hFam, hDconv, tendsto_finsetSum _ (fun i _ => hlim i)⟩

private theorem vorticityProducts_product_tendstoInMeasure
    {u w : ℕ → Vec3 → ℝ} {U W : Vec3 → ℝ}
    (hu : ∀ n, MemLp (u n) 2 volume) (hw : ∀ n, MemLp (w n) 2 volume)
    (hU : MemLp U 2 volume) (hW : MemLp W 2 volume)
    (huconv : Tendsto (fun n => eLpNorm (u n - U) 2 volume) atTop (𝓝 0))
    (hwconv : Tendsto (fun n => eLpNorm (w n - W) 2 volume) atTop (𝓝 0)) :
    TendstoInMeasure volume (fun n x => u n x * w n x) atTop
      (fun x => U x * W x) := by
  have h22 : ENNReal.HolderTriple 2 2 1 := by
    constructor
    rw [ENNReal.inv_two_add_inv_two, inv_one]
  have hmul (f g : Vec3 → ℝ) (hf : AEStronglyMeasurable f volume)
      (hg : AEStronglyMeasurable g volume) :
      eLpNorm (fun x => f x * g x) 1 volume ≤
        eLpNorm f 2 volume * eLpNorm g 2 volume := by
    have h := eLpNorm_smul_le_mul_eLpNorm hf hg
      (p := 2) (q := 2) (r := 1)
    change eLpNorm (f * g) 1 volume ≤
      eLpNorm f 2 volume * eLpNorm g 2 volume
    simpa only [Pi.smul_apply', smul_eq_mul] using h
  have hwm (n : ℕ) :
      eLpNorm (w n) 2 volume ≤
        eLpNorm (w n - W) 2 volume + eLpNorm W 2 volume := by
    have heq : w n = (w n - W) + W := by
      funext x
      simp only [Pi.sub_apply, Pi.add_apply, sub_add_cancel]
    calc
      eLpNorm (w n) 2 volume = eLpNorm ((w n - W) + W) 2 volume :=
        congrArg (fun z : Vec3 → ℝ => eLpNorm z 2 volume) heq
      _ ≤ _ := eLpNorm_add_le (p := (2 : ℝ≥0∞)) (by norm_num)
  have hfinite : eLpNorm W 2 volume ≠ ⊤ := hW.eLpNorm_ne_top
  have hfirst : Tendsto (fun n => eLpNorm (u n - U) 2 volume *
      (eLpNorm (w n - W) 2 volume + eLpNorm W 2 volume)) atTop (𝓝 0) := by
    have hright : Tendsto (fun n =>
        eLpNorm (w n - W) 2 volume + eLpNorm W 2 volume) atTop
        (𝓝 (eLpNorm W 2 volume)) := by
      simpa only [zero_add] using hwconv.add tendsto_const_nhds
    simpa only [zero_mul] using ENNReal.Tendsto.mul huconv (Or.inr hfinite)
      hright (Or.inr ENNReal.zero_ne_top)
  have hsecond : Tendsto (fun n =>
      eLpNorm U 2 volume * eLpNorm (w n - W) 2 volume) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (ENNReal.Tendsto.const_mul hwconv (Or.inr hU.eLpNorm_ne_top))
  have hbound : ∀ n, eLpNorm
      ((fun x => u n x * w n x) - fun x => U x * W x) 1 volume ≤
      eLpNorm (u n - U) 2 volume *
          (eLpNorm (w n - W) 2 volume + eLpNorm W 2 volume) +
        eLpNorm U 2 volume * eLpNorm (w n - W) 2 volume := by
    intro n
    have heq : ((fun x => u n x * w n x) - fun x => U x * W x) =
        (fun x => (u n x - U x) * w n x) +
          (fun x => U x * (w n x - W x)) := by
      funext x
      simp only [Pi.sub_apply, Pi.add_apply]
      ring
    rw [heq]
    calc
      _ ≤ eLpNorm (fun x => (u n x - U x) * w n x) 1 volume +
          eLpNorm (fun x => U x * (w n x - W x)) 1 volume :=
        eLpNorm_add_le (by norm_num)
      _ ≤ eLpNorm (u n - U) 2 volume * eLpNorm (w n) 2 volume +
          eLpNorm U 2 volume * eLpNorm (w n - W) 2 volume := by
        gcongr
        · exact hmul _ _ ((hu n).aestronglyMeasurable.sub hU.aestronglyMeasurable)
            (hw n).aestronglyMeasurable
        · exact hmul _ _ hU.aestronglyMeasurable
            ((hw n).aestronglyMeasurable.sub hW.aestronglyMeasurable)
      _ ≤ _ := by gcongr; exact hwm n
  have hL1 : Tendsto (fun n => eLpNorm
      ((fun x => u n x * w n x) - fun x => U x * W x) 1 volume)
      atTop (𝓝 0) := by
    have htop : Tendsto (fun n =>
        eLpNorm (u n - U) 2 volume *
          (eLpNorm (w n - W) 2 volume + eLpNorm W 2 volume) +
        eLpNorm U 2 volume * eLpNorm (w n - W) 2 volume) atTop (𝓝 0) := by
      simpa only [add_zero] using hfirst.add hsecond
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds htop
      (fun _ => bot_le) hbound
  exact tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (1 : ℝ≥0∞) ≠ 0) hL1

private theorem vorticityProducts_vectorSq_tendsto
    {m : ℕ} {g : ℕ → Fin 3 → Vec3 → ℝ}
    {D : Fin 3 → List (Fin 3) → Vec3 → ℝ}
    (hg : ∀ n i, ContDiff ℝ (⊤ : ℕ∞) (g n i))
    (hgc : ∀ n i, HasCompactSupport (g n i))
    (hD : ∀ i (α : List (Fin 3)), α.length ≤ m → MemLp (D i α) 2 volume)
    (hconv : ∀ i (α : List (Fin 3)), α.length ≤ m →
      Tendsto (fun n => eLpNorm (wordDeriv α (g n i) - D i α) 2 volume)
        atTop (𝓝 0)) :
    Tendsto (fun n => ∑ i, sobolevNormSqOn m univ
      (fun α => wordDeriv α (g n i))) atTop
      (𝓝 (∑ i, sobolevNormSqOn m univ (D i))) :=
  tendsto_finsetSum _ fun i _ =>
    vorticityProducts_sobolevNormSq_tendsto
      (fun n => hg n i) (fun n => hgc n i) (hD i) (hconv i)

private theorem vorticityProducts_vectorSq_diff_tendsto
    {m : ℕ} {g : ℕ → Fin 3 → Vec3 → ℝ}
    {D : Fin 3 → List (Fin 3) → Vec3 → ℝ}
    (hg : ∀ n i, ContDiff ℝ (⊤ : ℕ∞) (g n i))
    (hgc : ∀ n i, HasCompactSupport (g n i))
    (hD : ∀ i (α : List (Fin 3)), α.length ≤ m → MemLp (D i α) 2 volume)
    (hconv : ∀ i (α : List (Fin 3)), α.length ≤ m →
      Tendsto (fun n => eLpNorm (wordDeriv α (g n i) - D i α) 2 volume)
        atTop (𝓝 0)) :
    Tendsto (fun p : ℕ × ℕ => ∑ i, sobolevNormSqOn m univ
      (fun α => wordDeriv α (fun x => g p.1 i x - g p.2 i x))) atTop (𝓝 0) := by
  have h := tendsto_finsetSum (Finset.univ : Finset (Fin 3)) fun i _ =>
    vorticityProducts_sobolevNormSq_diff_tendsto
      (fun n => hg n i) (fun n => hgc n i) (hD i) (hconv i)
  simpa only [Finset.sum_const_zero] using h

private theorem vorticityProducts_wordDeriv_add_at
    (α : List (Fin 3)) {f g : Vec3 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) (x : Vec3) :
    wordDeriv α (fun y => f y + g y) x = wordDeriv α f x + wordDeriv α g x := by
  induction α generalizing f g with
  | nil => rfl
  | cons j α ih =>
      have hadd : spatialDeriv (fun y => f y + g y) j =
          fun y => spatialDeriv f j y + spatialDeriv g j y := by
        funext y
        exact spatialDeriv_add ((hf.differentiable (by simp)) y)
          ((hg.differentiable (by simp)) y) j
      simp only [wordDeriv, hadd]
      exact ih (contDiff_spatialDeriv_smooth hf j)
        (contDiff_spatialDeriv_smooth hg j)

private theorem vorticityProducts_product_sub_at
    (α : List (Fin 3)) {a b c d : Vec3 → ℝ}
    (ha : ContDiff ℝ (⊤ : ℕ∞) a) (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (hc : ContDiff ℝ (⊤ : ℕ∞) c) (hd : ContDiff ℝ (⊤ : ℕ∞) d)
    (x : Vec3) :
    wordDeriv α (fun y => a y * b y) x -
        wordDeriv α (fun y => c y * d y) x =
      wordDeriv α (fun y => (a y - c y) * b y) x +
        wordDeriv α (fun y => c y * (b y - d y)) x := by
  have heq : (fun y => a y * b y - c y * d y) =
      (fun y => (a y - c y) * b y + c y * (b y - d y)) := by
    funext y
    ring
  have h1 := vorticityProducts_wordDeriv_sub_at α (ha.mul hb) (hc.mul hd) x
  have h2 := vorticityProducts_wordDeriv_add_at α (ha.sub hc |>.mul hb)
    (hc.mul (hb.sub hd)) x
  rw [heq] at h1
  exact h1.symm.trans h2

private theorem vorticityProducts_word_integral_le_tensorSq
    (m : ℕ) (α : List (Fin 3)) (hα : α.length ≤ m)
    (u w : Fin 3 → Vec3 → ℝ) (ij : Fin 3 × Fin 3) :
    (∫ x, wordDeriv α (fun y => u ij.1 y * w ij.2 y) x ^ 2) ≤
      ∑ pq : Fin 3 × Fin 3, sobolevNormSqOn m univ
        (fun β => wordDeriv β (fun y => u pq.1 y * w pq.2 y)) := by
  have hword : (∫ x, wordDeriv α (fun y => u ij.1 y * w ij.2 y) x ^ 2) ≤
      sobolevNormSqOn m univ
        (fun β => wordDeriv β (fun y => u ij.1 y * w ij.2 y)) := by
    simp only [sobolevNormSqOn, Measure.restrict_univ]
    exact Finset.single_le_sum
      (f := fun β : List (Fin 3) =>
        ∫ x, wordDeriv β (fun y => u ij.1 y * w ij.2 y) x ^ 2)
      (s := sobolevWords m)
      (fun β _ => integral_nonneg fun x => sq_nonneg _) (mem_sobolevWords.mpr hα)
  calc
    _ ≤ sobolevNormSqOn m univ
        (fun β => wordDeriv β (fun y => u ij.1 y * w ij.2 y)) := hword
    _ ≤ _ := by
      exact Finset.single_le_sum
        (f := fun pq : Fin 3 × Fin 3 => sobolevNormSqOn m univ
          (fun β => wordDeriv β (fun y => u pq.1 y * w pq.2 y)))
        (s := Finset.univ)
        (fun pq _ => by
          simp only [sobolevNormSqOn, Measure.restrict_univ]
          exact Finset.sum_nonneg fun β _ => integral_nonneg fun x => sq_nonneg _)
        (Finset.mem_univ ij)

private theorem vorticityProducts_memLp_product_word
    {u w : Vec3 → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (huc : HasCompactSupport u) (hw : ContDiff ℝ (⊤ : ℕ∞) w)
    (α : List (Fin 3)) :
    MemLp (wordDeriv α (fun x => u x * w x)) 2 volume := by
  exact vorticityProducts_memLp_word (hu.mul hw) huc.mul_right α

private theorem vorticityProducts_product_sub_left_at
    (α : List (Fin 3)) {a b c : Vec3 → ℝ}
    (ha : ContDiff ℝ (⊤ : ℕ∞) a) (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (hc : ContDiff ℝ (⊤ : ℕ∞) c) (x : Vec3) :
    wordDeriv α (fun y => a y * c y) x -
        wordDeriv α (fun y => b y * c y) x =
      wordDeriv α (fun y => (a y - b y) * c y) x := by
  have h := vorticityProducts_wordDeriv_sub_at α (ha.mul hc) (hb.mul hc) x
  have heq : (fun y => a y * c y - b y * c y) =
      (fun y => (a y - b y) * c y) := by
    funext y
    ring
  rw [heq] at h
  exact h.symm

private theorem vorticityProducts_product_sub_right_at
    (α : List (Fin 3)) {a b c : Vec3 → ℝ}
    (ha : ContDiff ℝ (⊤ : ℕ∞) a) (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (hc : ContDiff ℝ (⊤ : ℕ∞) c) (x : Vec3) :
    wordDeriv α (fun y => c y * a y) x -
        wordDeriv α (fun y => c y * b y) x =
      wordDeriv α (fun y => c y * (a y - b y)) x := by
  have h := vorticityProducts_wordDeriv_sub_at α (hc.mul ha) (hc.mul hb) x
  have heq : (fun y => c y * a y - c y * b y) =
      (fun y => c y * (a y - b y)) := by
    funext y
    ring
  rw [heq] at h
  exact h.symm

@[expose] def vorticityProducts_cauchyA (m : ℕ) (C : ℝ)
    (g : ℕ → Fin 3 → Vec3 → ℝ) (p : ℕ × ℕ) : ℝ :=
  C * (vorticityProducts_vectorSq 2 (fun i x => g p.1 i x - g p.2 i x) *
      vorticityProducts_vectorSq m (g p.1) +
    vorticityProducts_vectorSq m (fun i x => g p.1 i x - g p.2 i x) *
      vorticityProducts_vectorSq 2 (g p.1))

@[expose] def vorticityProducts_cauchyB (m : ℕ) (C : ℝ)
    (g : ℕ → Fin 3 → Vec3 → ℝ) (p : ℕ × ℕ) : ℝ :=
  C * (vorticityProducts_vectorSq 2 (g p.2) *
      vorticityProducts_vectorSq m (fun i x => g p.2 i x - g p.1 i x) +
    vorticityProducts_vectorSq m (g p.2) *
      vorticityProducts_vectorSq 2 (fun i x => g p.2 i x - g p.1 i x))

private theorem vorticityProducts_tensor_cauchy_integral_bound
    {m : ℕ} {g : ℕ → Fin 3 → Vec3 → ℝ} {C : ℝ}
    (hg : ∀ n i, ContDiff ℝ (⊤ : ℕ∞) (g n i))
    (hgc : ∀ n i, HasCompactSupport (g n i))
    (hBilin : ∀ u w : Fin 3 → Vec3 → ℝ,
      (∀ i, ContDiff ℝ (⊤ : ℕ∞) (u i)) →
      (∀ i, HasCompactSupport (u i)) →
      (∀ i, ContDiff ℝ (⊤ : ℕ∞) (w i)) →
      (∀ i, HasCompactSupport (w i)) →
      (∑ ij : Fin 3 × Fin 3, sobolevNormSqOn m univ
        (fun α => wordDeriv α (fun x => u ij.1 x * w ij.2 x))) ≤
        C * (vorticityProducts_vectorSq 2 u * vorticityProducts_vectorSq m w +
          vorticityProducts_vectorSq m u * vorticityProducts_vectorSq 2 w))
    (p : ℕ × ℕ) (ij : Fin 3 × Fin 3) (α : List (Fin 3)) (hα : α.length ≤ m) :
    (∫ x, (wordDeriv α (fun y => g p.1 ij.1 y * g p.1 ij.2 y) x -
      wordDeriv α (fun y => g p.2 ij.1 y * g p.2 ij.2 y) x) ^ 2) ≤
      2 * vorticityProducts_cauchyA m C g p +
        2 * vorticityProducts_cauchyB m C g p := by
  let F : Vec3 → ℝ := fun x =>
    wordDeriv α (fun y => g p.1 ij.1 y * g p.1 ij.2 y) x -
      wordDeriv α (fun y => g p.2 ij.1 y * g p.2 ij.2 y) x
  let A : ℕ × ℕ → ℝ := fun p => C *
    (vorticityProducts_vectorSq 2 (fun i x => g p.1 i x - g p.2 i x) *
        vorticityProducts_vectorSq m (g p.1) +
      vorticityProducts_vectorSq m (fun i x => g p.1 i x - g p.2 i x) *
        vorticityProducts_vectorSq 2 (g p.1))
  let B : ℕ × ℕ → ℝ := fun p => C *
    (vorticityProducts_vectorSq 2 (g p.2) *
        vorticityProducts_vectorSq m (fun i x => g p.2 i x - g p.1 i x) +
      vorticityProducts_vectorSq m (g p.2) *
        vorticityProducts_vectorSq 2 (fun i x => g p.2 i x - g p.1 i x))
  change (∫ x, F x ^ 2) ≤ 2 * A p + 2 * B p
  let P : Vec3 → ℝ := fun x =>
    wordDeriv α (fun y => g p.2 ij.1 y * g p.1 ij.2 y) x
  have hP : MemLp P 2 volume :=
    vorticityProducts_memLp_product_word (hg p.2 ij.1) (hgc p.2 ij.1)
      (hg p.1 ij.2) α
  have hbase := vorticity_integral_sq_sub_le
    (vorticityProducts_memLp_product_word (hg p.1 ij.1) (hgc p.1 ij.1)
      (hg p.1 ij.2) α)
    (vorticityProducts_memLp_product_word (hg p.2 ij.1) (hgc p.2 ij.1)
      (hg p.2 ij.2) α) hP
  have hleft : (∫ x, (wordDeriv α
      (fun y => g p.1 ij.1 y * g p.1 ij.2 y) x - P x) ^ 2) ≤ A p := by
    have heq : (∫ x, (wordDeriv α
        (fun y => g p.1 ij.1 y * g p.1 ij.2 y) x - P x) ^ 2) =
        ∫ x, wordDeriv α
          (fun y => (g p.1 ij.1 y - g p.2 ij.1 y) * g p.1 ij.2 y) x ^ 2 := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [vorticityProducts_product_sub_left_at α
        (hg p.1 ij.1) (hg p.2 ij.1) (hg p.1 ij.2) x]
    rw [heq]
    let d : Fin 3 → Vec3 → ℝ := fun i x => g p.1 i x - g p.2 i x
    calc
      _ ≤ ∑ pq : Fin 3 × Fin 3, sobolevNormSqOn m univ
          (fun β => wordDeriv β (fun x => d pq.1 x * g p.1 pq.2 x)) :=
        vorticityProducts_word_integral_le_tensorSq m α hα d (g p.1) ij
      _ ≤ A p := by
        change _ ≤ C * (vorticityProducts_vectorSq 2 d *
          vorticityProducts_vectorSq m (g p.1) +
            vorticityProducts_vectorSq m d * vorticityProducts_vectorSq 2 (g p.1))
        exact hBilin d (g p.1)
          (fun i => (hg p.1 i).sub (hg p.2 i))
          (fun i => (hgc p.1 i).sub (hgc p.2 i))
          (hg p.1) (hgc p.1)
  have hright : (∫ x, (wordDeriv α
      (fun y => g p.2 ij.1 y * g p.2 ij.2 y) x - P x) ^ 2) ≤ B p := by
    have heq : (∫ x, (wordDeriv α
        (fun y => g p.2 ij.1 y * g p.2 ij.2 y) x - P x) ^ 2) =
        ∫ x, wordDeriv α
          (fun y => g p.2 ij.1 y * (g p.2 ij.2 y - g p.1 ij.2 y)) x ^ 2 := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [vorticityProducts_product_sub_right_at α
        (hg p.2 ij.2) (hg p.1 ij.2) (hg p.2 ij.1) x]
    rw [heq]
    let d : Fin 3 → Vec3 → ℝ := fun i x => g p.2 i x - g p.1 i x
    calc
      _ ≤ ∑ pq : Fin 3 × Fin 3, sobolevNormSqOn m univ
          (fun β => wordDeriv β (fun x => g p.2 pq.1 x * d pq.2 x)) :=
        vorticityProducts_word_integral_le_tensorSq m α hα (g p.2) d ij
      _ ≤ B p := by
        change _ ≤ C * (vorticityProducts_vectorSq 2 (g p.2) *
          vorticityProducts_vectorSq m d +
            vorticityProducts_vectorSq m (g p.2) * vorticityProducts_vectorSq 2 d)
        exact hBilin (g p.2) d (hg p.2) (hgc p.2)
          (fun i => (hg p.2 i).sub (hg p.1 i))
          (fun i => (hgc p.2 i).sub (hgc p.1 i))
  change (∫ x, F x ^ 2) ≤ _ at hbase ⊢
  exact hbase.trans (by gcongr)

private theorem vorticityProducts_cauchyA_tendsto
    {m : ℕ} {g : ℕ → Fin 3 → Vec3 → ℝ} {C S₂ Sₘ : ℝ}
    (hS₂ : Tendsto (fun n => vorticityProducts_vectorSq 2 (g n)) atTop (𝓝 S₂))
    (hSₘ : Tendsto (fun n => vorticityProducts_vectorSq m (g n)) atTop (𝓝 Sₘ))
    (hD₂ : Tendsto (fun p : ℕ × ℕ => vorticityProducts_vectorSq 2
        (fun i x => g p.1 i x - g p.2 i x)) atTop (𝓝 0))
    (hDₘ : Tendsto (fun p : ℕ × ℕ => vorticityProducts_vectorSq m
        (fun i x => g p.1 i x - g p.2 i x)) atTop (𝓝 0)) :
    Tendsto (vorticityProducts_cauchyA m C g) atTop (𝓝 0) := by
  have hfst : Tendsto Prod.fst (atTop : Filter (ℕ × ℕ)) atTop := by
    simpa only [Filter.prod_atTop_atTop_eq] using
      (Filter.tendsto_fst (f := (atTop : Filter ℕ)) (g := (atTop : Filter ℕ)))
  have h := ((hD₂.mul (hSₘ.comp hfst)).add
    (hDₘ.mul (hS₂.comp hfst))).const_mul C
  unfold vorticityProducts_cauchyA
  simpa only [zero_mul, add_zero, mul_zero, Function.comp_apply] using h

private theorem vorticityProducts_cauchyB_tendsto
    {m : ℕ} {g : ℕ → Fin 3 → Vec3 → ℝ} {C S₂ Sₘ : ℝ}
    (hS₂ : Tendsto (fun n => vorticityProducts_vectorSq 2 (g n)) atTop (𝓝 S₂))
    (hSₘ : Tendsto (fun n => vorticityProducts_vectorSq m (g n)) atTop (𝓝 Sₘ))
    (hD₂ : Tendsto (fun p : ℕ × ℕ => vorticityProducts_vectorSq 2
        (fun i x => g p.1 i x - g p.2 i x)) atTop (𝓝 0))
    (hDₘ : Tendsto (fun p : ℕ × ℕ => vorticityProducts_vectorSq m
        (fun i x => g p.1 i x - g p.2 i x)) atTop (𝓝 0)) :
    Tendsto (vorticityProducts_cauchyB m C g) atTop (𝓝 0) := by
  have hsnd : Tendsto Prod.snd (atTop : Filter (ℕ × ℕ)) atTop := by
    simpa only [Filter.prod_atTop_atTop_eq] using
      (Filter.tendsto_snd (f := (atTop : Filter ℕ)) (g := (atTop : Filter ℕ)))
  have hswap : Tendsto Prod.swap (atTop : Filter (ℕ × ℕ)) atTop := by
    simpa only [Filter.prod_atTop_atTop_eq] using
      (Filter.tendsto_prod_swap (f := (atTop : Filter ℕ)) (g := (atTop : Filter ℕ)))
  have hD₂rev : Tendsto (fun p : ℕ × ℕ => vorticityProducts_vectorSq 2
      (fun i x => g p.2 i x - g p.1 i x)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Prod.swap, Prod.fst, Prod.snd] using
      hD₂.comp hswap
  have hDₘrev : Tendsto (fun p : ℕ × ℕ => vorticityProducts_vectorSq m
      (fun i x => g p.2 i x - g p.1 i x)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Prod.swap, Prod.fst, Prod.snd] using
      hDₘ.comp hswap
  have h := (((hS₂.comp hsnd).mul hDₘrev).add
    ((hSₘ.comp hsnd).mul hD₂rev)).const_mul C
  unfold vorticityProducts_cauchyB
  simpa only [mul_zero, add_zero, Function.comp_apply] using h

private theorem vorticityProducts_tensor_cauchy_rhs_tendsto
    {m : ℕ} {g : ℕ → Fin 3 → Vec3 → ℝ} {C S₂ Sₘ : ℝ}
    (hS₂ : Tendsto (fun n => vorticityProducts_vectorSq 2 (g n)) atTop (𝓝 S₂))
    (hSₘ : Tendsto (fun n => vorticityProducts_vectorSq m (g n)) atTop (𝓝 Sₘ))
    (hD₂ : Tendsto (fun p : ℕ × ℕ => vorticityProducts_vectorSq 2
        (fun i x => g p.1 i x - g p.2 i x)) atTop (𝓝 0))
    (hDₘ : Tendsto (fun p : ℕ × ℕ => vorticityProducts_vectorSq m
        (fun i x => g p.1 i x - g p.2 i x)) atTop (𝓝 0)) :
    Tendsto (fun p : ℕ × ℕ =>
      2 * vorticityProducts_cauchyA m C g p +
        2 * vorticityProducts_cauchyB m C g p) atTop (𝓝 0) := by
  have hA := vorticityProducts_cauchyA_tendsto (C := C) hS₂ hSₘ hD₂ hDₘ
  have hB := vorticityProducts_cauchyB_tendsto (C := C) hS₂ hSₘ hD₂ hDₘ
  simpa only [mul_zero, add_zero] using (hA.const_mul 2).add (hB.const_mul 2)

private theorem vorticityProducts_tensor_cauchy
    {m : ℕ} {g : ℕ → Fin 3 → Vec3 → ℝ} {C S₂ Sₘ : ℝ}
    (hg : ∀ n i, ContDiff ℝ (⊤ : ℕ∞) (g n i))
    (hgc : ∀ n i, HasCompactSupport (g n i))
    (hS₂ : Tendsto (fun n => vorticityProducts_vectorSq 2 (g n)) atTop (𝓝 S₂))
    (hSₘ : Tendsto (fun n => vorticityProducts_vectorSq m (g n)) atTop (𝓝 Sₘ))
    (hD₂ : Tendsto (fun p : ℕ × ℕ => vorticityProducts_vectorSq 2
        (fun i x => g p.1 i x - g p.2 i x)) atTop (𝓝 0))
    (hDₘ : Tendsto (fun p : ℕ × ℕ => vorticityProducts_vectorSq m
        (fun i x => g p.1 i x - g p.2 i x)) atTop (𝓝 0))
    (hBilin : ∀ u w : Fin 3 → Vec3 → ℝ,
      (∀ i, ContDiff ℝ (⊤ : ℕ∞) (u i)) →
      (∀ i, HasCompactSupport (u i)) →
      (∀ i, ContDiff ℝ (⊤ : ℕ∞) (w i)) →
      (∀ i, HasCompactSupport (w i)) →
      (∑ ij : Fin 3 × Fin 3, sobolevNormSqOn m univ
        (fun α => wordDeriv α (fun x => u ij.1 x * w ij.2 x))) ≤
        C * (vorticityProducts_vectorSq 2 u * vorticityProducts_vectorSq m w +
          vorticityProducts_vectorSq m u * vorticityProducts_vectorSq 2 w)) :
    ∀ ij : Fin 3 × Fin 3, ∀ α : List (Fin 3), α.length ≤ m →
      Tendsto (fun p : ℕ × ℕ => eLpNorm
        (wordDeriv α (fun x => g p.1 ij.1 x * g p.1 ij.2 x) -
          wordDeriv α (fun x => g p.2 ij.1 x * g p.2 ij.2 x)) 2 volume)
        atTop (𝓝 0) := by
  intro ij α hα
  let F : ℕ × ℕ → Vec3 → ℝ := fun p x =>
    wordDeriv α (fun y => g p.1 ij.1 y * g p.1 ij.2 y) x -
      wordDeriv α (fun y => g p.2 ij.1 y * g p.2 ij.2 y) x
  have hmem (p : ℕ × ℕ) : MemLp (F p) 2 volume :=
    (vorticityProducts_memLp_product_word (hg p.1 ij.1) (hgc p.1 ij.1)
      (hg p.1 ij.2) α).sub
      (vorticityProducts_memLp_product_word (hg p.2 ij.1) (hgc p.2 ij.1)
        (hg p.2 ij.2) α)
  have hbound (p : ℕ × ℕ) : (∫ x, F p x ^ 2) ≤
      2 * vorticityProducts_cauchyA m C g p +
        2 * vorticityProducts_cauchyB m C g p :=
    vorticityProducts_tensor_cauchy_integral_bound hg hgc hBilin p ij α hα
  have hlim : Tendsto (fun p : ℕ × ℕ => ∫ x, F p x ^ 2) atTop (𝓝 0) := by
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (vorticityProducts_tensor_cauchy_rhs_tendsto hS₂ hSₘ hD₂ hDₘ)
      (fun _ => integral_nonneg fun x => sq_nonneg _) hbound
  exact vorticity_tendsto_eLpNorm_of_integral_sq hmem hlim

private theorem vorticityProducts_tensorSquare_zero_tendsto
    {m : ℕ} (v : Vec3 → Vec3)
    (D : Fin 3 → List (Fin 3) → Vec3 → ℝ)
    (hD : ∀ i, IsSobolevFamilyOn m univ (vecComponents v i) (D i))
    (g : ℕ → Fin 3 → Vec3 → ℝ)
    (hg : ∀ n i, ContDiff ℝ (⊤ : ℕ∞) (g n i))
    (hgc : ∀ n i, HasCompactSupport (g n i))
    (hconv₀ : ∀ i, Tendsto (fun n => eLpNorm (g n i - D i []) 2 volume)
      atTop (𝓝 0)) (ij : Fin 3 × Fin 3) :
    TendstoInMeasure volume (fun n x => g n ij.1 x * g n ij.2 x) atTop
      (tensorSquareComponents v ij) := by
  have hmemD (i : Fin 3) : MemLp (D i []) 2 volume := by
    simpa only [Measure.restrict_univ] using (hD i).memL2 [] (by simp)
  have hbase := vorticityProducts_product_tendstoInMeasure
    (fun n => vorticityProducts_memLp_word (hg n ij.1) (hgc n ij.1) [])
    (fun n => vorticityProducts_memLp_word (hg n ij.2) (hgc n ij.2) [])
    (hmemD ij.1) (hmemD ij.2) (hconv₀ ij.1) (hconv₀ ij.2)
  have hae : (fun x => D ij.1 [] x * D ij.2 [] x) =ᵐ[volume]
      tensorSquareComponents v ij := by
    have h₁ : D ij.1 [] =ᵐ[volume] vecComponents v ij.1 := by
      simpa only [Measure.restrict_univ] using (hD ij.1).zero
    have h₂ : D ij.2 [] =ᵐ[volume] vecComponents v ij.2 := by
      simpa only [Measure.restrict_univ] using (hD ij.2).zero
    filter_upwards [h₁, h₂] with x hx hy
    simp only [tensorSquareComponents, vecComponents, hx, hy]
  exact TendstoInMeasure.congr (fun _ => Filter.EventuallyEq.rfl) hae hbase

private theorem vorticityProducts_tensorSquare_sequence_limit
    {m : ℕ} (v : Vec3 → Vec3)
    (D : Fin 3 → List (Fin 3) → Vec3 → ℝ)
    (hD : ∀ i, IsSobolevFamilyOn m univ (vecComponents v i) (D i))
    (g : ℕ → Fin 3 → Vec3 → ℝ)
    (hg : ∀ n i, ContDiff ℝ (⊤ : ℕ∞) (g n i))
    (hgc : ∀ n i, HasCompactSupport (g n i))
    (hconv₀ : ∀ i, Tendsto (fun n => eLpNorm (g n i - D i []) 2 volume)
      atTop (𝓝 0))
    (hcau : ∀ ij : Fin 3 × Fin 3, ∀ α : List (Fin 3), α.length ≤ m →
      Tendsto (fun p : ℕ × ℕ => eLpNorm
        (wordDeriv α (fun x => g p.1 ij.1 x * g p.1 ij.2 x) -
          wordDeriv α (fun x => g p.2 ij.1 x * g p.2 ij.2 x)) 2 volume)
        atTop (𝓝 0)) :
    ∃ E : Fin 3 × Fin 3 → List (Fin 3) → Vec3 → ℝ,
      (∀ ij, IsSobolevFamilyOn m univ (tensorSquareComponents v ij) (E ij)) ∧
      Tendsto (fun n => ∑ ij : Fin 3 × Fin 3, sobolevNormSqOn m univ
        (fun α => wordDeriv α (fun x => g n ij.1 x * g n ij.2 x))) atTop
        (𝓝 (∑ ij : Fin 3 × Fin 3, sobolevNormSqOn m univ (E ij))) := by
  let q : ℕ → Fin 3 × Fin 3 → Vec3 → ℝ :=
    fun n ij x => g n ij.1 x * g n ij.2 x
  have hq (n : ℕ) (ij : Fin 3 × Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (q n ij) :=
    (hg n ij.1).mul (hg n ij.2)
  have hqc (n : ℕ) (ij : Fin 3 × Fin 3) : HasCompactSupport (q n ij) :=
    (hgc n ij.1).mul_right
  have hcau' : ∀ ij : Fin 3 × Fin 3, ∀ α : List (Fin 3), α.length ≤ m →
      Tendsto (fun p : ℕ × ℕ => eLpNorm
        (wordDeriv α (q p.1 ij) - wordDeriv α (q p.2 ij)) 2 volume)
        atTop (𝓝 0) := hcau
  have hzero (ij : Fin 3 × Fin 3) :
      TendstoInMeasure volume (fun n => q n ij) atTop
        (tensorSquareComponents v ij) :=
    vorticityProducts_tensorSquare_zero_tendsto v D hD g hg hgc hconv₀ ij
  obtain ⟨E, hE, -, hEbound⟩ := vorticityProducts_sequence_limit
    (g := q)
    (f := tensorSquareComponents v)
    hq hqc hcau' hzero
  exact ⟨E, hE, hEbound⟩

private theorem vorticityProducts_sobolevNormSq_nonneg
    (m : ℕ) (D : List (Fin 3) → Vec3 → ℝ) :
    0 ≤ sobolevNormSqOn m univ D := by
  simp only [sobolevNormSqOn, Measure.restrict_univ]
  exact Finset.sum_nonneg fun α _ => integral_nonneg fun x => sq_nonneg _

private theorem vorticityProducts_vector_smooth_bound
    (C₀ : ℝ) (hC₀ : 0 ≤ C₀)
    (hEmbed : ∀ f : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) f →
      HasCompactSupport f → ∀ x,
        |f x| ≤ C₀ * Real.sqrt (sobolevNormSqOn 2 univ
          (fun α => wordDeriv α f)))
    (u : Fin 3 → Vec3 → ℝ)
    (hu : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (u i))
    (huc : ∀ i, HasCompactSupport (u i)) (x : Vec3) :
    Real.sqrt (∑ i, u i x ^ 2) ≤
      3 * C₀ * Real.sqrt (vorticityProducts_vectorSq 2 u) := by
  have hSnonneg : 0 ≤ vorticityProducts_vectorSq 2 u :=
    Finset.sum_nonneg fun i _ =>
      vorticityProducts_sobolevNormSq_nonneg 2 (fun α => wordDeriv α (u i))
  have hi (i : Fin 3) : |u i x| ≤ C₀ * Real.sqrt (vorticityProducts_vectorSq 2 u) := by
    have hSi : sobolevNormSqOn 2 univ (fun α => wordDeriv α (u i)) ≤
        vorticityProducts_vectorSq 2 u := by
      unfold vorticityProducts_vectorSq
      exact Finset.single_le_sum
        (fun j _ => vorticityProducts_sobolevNormSq_nonneg 2
          (fun α => wordDeriv α (u j))) (Finset.mem_univ i)
    exact (hEmbed (u i) (hu i) (huc i) x).trans
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hSi) hC₀)
  calc
    Real.sqrt (∑ i, u i x ^ 2) =
        vec3EuclideanNorm (fun i => u i x) := rfl
    _ ≤ ∑ i : Fin 3, |u i x| := vec3EuclideanNorm_le_sum_abs _
    _ ≤ ∑ _i : Fin 3, C₀ * Real.sqrt (vorticityProducts_vectorSq 2 u) :=
      Finset.sum_le_sum fun i _ => hi i
    _ = 3 * C₀ * Real.sqrt (vorticityProducts_vectorSq 2 u) := by
      rw [Fin.sum_univ_three]
      ring

private theorem vorticityProducts_H2_smooth_bilin :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u w : Fin 3 → Vec3 → ℝ,
      (∀ i, ContDiff ℝ (⊤ : ℕ∞) (u i)) →
      (∀ i, HasCompactSupport (u i)) →
      (∀ i, ContDiff ℝ (⊤ : ℕ∞) (w i)) →
      (∀ i, HasCompactSupport (w i)) →
      (∑ ij : Fin 3 × Fin 3, sobolevNormSqOn 2 univ
        (fun α => wordDeriv α (fun x => u ij.1 x * w ij.2 x))) ≤
        C * (vorticityProducts_vectorSq 2 u * vorticityProducts_vectorSq 2 w +
          vorticityProducts_vectorSq 2 u * vorticityProducts_vectorSq 2 w) := by
  obtain ⟨C₀, hC₀, hEmbed⟩ := abs_le_sobolevTwo_smooth
  obtain ⟨C₂, hC₂, hSmooth⟩ := vorticityProducts_H2_smooth
  refine ⟨9 * C₂ * C₀ ^ 2, by positivity, ?_⟩
  intro u w hu huc hw hwc
  have huBound := vorticityProducts_vector_smooth_bound C₀ hC₀ hEmbed u hu huc
  have hwBound := vorticityProducts_vector_smooth_bound C₀ hC₀ hEmbed w hw hwc
  have h := hSmooth u w
    (3 * C₀ * Real.sqrt (vorticityProducts_vectorSq 2 u))
    (3 * C₀ * Real.sqrt (vorticityProducts_vectorSq 2 w))
    hu huc hw hwc huBound hwBound
  have hSu : 0 ≤ vorticityProducts_vectorSq 2 u :=
    Finset.sum_nonneg fun i _ =>
      vorticityProducts_sobolevNormSq_nonneg 2 (fun α => wordDeriv α (u i))
  have hSw : 0 ≤ vorticityProducts_vectorSq 2 w :=
    Finset.sum_nonneg fun i _ =>
      vorticityProducts_sobolevNormSq_nonneg 2 (fun α => wordDeriv α (w i))
  rw [show (3 * C₀ * Real.sqrt (vorticityProducts_vectorSq 2 u)) ^ 2 =
      9 * C₀ ^ 2 * vorticityProducts_vectorSq 2 u by
        rw [mul_pow, mul_pow, Real.sq_sqrt hSu]; ring,
    show (3 * C₀ * Real.sqrt (vorticityProducts_vectorSq 2 w)) ^ 2 =
      9 * C₀ ^ 2 * vorticityProducts_vectorSq 2 w by
        rw [mul_pow, mul_pow, Real.sq_sqrt hSw]; ring] at h
  change _ ≤ C₂ * ((9 * C₀ ^ 2 * vorticityProducts_vectorSq 2 u) *
    vorticityProducts_vectorSq 2 w +
      (9 * C₀ ^ 2 * vorticityProducts_vectorSq 2 w) *
        vorticityProducts_vectorSq 2 u) at h
  calc
    _ ≤ _ := h
    _ = _ := by ring

private theorem vorticityProducts_H2_core
    (C₂ Cb : ℝ)
    (hSmooth : ∀ (u w : Fin 3 → Vec3 → ℝ) (Mu Mw : ℝ),
      (∀ i, ContDiff ℝ (⊤ : ℕ∞) (u i)) →
      (∀ i, HasCompactSupport (u i)) →
      (∀ i, ContDiff ℝ (⊤ : ℕ∞) (w i)) →
      (∀ i, HasCompactSupport (w i)) →
      (∀ x, Real.sqrt (∑ i, u i x ^ 2) ≤ Mu) →
      (∀ x, Real.sqrt (∑ i, w i x ^ 2) ≤ Mw) →
      (∑ ij : Fin 3 × Fin 3, sobolevNormSqOn 2 univ
        (fun α => wordDeriv α (fun x => u ij.1 x * w ij.2 x))) ≤
        C₂ * (Mu ^ 2 * vorticityProducts_vectorSq 2 w +
          Mw ^ 2 * vorticityProducts_vectorSq 2 u))
    (hBilin : ∀ u w : Fin 3 → Vec3 → ℝ,
      (∀ i, ContDiff ℝ (⊤ : ℕ∞) (u i)) →
      (∀ i, HasCompactSupport (u i)) →
      (∀ i, ContDiff ℝ (⊤ : ℕ∞) (w i)) →
      (∀ i, HasCompactSupport (w i)) →
      (∑ ij : Fin 3 × Fin 3, sobolevNormSqOn 2 univ
        (fun α => wordDeriv α (fun x => u ij.1 x * w ij.2 x))) ≤
        Cb * (vorticityProducts_vectorSq 2 u * vorticityProducts_vectorSq 2 w +
          vorticityProducts_vectorSq 2 u * vorticityProducts_vectorSq 2 w))
    (v : Vec3 → Vec3) (D : Fin 3 → List (Fin 3) → Vec3 → ℝ)
    (hD : ∀ i, IsSobolevFamilyOn 2 univ (vecComponents v i) (D i))
    (g : ℕ → Fin 3 → Vec3 → ℝ)
    (hg : ∀ n i, ContDiff ℝ (⊤ : ℕ∞) (g n i))
    (hgc : ∀ n i, HasCompactSupport (g n i))
    (hconv : ∀ i (α : List (Fin 3)), α.length ≤ 2 →
      Tendsto (fun n => eLpNorm (wordDeriv α (g n i) - D i α) 2 volume)
        atTop (𝓝 0))
    (M : ℝ) (hM : ∀ n x, Real.sqrt (∑ i, g n i x ^ 2) ≤ M) :
    ∃ E : Fin 3 × Fin 3 → List (Fin 3) → Vec3 → ℝ,
      (∀ ij, IsSobolevFamilyOn 2 univ (tensorSquareComponents v ij) (E ij)) ∧
      (∑ ij : Fin 3 × Fin 3, sobolevNormSqOn 2 univ (E ij)) ≤
        2 * C₂ * M ^ 2 * (∑ i, sobolevNormSqOn 2 univ (D i)) := by
  have hmemD (i : Fin 3) (α : List (Fin 3)) (hα : α.length ≤ 2) :
      MemLp (D i α) 2 volume := by
    simpa only [Measure.restrict_univ] using (hD i).memL2 α hα
  have hS := vorticityProducts_vectorSq_tendsto hg hgc hmemD hconv
  have hdiff := vorticityProducts_vectorSq_diff_tendsto hg hgc hmemD hconv
  have hcau := vorticityProducts_tensor_cauchy hg hgc hS hS hdiff hdiff hBilin
  obtain ⟨E, hE, hEbound⟩ :=
    vorticityProducts_tensorSquare_sequence_limit v D hD g hg hgc
      (fun i => by simpa only [wordDeriv] using hconv i [] (by simp)) hcau
  have hSmoothBound (n : ℕ) :
      ∑ ij : Fin 3 × Fin 3, sobolevNormSqOn 2 univ
        (fun α => wordDeriv α (fun x => g n ij.1 x * g n ij.2 x)) ≤
      2 * C₂ * M ^ 2 * vorticityProducts_vectorSq 2 (g n) := by
    have h := hSmooth (g n) (g n) M M (hg n) (hgc n) (hg n) (hgc n)
      (hM n) (hM n)
    calc
      _ ≤ C₂ * (M ^ 2 * vorticityProducts_vectorSq 2 (g n) +
        M ^ 2 * vorticityProducts_vectorSq 2 (g n)) := h
      _ = _ := by ring
  have hright := hS.const_mul (2 * C₂ * M ^ 2)
  have hbound : (∑ ij : Fin 3 × Fin 3, sobolevNormSqOn 2 univ (E ij)) ≤
      2 * C₂ * M ^ 2 * (∑ i, sobolevNormSqOn 2 univ (D i)) :=
    le_of_tendsto_of_tendsto' hEbound hright hSmoothBound
  exact ⟨E, hE, hbound⟩

/-- The order-two whole-space estimate in `lem:vorticity-products`, conditional
on smooth compactly supported density for the local Sobolev families. -/
theorem vorticityProducts_H2
    (hApprox : ∀ {ι : Type} [Fintype ι] {m : ℕ} {f : ι → Vec3 → ℝ}
      {D : ι → List (Fin 3) → Vec3 → ℝ},
      (∀ i, IsSobolevFamilyOn m univ (f i) (D i)) →
      ∃ g : ℕ → ι → Vec3 → ℝ,
        (∀ n i, ContDiff ℝ (⊤ : ℕ∞) (g n i)) ∧
        (∀ n i, HasCompactSupport (g n i)) ∧
        (∀ i (α : List (Fin 3)), α.length ≤ m →
          Tendsto (fun n => eLpNorm (wordDeriv α (g n i) - D i α) 2 volume)
            atTop (𝓝 0)) ∧
        ∀ M : ℝ, (∀ᵐ x ∂volume, Real.sqrt (∑ i, f i x ^ 2) ≤ M) →
          ∀ n x, Real.sqrt (∑ i, g n i x ^ 2) ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : Vec3 → Vec3, HasCompactSupport v →
      hNormOn 2 univ (vecComponents v) < ⊤ →
      eLpNorm (fun x => vec3EuclideanNorm (v x)) ⊤ volume < ⊤ →
      hNormOn 2 univ (tensorSquareComponents v) ≤
        ENNReal.ofReal C * eLpNorm (fun x => vec3EuclideanNorm (v x)) ⊤ volume *
          hNormOn 2 univ (vecComponents v) := by
  classical
  obtain ⟨C₂, hC₂, hSmooth⟩ := vorticityProducts_H2_smooth
  obtain ⟨Cb, hCb, hBilin⟩ := vorticityProducts_H2_smooth_bilin
  refine ⟨Real.sqrt (2 * C₂), Real.sqrt_nonneg _, ?_⟩
  intro v _ hv hMtop
  have hmem2 := hNormOn_lt_top_iff.mp hv
  choose D hD using hmem2
  obtain ⟨g, hg, hgc, hconv, hgbound⟩ :=
    hApprox (ι := Fin 3) (m := 2) (f := vecComponents v) (D := D) hD
  let M : ℝ := (eLpNorm (fun x => vec3EuclideanNorm (v x)) ⊤ volume).toReal
  have hMnonneg : 0 ≤ M := ENNReal.toReal_nonneg
  have hMbound : ∀ᵐ x ∂volume, Real.sqrt (∑ i, vecComponents v i x ^ 2) ≤ M := by
    have hess := ae_le_eLpNormEssSup
      (f := fun x => vec3EuclideanNorm (v x)) (μ := volume)
    filter_upwards [hess] with x hx
    have hle : ENNReal.ofReal (vec3EuclideanNorm (v x)) ≤
        eLpNorm (fun y => vec3EuclideanNorm (v y)) ⊤ volume := by
      have hx' : ENNReal.ofReal (vec3EuclideanNorm (v x)) ≤
          eLpNormEssSup (fun y => vec3EuclideanNorm (v y)) volume := by
        simpa only [Real.enorm_eq_ofReal_abs,
          abs_of_nonneg (vec3EuclideanNorm_nonneg _)] using hx
      exact hx'.trans eLpNormEssSup_le_eLpNorm_top
    have hr := ENNReal.toReal_mono hMtop.ne hle
    have hr' : vec3EuclideanNorm (v x) ≤ M := by
      simpa only [ENNReal.toReal_ofReal (vec3EuclideanNorm_nonneg _)] using hr
    exact hr'
  have hM := hgbound M hMbound
  have hSmooth' : ∀ (u w : Fin 3 → Vec3 → ℝ) (Mu Mw : ℝ),
      (∀ i, ContDiff ℝ (⊤ : ℕ∞) (u i)) →
      (∀ i, HasCompactSupport (u i)) →
      (∀ i, ContDiff ℝ (⊤ : ℕ∞) (w i)) →
      (∀ i, HasCompactSupport (w i)) →
      (∀ x, Real.sqrt (∑ i, u i x ^ 2) ≤ Mu) →
      (∀ x, Real.sqrt (∑ i, w i x ^ 2) ≤ Mw) →
      (∑ ij : Fin 3 × Fin 3, sobolevNormSqOn 2 univ
        (fun α => wordDeriv α (fun x => u ij.1 x * w ij.2 x))) ≤
        C₂ * (Mu ^ 2 * vorticityProducts_vectorSq 2 w +
          Mw ^ 2 * vorticityProducts_vectorSq 2 u) := by
    intro u w Mu Mw hu huc hw hwc hMu hMw
    exact hSmooth u w Mu Mw hu huc hw hwc hMu hMw
  obtain ⟨E, hE, hbound⟩ := vorticityProducts_H2_core C₂ Cb hSmooth' hBilin
    v D hD g hg hgc hconv M hM
  have hnormD := hNormOn_eq isOpen_univ hD
  have hnormE := hNormOn_eq isOpen_univ hE
  rw [hnormD, hnormE]
  have hSnonneg : 0 ≤ ∑ i, sobolevNormSqOn 2 univ (D i) :=
    Finset.sum_nonneg fun i _ => vorticityProducts_sobolevNormSq_nonneg 2 (D i)
  have hK : 0 ≤ 2 * C₂ := by positivity
  have hroot := Real.sqrt_le_sqrt hbound
  rw [show 2 * C₂ * M ^ 2 * (∑ i, sobolevNormSqOn 2 univ (D i)) =
    (2 * C₂) * (M ^ 2 * (∑ i, sobolevNormSqOn 2 univ (D i))) by ring,
    Real.sqrt_mul hK, Real.sqrt_mul (sq_nonneg M),
    Real.sqrt_sq_eq_abs, abs_of_nonneg hMnonneg] at hroot
  calc
    ENNReal.ofReal (Real.sqrt (∑ ij, sobolevNormSqOn 2 univ (E ij))) ≤
        ENNReal.ofReal (Real.sqrt (2 * C₂) *
          (M * Real.sqrt (∑ i, sobolevNormSqOn 2 univ (D i)))) :=
      ENNReal.ofReal_le_ofReal hroot
    _ = _ := by
      rw [ENNReal.ofReal_mul (Real.sqrt_nonneg _),
        ENNReal.ofReal_mul hMnonneg,
        ENNReal.ofReal_toReal hMtop.ne]
      ring

private theorem vorticityProducts_H3_core
    (C₃ : ℝ)
    (hBilin : ∀ u w : Fin 3 → Vec3 → ℝ,
      (∀ i, ContDiff ℝ (⊤ : ℕ∞) (u i)) →
      (∀ i, HasCompactSupport (u i)) →
      (∀ i, ContDiff ℝ (⊤ : ℕ∞) (w i)) →
      (∀ i, HasCompactSupport (w i)) →
      (∑ ij : Fin 3 × Fin 3, sobolevNormSqOn 3 univ
        (fun α => wordDeriv α (fun x => u ij.1 x * w ij.2 x))) ≤
        C₃ * (vorticityProducts_vectorSq 2 u * vorticityProducts_vectorSq 3 w +
          vorticityProducts_vectorSq 3 u * vorticityProducts_vectorSq 2 w))
    (v : Vec3 → Vec3) (D : Fin 3 → List (Fin 3) → Vec3 → ℝ)
    (hD : ∀ i, IsSobolevFamilyOn 3 univ (vecComponents v i) (D i))
    (g : ℕ → Fin 3 → Vec3 → ℝ)
    (hg : ∀ n i, ContDiff ℝ (⊤ : ℕ∞) (g n i))
    (hgc : ∀ n i, HasCompactSupport (g n i))
    (hconv : ∀ i (α : List (Fin 3)), α.length ≤ 3 →
      Tendsto (fun n => eLpNorm (wordDeriv α (g n i) - D i α) 2 volume)
        atTop (𝓝 0)) :
    ∃ E : Fin 3 × Fin 3 → List (Fin 3) → Vec3 → ℝ,
      (∀ ij, IsSobolevFamilyOn 3 univ (tensorSquareComponents v ij) (E ij)) ∧
      (∑ ij : Fin 3 × Fin 3, sobolevNormSqOn 3 univ (E ij)) ≤
        2 * C₃ * ((∑ i, sobolevNormSqOn 2 univ (D i)) *
          (∑ i, sobolevNormSqOn 3 univ (D i))) := by
  have hconv₂ (i : Fin 3) (α : List (Fin 3)) (hα : α.length ≤ 2) :=
    hconv i α (by omega : α.length ≤ 3)
  have hmemD₃ (i : Fin 3) (α : List (Fin 3)) (hα : α.length ≤ 3) :
      MemLp (D i α) 2 volume := by
    simpa only [Measure.restrict_univ] using (hD i).memL2 α hα
  have hmemD₂ (i : Fin 3) (α : List (Fin 3)) (hα : α.length ≤ 2) :
      MemLp (D i α) 2 volume := hmemD₃ i α (by omega)
  have hS₂ := vorticityProducts_vectorSq_tendsto hg hgc hmemD₂ hconv₂
  have hS₃ := vorticityProducts_vectorSq_tendsto hg hgc hmemD₃ hconv
  have hdiff₂ := vorticityProducts_vectorSq_diff_tendsto hg hgc hmemD₂ hconv₂
  have hdiff₃ := vorticityProducts_vectorSq_diff_tendsto hg hgc hmemD₃ hconv
  have hcau := vorticityProducts_tensor_cauchy hg hgc hS₂ hS₃
    hdiff₂ hdiff₃ hBilin
  obtain ⟨E, hE, hEbound⟩ :=
    vorticityProducts_tensorSquare_sequence_limit v D hD g hg hgc
      (fun i => by simpa only [wordDeriv] using hconv i [] (by simp)) hcau
  have hSmoothBound (n : ℕ) :
      ∑ ij : Fin 3 × Fin 3, sobolevNormSqOn 3 univ
        (fun α => wordDeriv α (fun x => g n ij.1 x * g n ij.2 x)) ≤
      2 * C₃ * (vorticityProducts_vectorSq 2 (g n) *
        vorticityProducts_vectorSq 3 (g n)) := by
    have h := hBilin (g n) (g n) (hg n) (hgc n) (hg n) (hgc n)
    calc
      _ ≤ C₃ * (vorticityProducts_vectorSq 2 (g n) *
            vorticityProducts_vectorSq 3 (g n) +
          vorticityProducts_vectorSq 3 (g n) *
            vorticityProducts_vectorSq 2 (g n)) := h
      _ = _ := by ring
  have hlimBound : (∑ ij : Fin 3 × Fin 3, sobolevNormSqOn 3 univ (E ij)) ≤
      2 * C₃ * ((∑ i, sobolevNormSqOn 2 univ (D i)) *
        (∑ i, sobolevNormSqOn 3 univ (D i))) := by
    have hright := (hS₂.mul hS₃).const_mul (2 * C₃)
    exact le_of_tendsto_of_tendsto' hEbound hright hSmoothBound
  exact ⟨E, hE, hlimBound⟩

/-- The order-three whole-space estimate in `lem:vorticity-products`, conditional
on smooth compactly supported density for the local Sobolev families. -/
theorem vorticityProducts_H3
    (hApprox : ∀ {ι : Type} [Fintype ι] {m : ℕ} {f : ι → Vec3 → ℝ}
      {D : ι → List (Fin 3) → Vec3 → ℝ},
      (∀ i, IsSobolevFamilyOn m univ (f i) (D i)) →
      ∃ g : ℕ → ι → Vec3 → ℝ,
        (∀ n i, ContDiff ℝ (⊤ : ℕ∞) (g n i)) ∧
        (∀ n i, HasCompactSupport (g n i)) ∧
        (∀ i (α : List (Fin 3)), α.length ≤ m →
          Tendsto (fun n => eLpNorm (wordDeriv α (g n i) - D i α) 2 volume)
            atTop (𝓝 0)) ∧
        ∀ M : ℝ, (∀ᵐ x ∂volume, Real.sqrt (∑ i, f i x ^ 2) ≤ M) →
          ∀ n x, Real.sqrt (∑ i, g n i x ^ 2) ≤ M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v : Vec3 → Vec3,
      hNormOn 3 univ (vecComponents v) < ⊤ →
      hNormOn 3 univ (tensorSquareComponents v) ≤
        ENNReal.ofReal C * hNormOn 2 univ (vecComponents v) *
          hNormOn 3 univ (vecComponents v) := by
  classical
  obtain ⟨C₃, hC₃, hSmooth⟩ := vorticityProducts_H3_smooth
  refine ⟨Real.sqrt (2 * C₃), Real.sqrt_nonneg _, ?_⟩
  intro v hv
  have hmem3 := hNormOn_lt_top_iff.mp hv
  choose D hD using hmem3
  have hD₂ (i : Fin 3) : IsSobolevFamilyOn 2 univ (vecComponents v i) (D i) :=
    (hD i).of_le (by omega)
  obtain ⟨g, hg, hgc, hconv, -⟩ :=
    hApprox (ι := Fin 3) (m := 3) (f := vecComponents v) (D := D) hD
  have hBilin : ∀ u w : Fin 3 → Vec3 → ℝ,
      (∀ i, ContDiff ℝ (⊤ : ℕ∞) (u i)) →
      (∀ i, HasCompactSupport (u i)) →
      (∀ i, ContDiff ℝ (⊤ : ℕ∞) (w i)) →
      (∀ i, HasCompactSupport (w i)) →
      (∑ ij : Fin 3 × Fin 3, sobolevNormSqOn 3 univ
        (fun α => wordDeriv α (fun x => u ij.1 x * w ij.2 x))) ≤
        C₃ * (vorticityProducts_vectorSq 2 u * vorticityProducts_vectorSq 3 w +
          vorticityProducts_vectorSq 3 u * vorticityProducts_vectorSq 2 w) := by
    intro u w hu huc hw hwc
    exact hSmooth u w hu huc hw hwc
  obtain ⟨E, hE, hlimBound⟩ :=
    vorticityProducts_H3_core C₃ hBilin v D hD g hg hgc hconv
  have h2norm := hNormOn_eq isOpen_univ hD₂
  have h3norm := hNormOn_eq isOpen_univ hD
  have hprodNorm := hNormOn_eq isOpen_univ hE
  rw [hprodNorm, h2norm, h3norm]
  have hS₂nonneg : 0 ≤ ∑ i, sobolevNormSqOn 2 univ (D i) := by
    apply Finset.sum_nonneg
    intro i _
    exact Finset.sum_nonneg fun α _ => integral_nonneg fun x => sq_nonneg _
  have hS₃nonneg : 0 ≤ ∑ i, sobolevNormSqOn 3 univ (D i) := by
    apply Finset.sum_nonneg
    intro i _
    exact Finset.sum_nonneg fun α _ => integral_nonneg fun x => sq_nonneg _
  have hK : 0 ≤ 2 * C₃ := by positivity
  have hroot := Real.sqrt_le_sqrt hlimBound
  rw [Real.sqrt_mul hK, Real.sqrt_mul hS₂nonneg] at hroot
  calc
    ENNReal.ofReal (Real.sqrt (∑ ij, sobolevNormSqOn 3 univ (E ij))) ≤
        ENNReal.ofReal (Real.sqrt (2 * C₃) *
          (Real.sqrt (∑ i, sobolevNormSqOn 2 univ (D i)) *
            Real.sqrt (∑ i, sobolevNormSqOn 3 univ (D i)))) :=
      ENNReal.ofReal_le_ofReal hroot
    _ = _ := by
      rw [ENNReal.ofReal_mul (Real.sqrt_nonneg _),
        ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
      ring

private theorem vorticityProducts_cutoff_families
    {m : ℕ} {U T : Set Vec3} (hU : IsOpen U) (hT : IsClosed T) (hTU : T ⊆ U)
    {χ : Vec3 → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hχc : HasCompactSupport χ) (hχU : tsupport χ ⊆ U)
    {L CL : ℝ} (hCL : 0 ≤ CL)
    (hLeib : ∀ (U V : Set Vec3) (A B : List (Fin 3) → Vec3 → ℝ) (L : ℝ),
      MeasurableSet U → MeasurableSet V → U ⊆ V →
      (∀ α : List (Fin 3), α.length ≤ m → ∀ x, |A α x| ≤ L) →
      (∀ α : List (Fin 3), α.length ≤ m → ∀ x, x ∉ U → A α x = 0) →
      (∀ α : List (Fin 3), α.length ≤ m →
        AEStronglyMeasurable (A α) (volume.restrict V)) →
      (∀ α : List (Fin 3), α.length ≤ m → MemLp (B α) 2 (volume.restrict V)) →
      sobolevNormSqOn m V (fun α => sobolevLeibnizFamily α A B) ≤
        CL * L ^ 2 * sobolevNormSqOn m (U ∩ V) B)
    (hχb : ∀ α : List (Fin 3), α.length ≤ m →
      ∀ x, |wordDeriv α χ x| ≤ L)
    (hχ0 : ∀ α : List (Fin 3), ∀ x, x ∉ T → wordDeriv α χ x = 0)
    (v : Vec3 → Vec3) (D : Fin 3 → List (Fin 3) → Vec3 → ℝ)
    (hD : ∀ i, IsSobolevFamilyOn m U (vecComponents v i) (D i)) :
    ∃ E : Fin 3 → List (Fin 3) → Vec3 → ℝ,
      (∀ i, IsSobolevFamilyOn m univ
        (fun x => χ x * vecComponents v i x) (E i)) ∧
      (∑ i, sobolevNormSqOn m univ (E i)) ≤
        CL * L ^ 2 * (∑ i, sobolevNormSqOn m U (D i)) := by
  let E : Fin 3 → List (Fin 3) → Vec3 → ℝ := fun i α =>
    sobolevLeibnizFamily α (fun β => wordDeriv β χ) (D i)
  have hE (i : Fin 3) : IsSobolevFamilyOn m univ
      (fun x => χ x * vecComponents v i x) (E i) :=
    (hD i).smooth_mul_univ hU hχ hχc hχU
  refine ⟨E, hE, ?_⟩
  calc
    (∑ i, sobolevNormSqOn m univ (E i)) ≤
        ∑ i, CL * L ^ 2 * sobolevNormSqOn m U (D i) := by
      apply Finset.sum_le_sum
      intro i _
      exact vorticityProducts_leibniz_univ_normSq_le hLeib hCL hU hT hTU hχ hχb hχ0 (hD i)
    _ = CL * L ^ 2 * (∑ i, sobolevNormSqOn m U (D i)) := by
      rw [Finset.mul_sum]

private theorem vorticityProducts_restrict_hNorm_le
    {ι : Type*} [Fintype ι] {m : ℕ} {U : Set Vec3} (hU : IsOpen U)
    {f g : ι → Vec3 → ℝ} {D : ι → List (Fin 3) → Vec3 → ℝ}
    (hD : ∀ i, IsSobolevFamilyOn m univ (f i) (D i))
    (heq : ∀ i, f i =ᵐ[volume.restrict U] g i) :
    hNormOn m U g ≤ hNormOn m univ f := by
  have hlocal (i : ι) : IsSobolevFamilyOn m U (g i) (D i) :=
    ((hD i).mono_set hU (subset_univ _)).congr_ae (heq i)
      (fun _ _ => Filter.EventuallyEq.rfl)
  rw [hNormOn_eq isOpen_univ hD]
  refine (hNormOn_le hlocal).trans (ENNReal.ofReal_le_ofReal
    (Real.sqrt_le_sqrt ?_))
  exact Finset.sum_le_sum fun i _ =>
    Finset.sum_le_sum fun α hα =>
      setIntegral_mono_set ((hD i).memL2 α (mem_sobolevWords.mp hα)).integrable_sq
        (ae_of_all _ fun _ => sq_nonneg _) (ae_of_all _ (subset_univ _))

private theorem vorticityProducts_cutoff_data {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    ∃ (χ₀ : Vec3 → ℝ) (L : ℝ),
      ContDiff ℝ (⊤ : ℕ∞) χ₀ ∧ HasCompactSupport χ₀ ∧
      tsupport χ₀ ⊆ vec3Ball 0 R ∧
      (∀ x, vec3EuclideanNorm x ≤ r → χ₀ x = 1) ∧
      (∀ x, 0 ≤ χ₀ x) ∧ (∀ x, χ₀ x ≤ 1) ∧
      (∀ α : List (Fin 3), α.length ≤ 3 → ∀ x, |wordDeriv α χ₀ x| ≤ L) := by
  obtain ⟨χ₀, hχ₀, hχ₀c, hsupp, hone, hpos, hle⟩ :=
    vorticitySpatialCutoff_exists hr hrR
  have hbd (α : List (Fin 3)) : ∃ M : ℝ, ∀ x, |wordDeriv α χ₀ x| ≤ M := by
    have hc : HasCompactSupport (wordDeriv α χ₀) :=
      hχ₀c.mono' ((subset_tsupport _).trans (vorticityProducts_tsupport_wordDeriv_subset α χ₀))
    obtain ⟨M, hM⟩ :=
      (contDiff_wordDeriv hχ₀ α).continuous.bounded_above_of_compact_support hc
    exact ⟨M, fun x => by simpa only [Real.norm_eq_abs] using hM x⟩
  choose M hM using hbd
  refine ⟨χ₀, ∑ α ∈ sobolevWords 3, |M α|,
    hχ₀, hχ₀c, hsupp, hone, hpos, hle, ?_⟩
  intro α hα x
  exact (hM α x).trans ((le_abs_self _).trans
    (Finset.single_le_sum (f := fun α => |M α|) (fun _ _ => abs_nonneg _)
      (mem_sobolevWords.2 hα)))

private theorem vorticityProducts_cutoff_translate
    {r R : ℝ}
    {χ₀ : Vec3 → ℝ} (hχ₀ : ContDiff ℝ (⊤ : ℕ∞) χ₀)
    (hχ₀c : HasCompactSupport χ₀)
    (hsupp : tsupport χ₀ ⊆ vec3Ball 0 R)
    (hone : ∀ x, vec3EuclideanNorm x ≤ r → χ₀ x = 1)
    (hpos : ∀ x, 0 ≤ χ₀ x) (hle : ∀ x, χ₀ x ≤ 1)
    {L : ℝ} (hL : ∀ α : List (Fin 3), α.length ≤ 3 →
      ∀ x, |wordDeriv α χ₀ x| ≤ L) (x₀ : Vec3) :
    ∃ χ : Vec3 → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧
      tsupport χ ⊆ vec3Ball x₀ R ∧
      (∀ x ∈ vec3Ball x₀ r, χ x = 1) ∧
      (∀ x, 0 ≤ χ x) ∧ (∀ x, χ x ≤ 1) ∧
      (∀ α : List (Fin 3), α.length ≤ 3 → ∀ x, |wordDeriv α χ x| ≤ L) := by
  let χ : Vec3 → ℝ := fun x => χ₀ (x - x₀)
  have hχ : ContDiff ℝ (⊤ : ℕ∞) χ := hχ₀.comp (contDiff_id.sub contDiff_const)
  have hχc : HasCompactSupport χ := hχ₀c.comp_homeomorph (Homeomorph.subRight x₀)
  have hχU : tsupport χ ⊆ vec3Ball x₀ R := by
    have hs : Function.support χ ⊆ (fun x => x - x₀) ⁻¹' tsupport χ₀ :=
      fun x hx => subset_tsupport χ₀ hx
    refine (closure_minimal hs ((isClosed_tsupport χ₀).preimage
      (continuous_id.sub continuous_const))).trans fun x hx => ?_
    have hh := hsupp hx
    change vec3EuclideanNorm (x - x₀ - 0) < R at hh
    change vec3EuclideanNorm (x - x₀) < R
    simpa only [sub_zero] using hh
  refine ⟨χ, hχ, hχc, hχU, ?_, fun x => hpos _, fun x => hle _, ?_⟩
  · intro x hx
    exact hone _ (le_of_lt hx)
  · intro α hα x
    rw [show wordDeriv α χ x = wordDeriv α χ₀ (x - x₀) from
      congrFun (vorticityProducts_wordDeriv_translate α χ₀ x₀) x]
    exact hL α hα _

private theorem vorticityProducts_cutoff_hNorm_le
    {m : ℕ} {U : Set Vec3} (hU : IsOpen U)
    {f g : Fin 3 → Vec3 → ℝ}
    {D E : Fin 3 → List (Fin 3) → Vec3 → ℝ}
    (hD : ∀ i, IsSobolevFamilyOn m U (f i) (D i))
    (hE : ∀ i, IsSobolevFamilyOn m univ (g i) (E i))
    {K : ℝ} (hK : 0 ≤ K)
    (hbound : (∑ i, sobolevNormSqOn m univ (E i)) ≤
      K * (∑ i, sobolevNormSqOn m U (D i))) :
    hNormOn m univ g ≤ ENNReal.ofReal (Real.sqrt K) * hNormOn m U f := by
  rw [hNormOn_eq isOpen_univ hE, hNormOn_eq hU hD]
  have hS : 0 ≤ ∑ i, sobolevNormSqOn m U (D i) := by
    apply Finset.sum_nonneg
    intro i _
    exact Finset.sum_nonneg fun α _ => integral_nonneg fun x => sq_nonneg _
  have hroot := Real.sqrt_le_sqrt hbound
  rw [Real.sqrt_mul hK] at hroot
  exact (ENNReal.ofReal_le_ofReal hroot).trans_eq
    (ENNReal.ofReal_mul (Real.sqrt_nonneg _))

private theorem vorticityProducts_cutoff_linf_le
    {U : Set Vec3} (hU : MeasurableSet U) {χ : Vec3 → ℝ}
    (hχU : tsupport χ ⊆ U) (hχ0 : ∀ x, 0 ≤ χ x) (hχ1 : ∀ x, χ x ≤ 1)
    (v : Vec3 → Vec3) {E : Fin 3 → List (Fin 3) → Vec3 → ℝ}
    (hE : ∀ i, IsSobolevFamilyOn 2 univ
      (fun x => χ x * vecComponents v i x) (E i)) :
    eLpNorm (fun x => vec3EuclideanNorm (fun i => χ x * v x i)) ⊤ volume ≤
      eLpNorm (fun x => vec3EuclideanNorm (v x)) ⊤ (volume.restrict U) := by
  have hmem (i : Fin 3) : MemLp (fun x => χ x * v x i) 2 volume := by
    simpa only [Measure.restrict_univ, vecComponents] using
      ((hE i).memL2 [] (Nat.zero_le _)).ae_eq (hE i).zero
  have hwae : AEMeasurable (fun x : Vec3 => (fun i : Fin 3 => χ x * v x i)) volume :=
    AEMeasurable.of_eval (fun i => (hmem i).aestronglyMeasurable.aemeasurable)
  have hmeas : AEStronglyMeasurable
      (fun x => vec3EuclideanNorm (fun i => χ x * v x i)) volume :=
    (continuous_vec3EuclideanNorm.measurable.comp_aemeasurable hwae).aestronglyMeasurable
  calc
    eLpNorm (fun x => vec3EuclideanNorm (fun i => χ x * v x i)) ⊤ volume ≤
        eLpNorm (U.indicator (fun x => vec3EuclideanNorm (v x))) ⊤ volume := by
      apply eLpNorm_mono_ae_real hmeas
      filter_upwards [] with x
      by_cases hx : x ∈ U
      · simp only [Set.indicator_of_mem hx, Real.norm_eq_abs]
        rw [show (fun i => χ x * v x i) = χ x • v x by
          funext i; rfl, vec3EuclideanNorm_smul, abs_of_nonneg (hχ0 x)]
        have hn : 0 ≤ vec3EuclideanNorm (v x) := Real.sqrt_nonneg _
        simpa only [abs_of_nonneg (mul_nonneg (hχ0 x) hn)] using
          mul_le_of_le_one_left hn (hχ1 x)
      · have hzero : χ x = 0 := image_eq_zero_of_notMem_tsupport fun h => hx (hχU h)
        simp [Set.indicator_of_notMem hx, hzero, vec3EuclideanNorm]
    _ = _ := eLpNorm_indicator_eq_eLpNorm_restrict hU

private theorem vorticityProducts_local_H2_core
    {r R : ℝ} {χ₀ : Vec3 → ℝ} {L C₂ CL : ℝ}
    (hχ₀ : ContDiff ℝ (⊤ : ℕ∞) χ₀) (hχ₀c : HasCompactSupport χ₀)
    (hsupp : tsupport χ₀ ⊆ vec3Ball 0 R)
    (hone : ∀ x, vec3EuclideanNorm x ≤ r → χ₀ x = 1)
    (hpos : ∀ x, 0 ≤ χ₀ x) (hle : ∀ x, χ₀ x ≤ 1)
    (hL : ∀ α : List (Fin 3), α.length ≤ 3 → ∀ x, |wordDeriv α χ₀ x| ≤ L)
    (hCL : 0 ≤ CL)
    (hLeib : ∀ (U V : Set Vec3) (A B : List (Fin 3) → Vec3 → ℝ) (L : ℝ),
      MeasurableSet U → MeasurableSet V → U ⊆ V →
      (∀ α : List (Fin 3), α.length ≤ 2 → ∀ x, |A α x| ≤ L) →
      (∀ α : List (Fin 3), α.length ≤ 2 → ∀ x, x ∉ U → A α x = 0) →
      (∀ α : List (Fin 3), α.length ≤ 2 →
        AEStronglyMeasurable (A α) (volume.restrict V)) →
      (∀ α : List (Fin 3), α.length ≤ 2 → MemLp (B α) 2 (volume.restrict V)) →
      sobolevNormSqOn 2 V (fun α => sobolevLeibnizFamily α A B) ≤
        CL * L ^ 2 * sobolevNormSqOn 2 (U ∩ V) B)
    (hC₂ : 0 ≤ C₂)
    (hGlobal : ∀ w : Vec3 → Vec3, HasCompactSupport w →
      hNormOn 2 univ (vecComponents w) < ⊤ →
      eLpNorm (fun x => vec3EuclideanNorm (w x)) ⊤ volume < ⊤ →
      hNormOn 2 univ (tensorSquareComponents w) ≤
        ENNReal.ofReal C₂ * eLpNorm (fun x => vec3EuclideanNorm (w x)) ⊤ volume *
          hNormOn 2 univ (vecComponents w))
    (x₀ : Vec3) (v : Vec3 → Vec3)
    (hv : hNormOn 2 (vec3Ball x₀ R) (vecComponents v) < ⊤)
    (hvInf : eLpNorm (fun x => vec3EuclideanNorm (v x)) ⊤
      (volume.restrict (vec3Ball x₀ R)) < ⊤) :
    hNormOn 2 (vec3Ball x₀ r) (tensorSquareComponents v) ≤
      ENNReal.ofReal (C₂ * Real.sqrt (CL * L ^ 2)) *
        eLpNorm (fun x => vec3EuclideanNorm (v x)) ⊤
          (volume.restrict (vec3Ball x₀ R)) *
        hNormOn 2 (vec3Ball x₀ R) (vecComponents v) := by
  obtain ⟨χ, hχ, hχc, hχU, hχone, hχpos, hχle, hχb⟩ :=
    vorticityProducts_cutoff_translate hχ₀ hχ₀c hsupp hone hpos hle hL x₀
  let U := vec3Ball x₀ R
  let B := vec3Ball x₀ r
  let w : Vec3 → Vec3 := fun x i => χ x * v x i
  have hU : IsOpen U := isOpen_vec3Ball x₀ R
  have hB : IsOpen B := isOpen_vec3Ball x₀ r
  choose D hD using hNormOn_lt_top_iff.mp hv
  have hχ0 (α : List (Fin 3)) (x : Vec3) (hx : x ∉ tsupport χ) :
      wordDeriv α χ x = 0 :=
    image_eq_zero_of_notMem_tsupport fun h => hx (vorticityProducts_tsupport_wordDeriv_subset α χ h)
  obtain ⟨E, hE, hEb⟩ := vorticityProducts_cutoff_families hU
    (isClosed_tsupport χ) hχU hχ hχc hχU hCL hLeib
    (fun α hα x => hχb α (by omega) x) hχ0 v D hD
  have hEw (i : Fin 3) : IsSobolevFamilyOn 2 univ (vecComponents w i) (E i) := by
    change IsSobolevFamilyOn 2 univ (fun x => χ x * v x i) (E i)
    exact hE i
  have hw : hNormOn 2 univ (vecComponents w) < ⊤ :=
    hNormOn_lt_top_iff.mpr (fun i => ⟨E i, hEw i⟩)
  have hwc : HasCompactSupport w := by
    apply hχc.mono'
    intro x hx
    apply subset_tsupport χ
    intro hχx
    apply hx
    funext i
    simp [w, hχx]
  have hInf := vorticityProducts_cutoff_linf_le hU.measurableSet hχU hχpos hχle v hE
  have hwInf : eLpNorm (fun x => vec3EuclideanNorm (w x)) ⊤ volume < ⊤ := by
    apply lt_of_le_of_lt (by simpa [w] using hInf) hvInf
  have hlocal (ij : Fin 3 × Fin 3) :
      tensorSquareComponents w ij =ᵐ[volume.restrict B] tensorSquareComponents v ij := by
    refine (ae_restrict_iff' hB.measurableSet).2 (ae_of_all _ fun x hx => ?_)
    simp only [tensorSquareComponents, w, hχone x hx,
      one_mul]
  have hprod := hGlobal w hwc hw hwInf
  have hprodFin : hNormOn 2 univ (tensorSquareComponents w) < ⊤ :=
    lt_of_le_of_lt hprod
      (ENNReal.mul_lt_top
        (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hwInf) hw)
  choose F hF using hNormOn_lt_top_iff.mp hprodFin
  have hrestrict := vorticityProducts_restrict_hNorm_le hB hF hlocal
  have hcut : hNormOn 2 univ (vecComponents w) ≤
      ENNReal.ofReal (Real.sqrt (CL * L ^ 2)) * hNormOn 2 U (vecComponents v) :=
    vorticityProducts_cutoff_hNorm_le hU hD hEw
      (mul_nonneg hCL (sq_nonneg L)) hEb
  calc
    hNormOn 2 B (tensorSquareComponents v) ≤
        hNormOn 2 univ (tensorSquareComponents w) := hrestrict
    _ ≤ ENNReal.ofReal C₂ *
        eLpNorm (fun x => vec3EuclideanNorm (w x)) ⊤ volume *
        hNormOn 2 univ (vecComponents w) := hprod
    _ ≤ ENNReal.ofReal C₂ *
        eLpNorm (fun x => vec3EuclideanNorm (v x)) ⊤ (volume.restrict U) *
        (ENNReal.ofReal (Real.sqrt (CL * L ^ 2)) *
          hNormOn 2 U (vecComponents v)) := by
      gcongr
    _ = _ := by
      rw [ENNReal.ofReal_mul hC₂]
      simp only [U]
      ring

private theorem vorticityProducts_local_H3_core
    {r R : ℝ} {χ₀ : Vec3 → ℝ} {L C₃ CL₂ CL₃ : ℝ}
    (hχ₀ : ContDiff ℝ (⊤ : ℕ∞) χ₀) (hχ₀c : HasCompactSupport χ₀)
    (hsupp : tsupport χ₀ ⊆ vec3Ball 0 R)
    (hone : ∀ x, vec3EuclideanNorm x ≤ r → χ₀ x = 1)
    (hpos : ∀ x, 0 ≤ χ₀ x) (hle : ∀ x, χ₀ x ≤ 1)
    (hL : ∀ α : List (Fin 3), α.length ≤ 3 → ∀ x, |wordDeriv α χ₀ x| ≤ L)
    (hCL₂ : 0 ≤ CL₂)
    (hLeib₂ : ∀ (U V : Set Vec3) (A B : List (Fin 3) → Vec3 → ℝ) (L : ℝ),
      MeasurableSet U → MeasurableSet V → U ⊆ V →
      (∀ α : List (Fin 3), α.length ≤ 2 → ∀ x, |A α x| ≤ L) →
      (∀ α : List (Fin 3), α.length ≤ 2 → ∀ x, x ∉ U → A α x = 0) →
      (∀ α : List (Fin 3), α.length ≤ 2 →
        AEStronglyMeasurable (A α) (volume.restrict V)) →
      (∀ α : List (Fin 3), α.length ≤ 2 → MemLp (B α) 2 (volume.restrict V)) →
      sobolevNormSqOn 2 V (fun α => sobolevLeibnizFamily α A B) ≤
        CL₂ * L ^ 2 * sobolevNormSqOn 2 (U ∩ V) B)
    (hCL₃ : 0 ≤ CL₃)
    (hLeib₃ : ∀ (U V : Set Vec3) (A B : List (Fin 3) → Vec3 → ℝ) (L : ℝ),
      MeasurableSet U → MeasurableSet V → U ⊆ V →
      (∀ α : List (Fin 3), α.length ≤ 3 → ∀ x, |A α x| ≤ L) →
      (∀ α : List (Fin 3), α.length ≤ 3 → ∀ x, x ∉ U → A α x = 0) →
      (∀ α : List (Fin 3), α.length ≤ 3 →
        AEStronglyMeasurable (A α) (volume.restrict V)) →
      (∀ α : List (Fin 3), α.length ≤ 3 → MemLp (B α) 2 (volume.restrict V)) →
      sobolevNormSqOn 3 V (fun α => sobolevLeibnizFamily α A B) ≤
        CL₃ * L ^ 2 * sobolevNormSqOn 3 (U ∩ V) B)
    (hC₃ : 0 ≤ C₃)
    (hGlobal : ∀ w : Vec3 → Vec3,
      hNormOn 3 univ (vecComponents w) < ⊤ →
      hNormOn 3 univ (tensorSquareComponents w) ≤
        ENNReal.ofReal C₃ * hNormOn 2 univ (vecComponents w) *
          hNormOn 3 univ (vecComponents w))
    (x₀ : Vec3) (v : Vec3 → Vec3)
    (hv : hNormOn 3 (vec3Ball x₀ R) (vecComponents v) < ⊤) :
    hNormOn 3 (vec3Ball x₀ r) (tensorSquareComponents v) ≤
      ENNReal.ofReal (C₃ * Real.sqrt (CL₂ * L ^ 2) * Real.sqrt (CL₃ * L ^ 2)) *
        hNormOn 2 (vec3Ball x₀ R) (vecComponents v) *
        hNormOn 3 (vec3Ball x₀ R) (vecComponents v) := by
  obtain ⟨χ, hχ, hχc, hχU, hχone, -, -, hχb⟩ :=
    vorticityProducts_cutoff_translate hχ₀ hχ₀c hsupp hone hpos hle hL x₀
  let U := vec3Ball x₀ R
  let B := vec3Ball x₀ r
  let w : Vec3 → Vec3 := fun x i => χ x * v x i
  have hU : IsOpen U := isOpen_vec3Ball x₀ R
  have hB : IsOpen B := isOpen_vec3Ball x₀ r
  choose D₃ hD₃ using hNormOn_lt_top_iff.mp hv
  have hD₂ (i : Fin 3) : IsSobolevFamilyOn 2 U (vecComponents v i) (D₃ i) :=
    (hD₃ i).of_le (by omega)
  have hχ0 (α : List (Fin 3)) (x : Vec3) (hx : x ∉ tsupport χ) :
      wordDeriv α χ x = 0 :=
    image_eq_zero_of_notMem_tsupport fun h => hx (vorticityProducts_tsupport_wordDeriv_subset α χ h)
  obtain ⟨E₂, hE₂, hE₂b⟩ := vorticityProducts_cutoff_families hU
    (isClosed_tsupport χ) hχU hχ hχc hχU hCL₂ hLeib₂
    (fun α hα x => hχb α (by omega) x) hχ0 v D₃ hD₂
  obtain ⟨E₃, hE₃, hE₃b⟩ := vorticityProducts_cutoff_families hU
    (isClosed_tsupport χ) hχU hχ hχc hχU hCL₃ hLeib₃ hχb hχ0 v D₃ hD₃
  have hE₂w (i : Fin 3) : IsSobolevFamilyOn 2 univ (vecComponents w i) (E₂ i) := by
    change IsSobolevFamilyOn 2 univ (fun x => χ x * v x i) (E₂ i)
    exact hE₂ i
  have hE₃w (i : Fin 3) : IsSobolevFamilyOn 3 univ (vecComponents w i) (E₃ i) := by
    change IsSobolevFamilyOn 3 univ (fun x => χ x * v x i) (E₃ i)
    exact hE₃ i
  have hw : hNormOn 3 univ (vecComponents w) < ⊤ :=
    hNormOn_lt_top_iff.mpr (fun i => ⟨E₃ i, hE₃w i⟩)
  have hlocal (ij : Fin 3 × Fin 3) :
      tensorSquareComponents w ij =ᵐ[volume.restrict B] tensorSquareComponents v ij := by
    refine (ae_restrict_iff' hB.measurableSet).2 (ae_of_all _ fun x hx => ?_)
    simp only [tensorSquareComponents, w, hχone x hx,
      one_mul]
  have hprod := hGlobal w hw
  have hw₂ : hNormOn 2 univ (vecComponents w) < ⊤ :=
    hNormOn_lt_top_iff.mpr (fun i => ⟨E₂ i, hE₂w i⟩)
  have hprodFin : hNormOn 3 univ (tensorSquareComponents w) < ⊤ :=
    lt_of_le_of_lt hprod
      (ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hw₂) hw)
  choose F hF using hNormOn_lt_top_iff.mp hprodFin
  have hrestrict := vorticityProducts_restrict_hNorm_le hB hF hlocal
  have hcut₂ : hNormOn 2 univ (vecComponents w) ≤
      ENNReal.ofReal (Real.sqrt (CL₂ * L ^ 2)) * hNormOn 2 U (vecComponents v) :=
    vorticityProducts_cutoff_hNorm_le hU hD₂ hE₂w
      (mul_nonneg hCL₂ (sq_nonneg L)) hE₂b
  have hcut₃ : hNormOn 3 univ (vecComponents w) ≤
      ENNReal.ofReal (Real.sqrt (CL₃ * L ^ 2)) * hNormOn 3 U (vecComponents v) :=
    vorticityProducts_cutoff_hNorm_le hU hD₃ hE₃w
      (mul_nonneg hCL₃ (sq_nonneg L)) hE₃b
  calc
    hNormOn 3 B (tensorSquareComponents v) ≤
        hNormOn 3 univ (tensorSquareComponents w) := hrestrict
    _ ≤ ENNReal.ofReal C₃ * hNormOn 2 univ (vecComponents w) *
        hNormOn 3 univ (vecComponents w) := hprod
    _ ≤ ENNReal.ofReal C₃ *
        (ENNReal.ofReal (Real.sqrt (CL₂ * L ^ 2)) * hNormOn 2 U (vecComponents v)) *
        (ENNReal.ofReal (Real.sqrt (CL₃ * L ^ 2)) * hNormOn 3 U (vecComponents v)) := by
      gcongr
    _ = _ := by
      rw [ENNReal.ofReal_mul (mul_nonneg hC₃ (Real.sqrt_nonneg _)),
        ENNReal.ofReal_mul hC₃]
      simp only [U]
      ring

/-- The local product estimates in `lem:vorticity-products`, conditional on
smooth compactly supported density for whole-space Sobolev families. -/
theorem vorticityProducts_local
    (hApprox : ∀ {ι : Type} [Fintype ι] {m : ℕ} {f : ι → Vec3 → ℝ}
      {D : ι → List (Fin 3) → Vec3 → ℝ},
      (∀ i, IsSobolevFamilyOn m univ (f i) (D i)) →
      ∃ g : ℕ → ι → Vec3 → ℝ,
        (∀ n i, ContDiff ℝ (⊤ : ℕ∞) (g n i)) ∧
        (∀ n i, HasCompactSupport (g n i)) ∧
        (∀ i (α : List (Fin 3)), α.length ≤ m →
          Tendsto (fun n => eLpNorm (wordDeriv α (g n i) - D i α) 2 volume)
            atTop (𝓝 0)) ∧
        ∀ M : ℝ, (∀ᵐ x ∂volume, Real.sqrt (∑ i, f i x ^ 2) ≤ M) →
          ∀ n x, Real.sqrt (∑ i, g n i x ^ 2) ≤ M)
    {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x₀ : Vec3) (v : Vec3 → Vec3),
      (hNormOn 2 (vec3Ball x₀ R) (vecComponents v) < ⊤ →
        eLpNorm (fun x => vec3EuclideanNorm (v x)) ⊤
          (volume.restrict (vec3Ball x₀ R)) < ⊤ →
        hNormOn 2 (vec3Ball x₀ r) (tensorSquareComponents v) ≤
          ENNReal.ofReal C *
            eLpNorm (fun x => vec3EuclideanNorm (v x)) ⊤
              (volume.restrict (vec3Ball x₀ R)) *
            hNormOn 2 (vec3Ball x₀ R) (vecComponents v)) ∧
      (hNormOn 3 (vec3Ball x₀ R) (vecComponents v) < ⊤ →
        hNormOn 3 (vec3Ball x₀ r) (tensorSquareComponents v) ≤
          ENNReal.ofReal C * hNormOn 2 (vec3Ball x₀ R) (vecComponents v) *
            hNormOn 3 (vec3Ball x₀ R) (vecComponents v)) := by
  obtain ⟨χ₀, L, hχ₀, hχ₀c, hsupp, hone, hpos, hle, hL⟩ :=
    vorticityProducts_cutoff_data hr hrR
  obtain ⟨CL₂, hCL₂, hLeib₂⟩ := sobolevLeibnizFamily_normSq_le 2
  obtain ⟨CL₃, hCL₃, hLeib₃⟩ := sobolevLeibnizFamily_normSq_le 3
  obtain ⟨C₂, hC₂, hG₂⟩ := vorticityProducts_H2 hApprox
  obtain ⟨C₃, hC₃, hG₃⟩ := vorticityProducts_H3 hApprox
  let A := C₂ * Real.sqrt (CL₂ * L ^ 2)
  let B := C₃ * Real.sqrt (CL₂ * L ^ 2) * Real.sqrt (CL₃ * L ^ 2)
  have hA : 0 ≤ A := mul_nonneg hC₂ (Real.sqrt_nonneg _)
  have hB : 0 ≤ B := mul_nonneg (mul_nonneg hC₃ (Real.sqrt_nonneg _))
    (Real.sqrt_nonneg _)
  refine ⟨A + B, add_nonneg hA hB, ?_⟩
  intro x₀ v
  constructor
  · intro hv hvInf
    have h := vorticityProducts_local_H2_core hχ₀ hχ₀c hsupp hone hpos hle hL
      hCL₂ hLeib₂ hC₂ hG₂ x₀ v hv hvInf
    calc
      _ ≤ ENNReal.ofReal A *
          eLpNorm (fun x => vec3EuclideanNorm (v x)) ⊤
            (volume.restrict (vec3Ball x₀ R)) *
          hNormOn 2 (vec3Ball x₀ R) (vecComponents v) := h
      _ ≤ _ := by
        gcongr
        exact le_add_of_nonneg_right hB
  · intro hv
    have h := vorticityProducts_local_H3_core hχ₀ hχ₀c hsupp hone hpos hle hL
      hCL₂ hLeib₂ hCL₃ hLeib₃ hC₃ hG₃ x₀ v hv
    calc
      _ ≤ ENNReal.ofReal B * hNormOn 2 (vec3Ball x₀ R) (vecComponents v) *
          hNormOn 3 (vec3Ball x₀ R) (vecComponents v) := h
      _ ≤ _ := by
        gcongr
        exact le_add_of_nonneg_left hA

end ESS
