/-
Copyright (c) 2026 DICTO. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DICTO
-/

/- Modified for Lean Pool. -/

module

public import LeanPool.DehnInvariant.AngleSum
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
Lean study 2 of the shape-language canon (DICTO, 19 Nov 2026), part D: the core lemma.

`dehnSet_cut`: for a convex polytope `P` in 3-space and any plane, the Dehn invariant of `P` is
the sum of the
Dehn invariants of the two parts.  (An old edge inside the plane: its angle splits in two. A new
edge on a
face or inside the solid: its two angles sum to π or 2π, which is zero in ℝ/ℚπ. An old edge
crossing the plane
is cut at one point, which has length zero.)
No `sorry`.
-/

@[expose] public section

open scoped RealInnerProductSpace
open Set MeasureTheory Measure Module TensorProduct

namespace DehnCanon.Library

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {ι : Type}

/-- The constraints that hold with equality at `x`. -/
def act (a : ι → E) (b : ι → ℝ) (x : E) : Set ι := {i | ⟪a i, x⟫ = b i}

/-- The cone cut out by the constraints in `A`. -/
def cone (a : ι → E) (A : Set ι) : Set E := {v | ∀ i ∈ A, ⟪a i, v⟫ ≤ 0}

/-- The largest linear subspace inside `cone a A`. -/
def linCone (a : ι → E) (A : Set ι) : Submodule ℝ E where
  carrier := {v | ∀ i ∈ A, ⟪a i, v⟫ = 0}
  add_mem' := fun {u v} hu hv => by
    change ∀ i ∈ A, ⟪a i, u + v⟫ = 0
    intro i hi
    have h1 : ⟪a i, u⟫ = 0 := hu i hi
    have h2 : ⟪a i, v⟫ = 0 := hv i hi
    rw [inner_add_right, h1, h2, add_zero]
  zero_mem' := by
    change ∀ i ∈ A, ⟪a i, (0 : E)⟫ = 0
    intro i _; exact inner_zero_right _
  smul_mem' := fun r {v} hv => by
    change ∀ i ∈ A, ⟪a i, r • v⟫ = 0
    intro i hi
    have h1 : ⟪a i, v⟫ = 0 := hv i hi
    rw [inner_smul_right, h1, mul_zero]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma mem_linCone {a : ι → E} {A : Set ι} {v : E} : v ∈ linCone a A ↔ ∀ i ∈ A, ⟪a i, v⟫
    = 0 := Iff.rfl

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma cone_add (a : ι → E) (A : Set ι) : ∀ v ∈ cone a A, ∀ w ∈ cone a A, v + w ∈ cone a A := by
  intro v hv w hw i hi
  have h1 : ⟪a i, v⟫ ≤ 0 := hv i hi
  have h2 : ⟪a i, w⟫ ≤ 0 := hw i hi
  rw [inner_add_right]; linarith

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma cone_smul (a : ι → E) (A : Set ι) : ∀ v ∈ cone a A, ∀ s : ℝ, 0 < s → s • v ∈ cone a A := by
  intro v hv s hs i hi
  have h1 : ⟪a i, v⟫ ≤ 0 := hv i hi
  rw [inner_smul_right]
  exact mul_nonpos_of_nonneg_of_nonpos hs.le h1

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma cone_lin (a : ι → E) (A : Set ι) : ∀ v, (v ∈ cone a A ∧ -v ∈ cone a A) ↔ v ∈ linCone a A := by
  intro v; constructor
  · rintro ⟨h1, h2⟩ i hi
    have h3 : ⟪a i, v⟫ ≤ 0 := h1 i hi
    have h4 : ⟪a i, -v⟫ ≤ 0 := h2 i hi
    rw [inner_neg_right] at h4
    linarith
  · intro h
    refine ⟨fun i hi => ?_, fun i hi => ?_⟩
    · rw [h i hi]
    · rw [inner_neg_right, h i hi, neg_zero]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma linSpace_cone (a : ι → E) (A : Set ι) : linSpace (cone a A) = linCone a A :=
  linSpace_eq_of (cone_lin a A)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- At a point of a polytope, the directions that stay inside are given by the active constraints.
-/
lemma tcone_sol [Finite ι] (a : ι → E) (b : ι → ℝ) {x : E} (hx : x ∈ sol a b) :
    tcone (sol a b) x = cone a (act a b x) := by
  ext v; constructor
  · rintro ⟨-, t, ht, hmem⟩ i hi
    have h1 : ⟪a i, x + t • v⟫ ≤ b i := hmem i
    have h2 : ⟪a i, x⟫ = b i := hi
    rw [inner_add_right, inner_smul_right, h2] at h1
    by_contra hpos
    have hpos' : 0 < ⟪a i, v⟫ := not_le.1 hpos
    have h3 := mul_pos ht hpos'
    linarith
  · intro hv
    refine ⟨hx, ?_⟩
    have hev : ∀ᶠ t : ℝ in nhdsWithin 0 (Set.Ioi 0), ∀ i, ⟪a i, x + t • v⟫ ≤ b i := by
      rw [Filter.eventually_all]
      intro i
      by_cases hi : ⟪a i, x⟫ = b i
      · have hvi : ⟪a i, v⟫ ≤ 0 := hv i hi
        filter_upwards [eventually_mem_nhdsWithin] with t ht
        have ht' : (0 : ℝ) < t := ht
        rw [inner_add_right, inner_smul_right, hi]
        have h3 := mul_nonpos_of_nonneg_of_nonpos ht'.le hvi
        linarith
      · have hlt : ⟪a i, x⟫ < b i := lt_of_le_of_ne (hx i) hi
        have hcont : Continuous fun t : ℝ => ⟪a i, x + t • v⟫ := by fun_prop
        have hm : {t : ℝ | ⟪a i, x + t • v⟫ < b i} ∈ nhds (0 : ℝ) :=
          (isOpen_lt hcont continuous_const).mem_nhds (by
            change ⟪a i, x + (0 : ℝ) • v⟫ < b i
            rw [zero_smul, add_zero]; exact hlt)
        filter_upwards [nhdsWithin_le_nhds hm] with t ht
        exact le_of_lt ht
    obtain ⟨t, ht, htpos⟩ := (hev.and eventually_mem_nhdsWithin).exists
    exact ⟨t, htpos, ht⟩

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma tcone_cut_eq [Finite ι] (a : ι → E) (b : ι → ℝ) {c : E} {d : ℝ} {x : E} (hx : x ∈ sol a b)
    (hxd : ⟪c, x⟫ = d) :
    tcone (sol a b ∩ hsLe c d) x = cone a (act a b x) ∩ {v | ⟪c, v⟫ ≤ 0} := by
  have hx' : x ∈ sol (fun o : Option ι => o.elim c a) (fun o : Option ι => o.elim d b) := by
    rw [← sol_inter_hsLe]; exact ⟨hx, hxd.le⟩
  rw [sol_inter_hsLe, tcone_sol _ _ hx']
  ext v; constructor
  · intro h
    exact ⟨fun i hi => h (some i) hi, h none hxd⟩
  · rintro ⟨h1, h2⟩ o ho
    cases o with
    | none => exact h2
    | some i => exact h1 i ho

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma tcone_cut_lt [Finite ι] (a : ι → E) (b : ι → ℝ) {c : E} {d : ℝ} {x : E} (hx : x ∈ sol a b)
    (hxd : ⟪c, x⟫ < d) :
    tcone (sol a b ∩ hsLe c d) x = cone a (act a b x) := by
  have hx' : x ∈ sol (fun o : Option ι => o.elim c a) (fun o : Option ι => o.elim d b) := by
    rw [← sol_inter_hsLe]; exact ⟨hx, hxd.le⟩
  rw [sol_inter_hsLe, tcone_sol _ _ hx']
  ext v; constructor
  · intro h i hi
    exact h (some i) hi
  · intro h o ho
    cases o with
    | none => exact absurd ho (ne_of_lt hxd)
    | some i => exact h i ho

lemma edgeAngle_sol [Finite ι] (a : ι → E) (b : ι → ℝ) {x : E} (hx : x ∈ sol a b) :
    edgeAngle (sol a b) x = theta (cone a (act a b x)) := by
  unfold edgeAngle; rw [tcone_sol a b hx]

/-- **The angle class at a point under a plane cut**: additive, except at the points where an edge
crosses the plane. -/
lemma edgeAngle_cut [Fact (finrank ℝ E = 3)] [Finite ι] (a : ι → E) (b : ι → ℝ) {c : E} (hc : c ≠ 0)
    (d : ℝ) (x : E)
    (hexc : ¬ (x ∈ sol a b ∧ ⟪c, x⟫ = d ∧ finrank ℝ (linCone a (act a b x)) = 1 ∧
      ¬ linCone a (act a b x) ≤ (ℝ ∙ c)ᗮ)) :
    edgeAngle (sol a b) x = edgeAngle (sol a b ∩ hsLe c d) x + edgeAngle (sol a b ∩ hsGe c d)
        x := by
  by_cases hx : x ∈ sol a b
  · rcases lt_trichotomy ⟪c, x⟫ d with hlt | heq | hgt
    · have h1 : x ∉ sol a b ∩ hsGe c d := fun h => by
        have := mem_hsGe.1 h.2; linarith
      rw [edgeAngle_of_notMem h1, add_zero]
      unfold edgeAngle
      rw [tcone_sol a b hx, tcone_cut_lt a b hx hlt]
    · have heq' : ⟪-c, x⟫ = -d := by rw [inner_neg_left, heq]
      have h2 : tcone (sol a b ∩ hsGe c d) x = cone a (act a b x) ∩ {v | ⟪-c, v⟫ ≤ 0} :=
        tcone_cut_eq a b hx heq'
      unfold edgeAngle
      rw [tcone_sol a b hx, tcone_cut_eq a b hx heq, h2]
      exact theta_cut (cone_lin a _) (cone_add a _) (cone_smul a _) hc
        (fun h => hexc ⟨hx, heq, h.1, h.2⟩)
    · have h1 : x ∉ sol a b ∩ hsLe c d := fun h => by
        have := mem_hsLe.1 h.2; linarith
      have hlt' : ⟪-c, x⟫ < -d := by rw [inner_neg_left]; linarith
      have h2 : tcone (sol a b ∩ hsGe c d) x = cone a (act a b x) := tcone_cut_lt a b hx hlt'
      rw [edgeAngle_of_notMem h1, zero_add]
      unfold edgeAngle
      rw [tcone_sol a b hx, h2]
  · have hle : x ∉ sol a b ∩ hsLe c d := fun h => hx h.1
    have hge : x ∉ sol a b ∩ hsGe c d := fun h => hx h.1
    rw [edgeAngle_of_notMem hx, edgeAngle_of_notMem hle, edgeAngle_of_notMem hge, add_zero]

lemma edgeAngle_sol_congr [Finite ι] (a : ι → E) (b : ι → ℝ) {x y : E}
    (hmem : x ∈ sol a b ↔ y ∈ sol a b) (hact : act a b x = act a b y) :
    edgeAngle (sol a b) x = edgeAngle (sol a b) y := by
  by_cases hx : x ∈ sol a b
  · rw [edgeAngle_sol a b hx, edgeAngle_sol a b (hmem.1 hx), hact]
  · rw [edgeAngle_of_notMem hx, edgeAngle_of_notMem (fun h => hx (hmem.2 h))]

lemma edgeAngle_cut_congr [Finite ι] (a : ι → E) (b : ι → ℝ) (c : E) (d : ℝ) {x y : E}
    (hmem : x ∈ sol a b ↔ y ∈ sol a b) (hact : act a b x = act a b y)
    (hle : ⟪c, x⟫ ≤ d ↔ ⟪c, y⟫ ≤ d) (heq : ⟪c, x⟫ = d ↔ ⟪c, y⟫ = d) :
    edgeAngle (sol a b ∩ hsLe c d) x = edgeAngle (sol a b ∩ hsLe c d) y := by
  rw [sol_inter_hsLe]
  apply edgeAngle_sol_congr
  · rw [← sol_inter_hsLe]
    exact and_congr hmem hle
  · ext o
    cases o with
    | none => exact heq
    | some i => exact Set.ext_iff.1 hact i

/-- The sign pattern of a point against all the planes: the classifier. -/
noncomputable def cls (a : ι → E) (b : ι → ℝ) (c : E) (d : ℝ) (x : E) : (ι → SignType) × SignType :=
  (fun i => SignType.sign (⟪a i, x⟫ - b i), SignType.sign (⟪c, x⟫ - d))

omit [FiniteDimensional ℝ E] in
lemma meas_sign (u : E) (r : ℝ) (s : SignType) :
    MeasurableSet {x : E | SignType.sign (⟪u, x⟫ - r) = s} := by
  have hcont : Continuous fun x : E => ⟪u, x⟫ - r := by fun_prop
  rcases s with _ | _ | _
  · have h : {x : E | SignType.sign (⟪u, x⟫ - r) = SignType.zero} = {x | ⟪u, x⟫ - r = 0} := by
      ext x; exact sign_eq_zero_iff
    rw [h]; exact (isClosed_eq hcont continuous_const).measurableSet
  · have h : {x : E | SignType.sign (⟪u, x⟫ - r) = SignType.neg} = {x | ⟪u, x⟫ - r < 0} := by
      ext x; exact sign_eq_neg_one_iff
    rw [h]; exact (isOpen_lt hcont continuous_const).measurableSet
  · have h : {x : E | SignType.sign (⟪u, x⟫ - r) = SignType.pos} = {x | 0 < ⟪u, x⟫ - r} := by
      ext x; exact sign_eq_one_iff
    rw [h]; exact (isOpen_lt continuous_const hcont).measurableSet

omit [FiniteDimensional ℝ E] in
lemma cls_meas [Finite ι] (a : ι → E) (b : ι → ℝ) (c : E) (d : ℝ) (k : (ι → SignType) × SignType) :
    MeasurableSet (cls a b c d ⁻¹' {k}) := by
  have h : cls a b c d ⁻¹' {k} =
      (⋂ i, {x : E | SignType.sign (⟪a i, x⟫ - b i) = k.1 i}) ∩
        {x : E | SignType.sign (⟪c, x⟫ - d) = k.2} := by
    ext x
    simp only [mem_preimage, mem_singleton_iff, mem_inter_iff, mem_iInter, mem_ofPred_eq, cls,
      Prod.ext_iff, funext_iff]
  rw [h]
  exact (MeasurableSet.iInter fun i => meas_sign _ _ _).inter (meas_sign _ _ _)

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma cls_facts (a : ι → E) (b : ι → ℝ) (c : E) (d : ℝ) {x y : E} (h : cls a b c d x
    = cls a b c d y) :
    (x ∈ sol a b ↔ y ∈ sol a b) ∧ act a b x = act a b y ∧
    (⟪c, x⟫ ≤ d ↔ ⟪c, y⟫ ≤ d) ∧ (⟪c, x⟫ = d ↔ ⟪c, y⟫ = d) ∧ (d ≤ ⟪c, x⟫ ↔ d ≤ ⟪c, y⟫) := by
  have h1 : ∀ i, SignType.sign (⟪a i, x⟫ - b i) = SignType.sign (⟪a i, y⟫ - b i) :=
    fun i => congrFun (congrArg Prod.fst h) i
  have h2 : SignType.sign (⟪c, x⟫ - d) = SignType.sign (⟪c, y⟫ - d) := congrArg Prod.snd h
  have le_iff : ∀ p q : ℝ, SignType.sign p = SignType.sign q → (p ≤ 0 ↔ q ≤ 0) := by
    intro p q hpq; rw [← sign_nonpos_iff, ← sign_nonpos_iff (a := q), hpq]
  have eq_iff : ∀ p q : ℝ, SignType.sign p = SignType.sign q → (p = 0 ↔ q = 0) := by
    intro p q hpq; rw [← sign_eq_zero_iff, ← sign_eq_zero_iff (a := q), hpq]
  have ge_iff : ∀ p q : ℝ, SignType.sign p = SignType.sign q → (0 ≤ p ↔ 0 ≤ q) := by
    intro p q hpq; rw [← sign_nonneg_iff, ← sign_nonneg_iff (a := q), hpq]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · constructor
    · intro hx i; exact sub_nonpos.1 ((le_iff _ _ (h1 i)).1 (sub_nonpos.2 (hx i)))
    · intro hy i; exact sub_nonpos.1 ((le_iff _ _ (h1 i)).2 (sub_nonpos.2 (hy i)))
  · ext i
    change ⟪a i, x⟫ = b i ↔ ⟪a i, y⟫ = b i
    rw [← sub_eq_zero, ← sub_eq_zero (a := ⟪a i, y⟫)]
    exact eq_iff _ _ (h1 i)
  · rw [← sub_nonpos, ← sub_nonpos (a := ⟪c, y⟫)]; exact le_iff _ _ h2
  · rw [← sub_eq_zero, ← sub_eq_zero (a := ⟪c, y⟫)]; exact eq_iff _ _ h2
  · rw [← sub_nonneg, ← sub_nonneg (a := ⟪c, y⟫)]; exact ge_iff _ _ h2

/-- The edge points of a bounded polytope have finite total length. -/
lemma support_finite [Finite ι] (a : ι → E) (b : ι → ℝ) (hb : Bornology.IsBounded (sol a b)) :
    μH[1] {x | edgeAngle (sol a b) x ≠ 0} ≠ ⊤ := by
  classical
  let R : Set ι → Set E := fun A => {x | x ∈ sol a b ∧ act a b x = A ∧ finrank ℝ (linCone a A) = 1}
  have hsub : {x | edgeAngle (sol a b) x ≠ 0} ⊆ ⋃ A ∈ (Set.univ : Set (Set ι)), R A := by
    intro x hx
    have hx0 : edgeAngle (sol a b) x ≠ 0 := hx
    have hxs : x ∈ sol a b := by
      by_contra hno; exact hx0 (edgeAngle_of_notMem hno)
    rw [edgeAngle_sol a b hxs] at hx0
    have hfr : finrank ℝ (linCone a (act a b x)) = 1 := by
      by_contra hno
      apply hx0
      unfold theta
      rw [linSpace_cone, ite_eq_right hno]
    exact mem_biUnion (mem_univ (act a b x)) ⟨hxs, rfl, hfr⟩
  obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.1 hb
  have hR : ∀ A ∈ (Set.univ : Set (Set ι)), μH[1] (R A) < ⊤ := by
    intro A _
    rcases (R A).eq_empty_or_nonempty with he | ⟨x0, hx0s, hx0A, hfr⟩
    · rw [he, measure_empty]; exact ENNReal.zero_lt_top
    · obtain ⟨u, hu0, hspan⟩ := finrank_eq_one_iff'.1 hfr
      have hu0' : (u : E) ≠ 0 := fun h => hu0 (Subtype.ext h)
      have hun : 0 < ‖(u : E)‖ := norm_pos_iff.2 hu0'
      let f : ℝ → E := fun t => x0 + t • (u : E)
      have hLip : LipschitzWith ‖(u : E)‖₊ f := by
        apply LipschitzWith.of_dist_le_mul
        intro s t
        change dist (x0 + s • (u : E)) (x0 + t • (u : E)) ≤ ↑‖(u : E)‖₊ * dist s t
        rw [dist_add_left, dist_eq_norm, ← sub_smul, norm_smul, Real.dist_eq, Real.norm_eq_abs,
          coe_nnNorm, mul_comm]
      have hRsub : R A ⊆ f '' Icc (-(2 * M / ‖(u : E)‖)) (2 * M / ‖(u : E)‖) := by
        rintro x ⟨hxs, hxA, -⟩
        have hmem : x - x0 ∈ linCone a A := by
          intro i hi
          have e1 : ⟪a i, x⟫ = b i := by
            have : i ∈ act a b x := by rw [hxA]; exact hi
            exact this
          have e2 : ⟪a i, x0⟫ = b i := by
            have : i ∈ act a b x0 := by rw [hx0A]; exact hi
            exact this
          rw [inner_sub_right, e1, e2, sub_self]
        obtain ⟨t, ht⟩ := hspan ⟨x - x0, hmem⟩
        have ht' : t • (u : E) = x - x0 := congrArg Subtype.val ht
        refine ⟨t, ?_, ?_⟩
        · have h1 : ‖x - x0‖ ≤ 2 * M := by
            calc ‖x - x0‖ ≤ ‖x‖ + ‖x0‖ := norm_sub_le _ _
              _ ≤ M + M := add_le_add (hM x hxs) (hM x0 hx0s)
              _ = 2 * M := by ring
          rw [← ht', norm_smul, Real.norm_eq_abs] at h1
          have h2 : |t| ≤ 2 * M / ‖(u : E)‖ := by
            rw [le_div_iff₀ hun]; exact h1
          exact abs_le.1 h2
        · change x0 + t • (u : E) = x
          rw [ht']; abel
      calc μH[1] (R A) ≤ μH[1] (f '' Icc (-(2 * M / ‖(u : E)‖)) (2 * M / ‖(u : E)‖)) :=
            measure_mono hRsub
        _ ≤ (‖(u : E)‖₊ : ENNReal) ^ (1 : ℝ) * μH[1] (Icc (-(2 * M / ‖(u : E)‖))
            (2 * M / ‖(u : E)‖)) :=
            hLip.hausdorffMeasure_image_le zero_le_one _
        _ < ⊤ := by
            apply ENNReal.mul_lt_top
            · exact ENNReal.rpow_lt_top_of_nonneg zero_le_one ENNReal.coe_ne_top
            · rw [hausdorffMeasure_real]; exact measure_Icc_lt_top
  exact ((measure_mono hsub).trans_lt (measure_biUnion_lt_top Set.finite_univ hR)).ne

/-- The points where an edge crosses the cutting plane have length zero. -/
lemma exc_null [Finite ι] (a : ι → E) (b : ι → ℝ) (c : E) (d : ℝ) :
    μH[1] {x | x ∈ sol a b ∧ ⟪c, x⟫ = d ∧ finrank ℝ (linCone a (act a b x)) = 1 ∧
      ¬ linCone a (act a b x) ≤ (ℝ ∙ c)ᗮ} = 0 := by
  classical
  let Xs : Set ι → Set E := fun A => {x | act a b x = A ∧ ⟪c, x⟫ = d ∧
    finrank ℝ (linCone a A) = 1 ∧ ¬ linCone a A ≤ (ℝ ∙ c)ᗮ}
  have hsub : {x | x ∈ sol a b ∧ ⟪c, x⟫ = d ∧ finrank ℝ (linCone a (act a b x)) = 1 ∧
      ¬ linCone a (act a b x) ≤ (ℝ ∙ c)ᗮ} ⊆ ⋃ A, Xs A := by
    rintro x ⟨-, h2, h3, h4⟩
    exact mem_iUnion.2 ⟨act a b x, rfl, h2, h3, h4⟩
  have hXs : ∀ A, μH[1] (Xs A) = 0 := by
    intro A
    have hss : (Xs A).Subsingleton := by
      rintro x ⟨hxA, hxd, hfr, hnot⟩ y ⟨hyA, hyd, -, -⟩
      have hmem : x - y ∈ linCone a A := by
        intro i hi
        have e1 : ⟪a i, x⟫ = b i := by
          have : i ∈ act a b x := by rw [hxA]; exact hi
          exact this
        have e2 : ⟪a i, y⟫ = b i := by
          have : i ∈ act a b y := by rw [hyA]; exact hi
          exact this
        rw [inner_sub_right, e1, e2, sub_self]
      obtain ⟨u, hu0, hspan⟩ := finrank_eq_one_iff'.1 hfr
      have huc : ⟪c, (u : E)⟫ ≠ 0 := by
        intro h0
        apply hnot
        intro w hw
        obtain ⟨s, hs⟩ := hspan ⟨w, hw⟩
        have hs' : s • (u : E) = w := congrArg Subtype.val hs
        rw [Submodule.mem_orthogonal_singleton_iff_inner_right, ← hs', inner_smul_right, h0,
            mul_zero]
      obtain ⟨t, ht⟩ := hspan ⟨x - y, hmem⟩
      have ht' : t • (u : E) = x - y := congrArg Subtype.val ht
      have h0 : ⟪c, x - y⟫ = 0 := by rw [inner_sub_right, hxd, hyd, sub_self]
      rw [← ht', inner_smul_right] at h0
      have ht0 : t = 0 := by
        rcases mul_eq_zero.1 h0 with h | h
        · exact h
        · exact absurd h huc
      rw [ht0, zero_smul] at ht'
      exact sub_eq_zero.1 ht'.symm
    rcases hss.eq_empty_or_singleton with he | ⟨x, he⟩
    · rw [he, measure_empty]
    · rw [he]
      have := nullSingletonClass_hausdorff E (d := 1) one_pos
      exact measure_singleton x
  exact measure_mono_null hsub (measure_iUnion_null_iff.2 hXs)

/-- **The core lemma: the Dehn invariant is additive under a plane cut.**
For a convex polytope `P` in 3-space and the plane `⟪c, x⟫ = d`, `c ≠ 0`:
`dehnSet P = dehnSet (P ∩ {⟪c,x⟫ ≤ d}) + dehnSet (P ∩ {⟪c,x⟫ ≥ d})`. -/
theorem dehnSet_cut [Fact (finrank ℝ E = 3)] {P : Set E} (hP : IsPoly P) (c : E) (d : ℝ)
    (hc : c ≠ 0) :
    dehnSet P = dehnSet (P ∩ hsLe c d) + dehnSet (P ∩ hsGe c d) := by
  classical
  obtain ⟨hb, ι, _, a, b, rfl⟩ := hP
  change tsum1 μH[1] (edgeAngle (sol a b)) =
    tsum1 μH[1] (edgeAngle (sol a b ∩ hsLe c d)) + tsum1 μH[1] (edgeAngle (sol a b ∩ hsGe c d))
  apply tsum1_add μH[1] (cls a b c d) (cls_meas a b c d)
  · intro x y hxy
    obtain ⟨h1, h2, h3, h4, -⟩ := cls_facts a b c d hxy
    exact edgeAngle_cut_congr a b c d h1 h2 h3 h4
  · intro x y hxy
    obtain ⟨h1, h2, -, h4, h5⟩ := cls_facts a b c d hxy
    refine edgeAngle_cut_congr a b (-c) (-d) h1 h2 ?_ ?_
    · rw [inner_neg_left, inner_neg_left, neg_le_neg_iff, neg_le_neg_iff]; exact h5
    · rw [inner_neg_left, inner_neg_left, neg_inj, neg_inj]; exact h4
  · rw [sol_inter_hsLe]
    apply support_finite
    rw [← sol_inter_hsLe]; exact hb.subset inter_subset_left
  · change μH[1] {x | edgeAngle (sol a b ∩ hsLe (-c) (-d)) x ≠ 0} ≠ ⊤
    rw [sol_inter_hsLe]
    apply support_finite
    rw [← sol_inter_hsLe]; exact hb.subset inter_subset_left
  · refine measure_mono_null ?_ (exc_null a b c d)
    intro x hx
    by_contra hno
    exact hx (edgeAngle_cut a b hc d x hno)

end DehnCanon.Library
