/-
Copyright (c) 2026 Jim Fowler, Dennis Sweeney. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jim Fowler, Dennis Sweeney
-/
module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Tactic


/-!
# ClassifyInterval

Supporting results for the classification of compact one-dimensional manifolds.
-/

@[expose] public section

namespace OneMfld

open Function
open Set

theorem ici_cap_iio_empty (y : Real) : (Ici y ∩ Iio y) = ∅ := by
    have h' : Ici y ∩ Iio y = Ico y y := rfl
    rw [h']
    simp only [lt_self_iff_false, not_false_eq_true, Ico_eq_empty]

theorem iic_cap_ioi_empty (y : Real) : (Iic y ∩ Ioi y) = ∅ := by
    have h' : Iic y ∩ Ioi y = Ioc y y := Iic_inter_Ioi
    rw [h']
    simp only [lt_self_iff_false, not_false_eq_true, Ioc_eq_empty]

theorem not_ici (U : Set Real) (y : Real) (hu : IsOpen U) : (Ici y ≠ U) := by
  by_contra h
  rw [←h] at hu
  have h''' : IsClosed (Ici y) := by
      apply isClosed_Ici
  have ho : IsOpen (Ici y)ᶜ
  · exact IsClosed.isOpen_compl
  have hr : IsPreconnected (univ : Set Real) := isPreconnected_univ
  let hr' := hr (Ici y) ((Ici y)ᶜ) hu ho
  have huniv : Ici y ∪ (Ici y)ᶜ = univ := union_compl_self (Ici y)
  rw [huniv] at hr'
  simp only [subset_refl, univ_inter, nonempty_Ici, compl_Ici, nonempty_Iio, forall_const] at hr'
  rw [ici_cap_iio_empty] at hr'
  apply Set.not_nonempty_empty
  exact hr'

theorem not_iic (U : Set Real) (y : Real) (hu : IsOpen U) : (Iic y ≠ U) := by
  by_contra h
  rw [←h] at hu
  have h''' : IsClosed (Iic y) := by
      apply isClosed_Iic
  have ho : IsOpen (Iic y)ᶜ
  · exact IsClosed.isOpen_compl
  have hr : IsPreconnected (univ : Set Real) := isPreconnected_univ
  let hr' := hr (Iic y) ((Iic y)ᶜ) hu ho
  have huniv : Iic y ∪ (Iic y)ᶜ = univ := union_compl_self (Iic y)
  rw [huniv] at hr'
  simp only [subset_refl, univ_inter, nonempty_Iic, compl_Iic, nonempty_Ioi, forall_const] at hr'
  rw [iic_cap_ioi_empty] at hr'
  apply Set.not_nonempty_empty
  exact hr'

lemma ioc_not_open (x y : Real) (hxy : x < y) : ¬ IsOpen (Ioc x y) := by
  have hu : (Ioc x y) ∪ (Iio y) = (Iic y)
  · ext p
    simp only [mem_union, mem_Ioc, mem_Iio, mem_Iic]
    apply Iff.intro
    · intro h
      rcases h with (h1|h2)
      · tauto
      · exact le_of_lt h2
    by_cases hp : p = y
    · intro h
      rw [hp]
      simp only [le_refl, and_true, lt_self_iff_false, or_false]
      exact hxy
    intro h
    right
    exact lt_of_le_of_ne h hp
  by_contra hopen
  have hopen' : IsOpen (Iio y) := isOpen_Iio
  have hopen'' : IsOpen (Iic y)
  · rw [←hu]
    exact IsOpen.union hopen hopen'
  have hc : IsOpen ((Iic y)ᶜ)
  · simp only [compl_Iic]
    exact isOpen_Ioi
  have hcon := isPreconnected_univ (Iic y) ((Iic y)ᶜ) hopen'' hc
               (by simp only [compl_Iic, Iic_union_Ioi, subset_refl])
               (by simp only [univ_inter, nonempty_Iic])
               (by simp only [compl_Iic, univ_inter, nonempty_Ioi])
  simp only [compl_Iic, univ_inter] at hcon
  rcases hcon with ⟨x,hx⟩
  simp at hx
  linarith

lemma ico_not_open (x y : Real) (hxy : x < y) : ¬ IsOpen (Ico x y) := by
  have hxy' : -y < -x := neg_lt_neg_iff.mpr hxy
  have hn := ioc_not_open (-y) (-x) hxy'
  let f : Real → Real := fun x => - x
  let fb : Bijective f := ⟨ neg_injective, neg_surjective ⟩
  let fe := Equiv.ofBijective f fb
  have fc : Continuous fe := continuous_neg
  have fo : IsOpenMap fe := isOpenMap_neg ℝ
  have fh : Homeomorph Real Real
  · apply Equiv.toHomeomorphOfContinuousOpen
    · exact fc
    exact fo
  by_contra h
  have p := fo (Ico x y) h
  have he : fe '' (Ico x y) = Ioc (-y) (-x)
  · ext t
    have ht : ∀ s : Real, fe.symm (-s) = s := fun s => Equiv.ofBijective_symm_apply_apply f fb s
    have ht' := ht (-t)
    simp only [neg_neg] at ht'
    simp only [mem_image_equiv, mem_Ico, mem_Ioc]
    apply Iff.intro
    · simp only [and_imp]
      intro h1 h2
      constructor
      · rw [ht'] at h1
        rw [ht'] at h2
        linarith
      rw [ht'] at h1
      rw [ht'] at h2
      linarith
    simp only [and_imp]
    intro h1 h2
    rw [ht']
    constructor
    · linarith
    linarith
  · rw [he] at p
    exact hn p

lemma icc_not_open (x y : Real) (hxy : x < y) : ¬ IsOpen (Icc x y) := by
  by_contra h
  have hc : IsClosed (Icc x y) := isClosed_Icc
  have hc'' : IsOpen ((Icc x y)ᶜ) := IsClosed.isOpen_compl
  have hcon := isPreconnected_univ (Icc x y) ((Icc x y)ᶜ) h hc''
               (by simp only [union_compl_self, subset_refl])
               (by simp only [univ_inter, nonempty_Icc]
                   linarith)
               (by simp only [univ_inter]
                   have hy : ((y + 1) ∈ (Icc x y)ᶜ)
                   · simp only [mem_compl_iff, mem_Icc, add_le_iff_nonpos_right, not_and, not_le,
                       zero_lt_one, implies_true]
                   exact nonempty_of_mem hy)
  simp only [inter_compl_self, inter_empty, Set.not_nonempty_empty] at hcon

lemma not_ioc (U : Set Real) (x y : Real) (hu : IsOpen U) (h : Ioc x y = U) : (U = ∅) := by
  by_cases hxy : (x < y)
  · have h' : ¬ IsOpen (Ioc x y)
    · apply ioc_not_open x y
      exact hxy
    exfalso
    apply h'
    rw [h]
    tauto
  · have h' : Ioc x y = ∅
    · exact Ioc_eq_empty hxy
    rw [h] at h'
    tauto

theorem not_ico (U : Set Real) (x y : Real) (hu : IsOpen U) (h : Ico x y = U) : (U = ∅) := by
  by_cases hxy : (x < y)
  · have h' : ¬ IsOpen (Ico x y)
    · apply ico_not_open x y
      exact hxy
    exfalso
    apply h'
    rw [h]
    tauto
  · have h' : Ico x y = ∅
    · exact Ico_eq_empty hxy
    rw [h] at h'
    tauto

theorem not_icc (U : Set Real) (x y : Real) (hu : IsOpen U) (h : Icc x y = U) : (U = ∅) := by
  by_cases hxy : (x < y)
  · have h' : ¬ IsOpen (Icc x y)
    · apply icc_not_open x y
      exact hxy
    exfalso
    apply h'
    rw [h]
    tauto
  · by_cases hyx : (x > y)
    · have h' : Icc x y = ∅
      · exact Icc_eq_empty_of_lt hyx
      rw [h] at h'
      exact h'
    · have hxy' : x ≥ y := le_of_not_gt hxy
      have hyx' : x ≤ y := by exact le_of_not_gt hyx
      have hxx : x = y
      · have hxy'' : (x = y) ∨ (y < x) := eq_or_gt_of_not_lt hxy
        have hyx'' : (x = y) ∨ (x < y) := by exact Or.symm (Decidable.lt_or_eq_of_le hyx')
        rcases hyx'' with (h|h)
        · exact h
        tauto
      rw [←hxx] at h
      simp only [Icc_self] at h
      rw [←h] at hu
      exfalso
      have c : ¬ IsOpen {x} := not_isOpen_singleton x
      tauto

theorem classify_intervals (U : Set Real) (hu : IsOpen U) (hc : IsPreconnected U) :
  (∃ x y, (Set.Ioo x y = U)) ∨
  (∃ (x : Real), (U = Set.Iio x)) ∨
  (∃ (x : Real), (Set.Ioi x = U)) ∨
  (U = univ) ∨ (U = ∅) := by
  have h : U ∈ (range (uncurry Icc)) ∪ range (uncurry Ico) ∪ range (uncurry Ioc) ∪ range
      (uncurry Ioo) ∪  (range Ici ∪ range Ioi ∪ range Iic ∪ range Iio ∪ {univ, ∅})
  · rw [←setOfPred_isPreconnected_eq_of_ordered]
    exact hc
  simp only [union_insert, union_singleton, mem_insert_iff, mem_union, mem_range, Prod.exists,
    uncurry_apply_pair] at h
  cases h
  case inl h => tauto
  case inr h =>
    cases h
    case inl h => tauto
    case inr h =>
      cases h
      case inr h =>
        cases h
        case inl h =>
          cases h
          case inr h => by_contra
                        rcases h with ⟨ x', hx ⟩
                        apply not_iic
                        · exact hu
                        exact hx
          case inl h =>
            cases h
            case inr h => right; right; left; assumption
            case inl h => by_contra
                          rcases h with ⟨ x', hx ⟩
                          apply not_ici
                          · exact hu
                          exact hx
        case inr h => tauto
      case inl h =>
        cases h
        case inr h => left; tauto
        case inl h =>
          cases h
          case inl h =>
            cases h
            case inl h => rcases h with ⟨ x, y, hx ⟩
                          right; right; right; right
                          apply not_icc
                          · exact hu
                          exact hx
            case inr h => rcases h with ⟨ x, y, hx ⟩
                          right; right; right; right
                          apply not_ico
                          · exact hu
                          exact hx
          case inr h => rcases h with ⟨ x, y, hx ⟩
                        right
                        right
                        right
                        right
                        apply not_ioc
                        · exact hu
                        exact hx

/-- Select disjuncts repeatedly to reduce a nested disjunction to one of its branches. -/
macro "solveDisj" : tactic => `(tactic| repeat (apply Or.inl <|> apply Or.inr))

theorem classify_connected_interval (U : Set Real) (hu : IsOpen U) (hc : IsConnected U) :
  (∃ x y, (Set.Ioo x y = U)) ∨
  (∃ (x : Real), (U = Set.Iio x)) ∨
  (∃ (x : Real), (Set.Ioi x = U)) ∨
  (U = univ) := by
    have hpc : IsPreconnected U := by exact IsConnected.isPreconnected hc
    have hi := classify_intervals U hu hpc
    have ho : ¬ (U = ∅) := by
      by_contra hn
      rw [hn] at hc
      have he : (∅ : Set Real).Nonempty := IsConnected.nonempty hc
      exact Set.not_nonempty_empty he
    rcases hi with (h|h|h|h|h)
    · left; assumption
    · right; left; assumption
    · right; right; left; assumption
    · right; right; right; assumption
    exfalso
    exact ho h

/-- The logarithm homeomorphism from positive nonnegative reals to the real line. -/
noncomputable def homeoNnrealReal : (Set.Ioi 0 : Set NNReal) ≃ₜ (Set.univ : Set Real) where
  toFun := fun ⟨x,_⟩ => ⟨ Real.log x, trivial ⟩
  invFun := fun ⟨x,_⟩ => ⟨ NNReal.mk (Real.exp x) (Real.exp_nonneg x), Real.exp_pos x ⟩
  left_inv := fun ⟨ ⟨ x, nn ⟩, p ⟩  => by
    ext
    simp only [NNReal.coe_mk]
    exact Real.exp_log p
  right_inv := fun x => by
    simp only [NNReal.coe_mk, Real.log_exp, Subtype.coe_eta]
  continuous_toFun := by
    simp only
    refine Continuous.subtype_mk ?_ fun x => trivial
    refine Continuous.log ?_ ?_
    · exact Isometry.continuous fun x1 => congrFun rfl
    intro x
    rcases x with ⟨x,hx⟩
    simp only [ne_eq, NNReal.coe_eq_zero]
    exact pos_iff_ne_zero.mp hx
  continuous_invFun := by
    simp only
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    apply Continuous.rexp
    exact continuous_subtype_val

/-- Compatibility name for Mathlib's truncation to the nonnegative reals. -/
abbrev relu : ℝ → NNReal := Real.toNNReal

lemma relu_zero : relu 0 = 0 := Real.toNNReal_zero

theorem continuous_relu : Continuous relu := continuous_real_toNNReal

lemma proj_relu {x : ℝ} (h : x > 0) : (relu x).toReal = x :=
  Real.coe_toNNReal x h.le

lemma proj_relu' {x : ℝ} (h : x ≤ 0) : (relu x).toReal = 0 := by
  rw [relu, Real.toNNReal_of_nonpos h, NNReal.coe_zero]

lemma relu_proj {x : NNReal} : relu x.toReal = x := Real.toNNReal_coe

lemma relu_mono : StrictMonoOn relu (Set.Ici 0) := by
  intro x hx y hy h
  exact_mod_cast (show ((relu x : NNReal) : ℝ) < ((relu y : NNReal) : ℝ) by
    simpa only [relu, Real.coe_toNNReal x hx, Real.coe_toNNReal y hy] using h)

lemma relu_interval_ioo {U : Set NNReal} {a b : Real} (h : Ioo a b = relu ⁻¹' U) :
  (relu '' (Set.Ioo a b) = U) := by
  apply subset_antisymm
  · rintro _ ⟨y, hy, rfl⟩
    rw [h] at hy
    exact hy
  · intro x hx
    refine ⟨(x : ℝ), ?_, relu_proj⟩
    rw [h]
    simpa only [mem_preimage, relu_proj] using hx

theorem StrictMonoOn.injOn_Ioo {α : Type u_1} {β : Type u_2} {f : α → β}
  [LinearOrder α] [LinearOrder β] {a : α} {b : α} (h : StrictMonoOn f (Set.Icc a b)) :
  InjOn f (Set.Ioo a b) := by
  exact (h.mono Ioo_subset_Icc_self).injOn

lemma relu_ioo (a b : Real) :
  (relu '' (Set.Ioo a b) = Set.Ioo (relu a) (relu b)) ∨
  (relu '' (Set.Ioo a b) = Set.Ico 0 (relu b)) ∨
  (relu '' (Set.Ioo a b) = { 0 }) ∨
  (relu '' (Set.Ioo a b) = ∅) := by
  by_cases ha : a > 0
  · by_cases hb : b > 0
    · left
      ext z
      simp only [mem_image, mem_Ioo]
      constructor
      · intro ⟨ x, ⟨ hx, hxz ⟩ ⟩
        have hax : relu a < relu x := by
          apply NNReal.coe_lt_coe.mp
          rw [proj_relu]
          · rw [proj_relu]
            · exact hx.1
            linarith
          linarith
        have hxb : relu x < relu b := by
          apply NNReal.coe_lt_coe.mp
          rw [proj_relu]
          · rw [proj_relu]
            · exact hx.2
            linarith
          linarith
        rw [hxz] at hax
        rw [hxz] at hxb
        exact ⟨hax, hxb⟩
      · intro ⟨ haz, hzb ⟩
        use z
        rw [relu_proj]
        simp only [and_true]
        have haz' : NNReal.toReal (relu a) < NNReal.toReal z := by exact haz
        have hzb' : NNReal.toReal z < NNReal.toReal (relu b) := by exact hzb
        rw [proj_relu] at hzb'
        · rw [proj_relu] at haz'
          · exact ⟨haz', hzb'⟩
          exact ha
        exact hb
    · have : Ioo a b = ∅ := by
        ext z
        simp only [mem_Ioo, mem_empty_iff_false, iff_false, not_and, not_lt]
        intro ha
        linarith
      rw [this]
      simp only [image_empty]
      simp only [or_true]
  · by_cases hb : b > 0
    · by_cases ha0 : a = 0
      · rw [ha0]
        left
        ext z
        simp only [mem_image, mem_Ioo]
        apply Iff.intro
        · intro ⟨ y, ⟨ h0y, hyb ⟩, hyz ⟩
          rw [←hyz]
          apply And.intro
          · rw [relu_zero]
            have : 0 < NNReal.toReal (relu y) := by
              rw [proj_relu]
              · assumption
              linarith
            simp only [gt_iff_lt]
            exact this
          · have : NNReal.toReal (relu y) < NNReal.toReal (relu b) := by
              rw [proj_relu]
              · rw [proj_relu]
                · assumption
                linarith
              linarith
            exact this
        · intro ⟨ h0z, hzb ⟩
          use z.toReal
          apply And.intro
          · apply And.intro
            · simp only [NNReal.coe_pos]
              exact pos_of_gt h0z
            · have : NNReal.toReal z < NNReal.toReal (relu b) := by exact hzb
              exact Real.lt_toNNReal_iff_coe_lt.mp hzb
          · exact relu_proj
      · right; left
        ext z
        simp only [mem_image, mem_Ioo, mem_Ico, zero_le, true_and]
        apply Iff.intro
        · intro ⟨ y, ⟨ hay, hyb ⟩ , hyz ⟩
          rw [←hyz]
          dsimp [relu, Real.toNNReal]
          simp only [gt_iff_lt]
          refine NNReal.coe_lt_coe.mp ?_
          simp only [NNReal.coe_mk, lt_sup_iff, sup_lt_iff, lt_self_iff_false, and_false, or_false]
          apply And.intro <;> linarith
        · intro hzb
          use NNReal.toReal z
          apply And.intro
          · apply And.intro
            · have ha0' : a < 0 := by
                simp only [gt_iff_lt, not_lt] at ha
                exact lt_of_le_of_ne ha ha0
              have h0z : 0 ≤ (relu z) := by exact zero_le
              have h0z' : a < relu z := by exact lt_of_le_of_lt' h0z ha0'
              rw [relu_proj] at h0z'
              assumption
            · have : NNReal.toReal z < NNReal.toReal (relu b) := by exact hzb
              rw [proj_relu] at this
              · assumption
              assumption
          · rw [relu_proj]
    · by_cases hab : a ≥ b
      · have : Ioo a b = ∅ := by
          exact Ioo_eq_empty_of_le hab
        rw [this]
        simp only [image_empty, or_true]
      · right; right; left
        ext z
        simp only [mem_image, mem_Ioo, mem_singleton_iff]
        constructor
        · rintro ⟨ y, hy, hyz ⟩
          have : y ≤ 0 := by linarith
          have h' := proj_relu' this
          rw [hyz] at h'
          exact NNReal.coe_eq_zero.mp h'
        · intro hz
          have hab' : a < b := by linarith
          use (a + b) / 2
          apply And.intro
          · apply And.intro
            · exact left_lt_add_div_two.mpr hab'
            · exact add_div_two_lt_right.mpr hab'
          · have hn : (a + b) / 2 ≤ 0 := by linarith
            rw [hz]
            apply NNReal.coe_eq_zero.mp
            exact proj_relu' hn

lemma relu_iio (b : Real) :
  ((relu '' (Set.Iio b) = Set.Ico 0 (relu b)) ∨
  (relu '' (Set.Iio b) = { 0 })) := by
    by_cases hb : b > 0
    · left
      ext z
      simp only [mem_image, mem_Iio, mem_Ico, zero_le, true_and]
      apply Iff.intro
      · intro ⟨ x, ⟨  hxb, hxz ⟩ ⟩
        rw [←hxz]
        simp only [gt_iff_lt]
        dsimp [relu, Real.toNNReal]
        apply NNReal.coe_lt_coe.mp
        simp only [NNReal.coe_mk, lt_sup_iff, sup_lt_iff, lt_self_iff_false, and_false, or_false]
        apply And.intro
        · assumption
        · assumption
      · intro hzb
        use z.1
        apply And.intro
        · exact Nonneg.toNonneg_lt.mp hzb
        · have : z ≥ 0 := by exact zero_le
          simp only [NNReal.val_eq_coe]
          exact relu_proj
    · right
      ext z
      simp only [mem_image, mem_Iio, mem_singleton_iff]
      apply Iff.intro
      · intro ⟨ x, ⟨ hxb, hxz ⟩ ⟩
        have : x ≤ 0 := by linarith
        have hn := proj_relu' this
        rw [hxz] at hn
        exact NNReal.coe_eq_zero.mp hn
      · intro hz
        use b - 1
        simp only [sub_lt_self_iff, zero_lt_one, true_and]
        have : b - 1 ≤ 0 := by linarith
        have hn := proj_relu' this
        rw [hz]
        simp only [NNReal.coe_eq_zero] at hn
        assumption

lemma relu_univ : (relu '' univ = univ) := by
  ext z
  simp only [image_univ, mem_range, mem_univ, iff_true]
  use z.1
  apply relu_proj

lemma relu_ioi (b : Real) :
  ((relu '' (Set.Ioi b) = Set.Ioi (relu b)) ∨
  (relu '' (Set.Ioi b) = univ)) := by
  by_cases hb : b > 0
  · left
    ext z
    simp only [mem_image, mem_Ioi]
    apply Iff.intro
    · intro ⟨ x, ⟨ hbx, hxz ⟩ ⟩
      rw [←hxz]
      apply NNReal.coe_lt_coe.mp
      rw [proj_relu, proj_relu]
      · linarith
      · linarith
      linarith
    · intro hbz
      use z.1
      apply And.intro
      · simp only [NNReal.val_eq_coe]
        refine (Real.toNNReal_lt_iff_lt_coe ?_).mp hbz
        linarith
      · apply relu_proj
  · by_cases hb' : b = 0
    · left
      rw [hb']
      ext z
      simp only [mem_image, mem_Ioi]
      apply Iff.intro
      · intro ⟨ x, ⟨ hbx, hxz ⟩ ⟩
        rw [relu_zero]
        rw [←hxz]
        apply NNReal.coe_pos.mp
        rw [proj_relu]
        · assumption
        assumption
      · intro hz
        use z.1
        apply And.intro
        · rw [relu_zero] at hz
          exact hz
        apply relu_proj
    · right
      ext z
      simp only [mem_image, mem_Ioi, mem_univ, iff_true]
      use z.1
      simp only [NNReal.val_eq_coe]
      apply And.intro
      · have : 0 ≤ NNReal.toReal z := by exact NNReal.zero_le_coe
        have this' : b < 0 := by
          simp only [gt_iff_lt, not_lt] at hb
          exact lt_of_le_of_ne hb hb'
        exact lt_of_le_of_lt' this this'
      · exact relu_proj

lemma a_and_b (U : Set NNReal) (ε : Real) (εpos : ε > 0) (A : Set NNReal) (B : Set NNReal)
    (openA : IsOpen A) (openB : IsOpen B)
                (hp : IsPreconnected U)
                (interval : Set NNReal)
                (interval_def : interval = Set.Ioo (0 : NNReal) (NNReal.mk ε (by linarith)))
                (h1' : interval ⊆ A ∪ B)
                (empty : ¬ (interval ∩ B).Nonempty)
                (hA : (U \ {0} ∩ A).Nonempty) (hB : (U \ {0} ∩ B).Nonempty)
                (hAB : U \ {0} ⊆ A ∪ B) : (U \ {0} ∩ (A ∩ B)).Nonempty := by
        let interval' := Set.Iio (NNReal.mk ε (by linarith))
        let A' := A ∪ interval'
        have openA' : IsOpen A' := by
          apply IsOpen.union openA
          exact isOpen_Iio
        let B' := B ∩ Set.Ioi 0
        have openB' : IsOpen B' := by
          exact IsOpen.inter openB isOpen_Ioi
        specialize hp A' B' openA' openB'
        have h1 : U ⊆ A' ∪ B' := by
          intro x hx
          by_cases h0' : x = 0
          · rw [h0']
            simp only [mem_union]
            left
            exact mem_union_right A εpos
          · have : x ∈ U \ { 0 } := by exact mem_sdiff_of_mem hx h0'
            specialize hAB this
            simp only [mem_union]
            rcases hAB with (hAB|hAB)
            · left
              exact mem_union_left interval' hAB
            · right
              apply (mem_inter_iff x B (Ioi 0)).mpr
              apply And.intro
              · assumption
              · apply mem_Ioi.mpr
                exact pos_iff_ne_zero.mpr h0'
        have h2 : (U ∩ A').Nonempty := by
          rcases hA with ⟨ x, hx ⟩
          use x
          simp only [mem_inter_iff]
          apply And.intro
          · have : x ∈ U \ {0} := by exact mem_of_mem_inter_left hx
            exact mem_of_mem_sdiff this
          · apply (mem_union x A interval').mpr
            left
            exact mem_of_mem_inter_right hx
        have h3 : (U ∩ B').Nonempty := by
          rcases hB with ⟨ x, hx ⟩
          use x
          simp only [mem_inter_iff]
          apply And.intro
          · have : x ∈ U \ { 0 } := by exact mem_of_mem_inter_left hx
            exact mem_of_mem_sdiff this
          · apply (mem_inter_iff x B (Ioi 0)).mpr
            apply And.intro
            · exact mem_of_mem_inter_right hx
            · apply mem_Ioi.mpr
              have : x ∈ U \ { 0 } := by exact mem_of_mem_inter_left hx
              have this' : x ∉ ({ 0 } : Set NNReal) := by exact notMem_of_mem_sdiff this
              exact pos_iff_ne_zero.mpr this'
        specialize hp h1 h2 h3
        rcases hp with ⟨ x, hx ⟩
        use x
        simp only [mem_inter_iff, mem_sdiff, mem_singleton_iff]
        have hn0 : x ≠ 0 := by
          have : x ∈ A' ∩ B' := by exact mem_of_mem_inter_right hx
          have : x ∈ B' := by exact mem_of_mem_inter_right this
          have : x ∈ Set.Ioi 0 := by exact mem_of_mem_inter_right this
          exact pos_iff_ne_zero.mp this
        apply And.intro
        · apply And.intro
          · exact mem_of_mem_inter_left hx
          · exact hn0
        · apply And.intro
          · have : x ∈ A' ∩ B' := by exact mem_of_mem_inter_right hx
            have : x ∈ A' := by exact mem_of_mem_inter_left this
            simp only [A'] at this
            rcases this with (this|this)
            · assumption
            · have hi : x ∈ interval := by
                rw [interval_def]
                simp only [mem_Ioo]
                dsimp [interval'] at this
                simp only [mem_Iio] at this
                apply And.intro
                · exact pos_iff_ne_zero.mpr hn0
                · exact this
              have this' := h1' hi
              rcases this' with (this'|this')
              · assumption
              · exfalso
                apply empty
                use x
                exact mem_inter hi this'
          · have : x ∈ A' ∩ B' := by exact mem_of_mem_inter_right hx
            have : x ∈ B' := by exact mem_of_mem_inter_right this
            exact mem_of_mem_inter_left this

lemma remove_zero_connected (U : Set NNReal) (h0 : 0 ∈ U) (hu : IsOpen U) (hc : IsConnected U) :
  IsConnected (U \ {0}) := by
  rcases Metric.isOpen_iff.mp hu 0 h0 with ⟨ ε, εpos, hε ⟩
  dsimp [IsConnected]
  apply And.intro
  · let ε' : NNReal := NNReal.mk (ε/2) (by linarith)
    have : ε' ∈ Metric.ball 0 ε := by
      simp only [Metric.mem_ball]
      dsimp [ε']
      have hd : dist ε' 0 = ε/2 := by
        rw [NNReal.dist_eq]
        simp only [ε', NNReal.coe_mk, NNReal.coe_zero, sub_zero]
        exact abs_of_nonneg (by linarith)
      rw [hd]
      simp only [half_lt_self_iff, gt_iff_lt]
      linarith
    use ε'
    apply mem_sdiff_singleton.mpr
    apply And.intro
    · exact hε this
    · apply NNReal.coe_ne_zero.mp
      simp only [ne_eq, NNReal.coe_eq_zero]
      dsimp [ε']
      apply NNReal.coe_ne_zero.mp
      simp only [NNReal.coe_mk, ne_eq, div_eq_zero_iff, OfNat.ofNat_ne_zero, or_false]
      exact ne_of_gt εpos
  · have hset : U \ {0} = U ∩ Ioi 0 := by
      ext x
      simp only [mem_sdiff, mem_singleton_iff, mem_inter_iff, mem_Ioi,
        pos_iff_ne_zero]
    rw [hset]
    exact (hc.isPreconnected.ordConnected.inter ordConnected_Ioi).isPreconnected

lemma zero_in_open (a b : NNReal) (h : IsOpen ((Ioo a b) ∪ {0})) : a ≤ 0 ∧ 0 < b := by
  by_contra h'
  simp only [nonpos_iff_eq_zero, not_and, not_lt] at h'
  by_cases ha : a = 0
  · specialize h' ha
    rw [ha] at h
    rw [h'] at h
    simp only [lt_self_iff_false, not_false_eq_true, Ioo_eq_empty, union_singleton,
      insert_empty_eq] at h
    have : ¬ IsOpen ({ 0 } : Set NNReal) := not_isOpen_singleton 0
    apply this
    assumption
  · let U := Set.Iio (a / 2)
    have openU : IsOpen U := by exact isOpen_Iio
    let U' := U ∩ (Ioo a b ∪ {0})
    let openU' : IsOpen U' := by exact IsOpen.inter openU h
    have U0 : U' = { 0 } := by
      ext x
      simp only [mem_singleton_iff]
      apply Iff.intro
      · intro hx
        dsimp [U, U'] at hx
        simp only [union_singleton, mem_inter_iff, mem_Iio, mem_insert_iff, mem_Ioo] at hx
        have hx1 := hx.1
        have hx2 := hx.2
        rcases hx2 with (hx2|hx2)
        · exact hx2
        · have : a < x := hx2.1
          exfalso
          have this' : a < a / 2 := by exact gt_trans hx1 this
          have this'' : a.toReal < a.toReal / 2 := by exact this'
          have this3 : 0 ≤ a.toReal := by exact NNReal.zero_le_coe
          linarith
      · intro hx
        dsimp [U, U']
        simp only [union_singleton, mem_inter_iff, mem_Iio, mem_insert_iff, mem_Ioo]
        apply And.intro
        · rw [hx]
          have : 0 < a := by exact pos_iff_ne_zero.mpr ha
          exact half_pos this
        · left; assumption
    have : ¬ IsOpen ({ 0 } : Set NNReal) := not_isOpen_singleton 0
    apply this
    rwa [U0] at openU'

theorem classify_connected_nnreal_interval (U : Set NNReal) (hu : IsOpen U) (hc : IsConnected U) :
  (∃ x y, (Set.Ioo x y = U)) ∨
  (∃ (x : NNReal), (Set.Iio x = U)) ∨
  (∃ (x : NNReal), (Set.Ioi x = U)) ∨
  (U = univ) := by
  have hzeroInterval : Ici (0 : NNReal) = univ := by
    ext x
    simp only [mem_Ici, zero_le, mem_univ]
  have h := hc.isPreconnected.mem_intervals
  simp only [mem_insert_iff, mem_singleton_iff] at h
  rcases h with h | h | h | h | h | h | h | h | h | h
  · have hi := (congrArg interior h).symm.trans hu.interior_eq
    rw [← Ici_inter_Iic, interior_inter, interior_Iic] at hi
    by_cases hzero : sInf U = 0
    · exact Or.inr (Or.inl ⟨sSup U, by simpa only [hzero, hzeroInterval, interior_univ,
        univ_inter] using hi⟩)
    · rw [interior_Ici' ⟨0, pos_iff_ne_zero.mpr hzero⟩, Ioi_inter_Iio] at hi
      exact Or.inl ⟨sInf U, sSup U, hi⟩
  · have hi := (congrArg interior h).symm.trans hu.interior_eq
    rw [← Ici_inter_Iio, interior_inter, interior_Iio] at hi
    by_cases hzero : sInf U = 0
    · exact Or.inr (Or.inl ⟨sSup U, by simpa only [hzero, hzeroInterval, interior_univ,
        univ_inter] using hi⟩)
    · rw [interior_Ici' ⟨0, pos_iff_ne_zero.mpr hzero⟩, Ioi_inter_Iio] at hi
      exact Or.inl ⟨sInf U, sSup U, hi⟩
  · have hi := (congrArg interior h).symm.trans hu.interior_eq
    rw [interior_Ioc] at hi
    exact Or.inl ⟨sInf U, sSup U, hi⟩
  · exact Or.inl ⟨sInf U, sSup U, h.symm⟩
  · have hi := (congrArg interior h).symm.trans hu.interior_eq
    by_cases hzero : sInf U = 0
    · exact Or.inr (Or.inr (Or.inr (by simpa only [hzero, hzeroInterval,
        interior_univ] using hi.symm)))
    · rw [interior_Ici' ⟨0, pos_iff_ne_zero.mpr hzero⟩] at hi
      exact Or.inr (Or.inr (Or.inl ⟨sInf U, hi⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨sInf U, h.symm⟩))
  · have hi := (congrArg interior h).symm.trans hu.interior_eq
    rw [interior_Iic] at hi
    exact Or.inr (Or.inl ⟨sSup U, hi⟩)
  · exact Or.inr (Or.inl ⟨sSup U, h.symm⟩)
  · exact Or.inr (Or.inr (Or.inr h))
  · exact (hc.nonempty.ne_empty h).elim

end OneMfld
