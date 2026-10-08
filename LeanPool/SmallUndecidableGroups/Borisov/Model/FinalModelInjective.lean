/-
Copyright (c) 2026 Qiuyu Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Marc Kegel, Shana Yunsheng Li, Qiuyu Ren
-/

module

public import LeanPool.SmallUndecidableGroups.Borisov.Model.FinalModel
public import LeanPool.SmallUndecidableGroups.Borisov.Model.G0HNN

/-! The already-verified four-relator HNN model supplies the first two
HNN stages.  We only have to map its four-generator presentation into the
first four generators of Borisov's full presentation. -/

@[expose] public section

namespace Undecidability

open CommutatorLemmas

namespace BorisovFinalModelInjective

open BorisovCStage
open BorisovConverseCore
open BorisovFinalModel
open BorisovG0HNN
open BorisovHNNModel
open HNNLemmas

noncomputable section

variable (datum : Thue.StandingDatum) (hfree : RankFiveFree datum)

/-- The group defined by Borisov’s fourteen-relator presentation. -/
abbrev Presented : Type := (Borisov.presentation datum).Group

/-- The seven generators of Borisov’s presented group. -/
def presentedGenerator : Fin 7 → Presented datum :=
  PresentedGroup.of

private theorem full_relator_eq_one (i : Fin 14) :
    Word.eval (presentedGenerator datum)
        ((Borisov.presentation datum).relator i) = 1 := by
  simpa [FP.evalWord, presentedGenerator] using
    (Borisov.presentation datum).relator_eq_one i

/-- The four generators of the initial Borisov stage, interpreted in the full presentation. -/
def g0Generator : Fin 4 → Presented datum :=
  ![presentedGenerator datum 0, presentedGenerator datum 1,
    presentedGenerator datum 2, presentedGenerator datum 3]

theorem g0_relators :
    ∀ r ∈ BorisovIntersections.presentation.relSet,
      FreeGroup.lift (g0Generator datum) r = 1 := by
  rintro r ⟨i, rfl⟩
  fin_cases i
  · change Word.eval (g0Generator datum)
      (BorisovIntersections.presentation.relator 0) = 1
    simpa [BorisovIntersections.presentation, Borisov.presentation,
      BorisovIntersections.sDRelator, Borisov.sDRelator,
      BorisovIntersections.dWord, BorisovIntersections.s1Word,
      Borisov.dWord, Borisov.s1Word, g0Generator] using
      full_relator_eq_one datum 0
  · change Word.eval (g0Generator datum)
      (BorisovIntersections.presentation.relator 1) = 1
    simpa [BorisovIntersections.presentation, Borisov.presentation,
      BorisovIntersections.sERelator, Borisov.sERelator,
      BorisovIntersections.eWord, BorisovIntersections.s1Word,
      Borisov.eWord, Borisov.s1Word, g0Generator] using
      full_relator_eq_one datum 1
  · change Word.eval (g0Generator datum)
      (BorisovIntersections.presentation.relator 2) = 1
    simpa [BorisovIntersections.presentation, Borisov.presentation,
      BorisovIntersections.sDRelator, Borisov.sDRelator,
      BorisovIntersections.dWord, BorisovIntersections.s2Word,
      Borisov.dWord, Borisov.s2Word, g0Generator] using
      full_relator_eq_one datum 2
  · change Word.eval (g0Generator datum)
      (BorisovIntersections.presentation.relator 3) = 1
    simpa [BorisovIntersections.presentation, Borisov.presentation,
      BorisovIntersections.sERelator, Borisov.sERelator,
      BorisovIntersections.eWord, BorisovIntersections.s2Word,
      Borisov.eWord, Borisov.s2Word, g0Generator] using
      full_relator_eq_one datum 3

/-- The homomorphism from the initial four-generator presentation to the full presentation. -/
def g0ToPresented : BorisovIntersections.G0 →* Presented datum :=
  PresentedGroup.toGroup (g0_relators datum)

@[simp] private theorem g0ToPresented_of (i : Fin 4) :
    g0ToPresented datum (PresentedGroup.of i) = g0Generator datum i := by
  simp [g0ToPresented]

/-- Reverse map from the semantic two-stable-letter group `Gamma3` to the
full Borisov presentation. -/
def gamma3ToPresented : Gamma3 →* Presented datum :=
  (g0ToPresented datum).comp BorisovG0HNN.fromHNN

@[simp] theorem gamma3ToPresented_d3 :
    gamma3ToPresented datum d3 = presentedGenerator datum 0 := by
  rw [gamma3ToPresented, MonoidHom.comp_apply,
    show d3 = BorisovG0HNN.hnnD from rfl,
    BorisovG0HNN.fromHNN_hnnD]
  simp [BorisovG0HNN.presentedD, BorisovIntersections.d,
    BorisovIntersections.evalWord, BorisovIntersections.dWord,
    FP.evalWord, g0Generator, presentedGenerator]

@[simp] theorem gamma3ToPresented_e3 :
    gamma3ToPresented datum e3 = presentedGenerator datum 1 := by
  rw [gamma3ToPresented, MonoidHom.comp_apply,
    show e3 = BorisovG0HNN.hnnE from rfl,
    BorisovG0HNN.fromHNN_hnnE]
  simp [BorisovG0HNN.presentedE, BorisovIntersections.e,
    BorisovIntersections.evalWord, BorisovIntersections.eWord,
    FP.evalWord, g0Generator, presentedGenerator]

@[simp] theorem gamma3ToPresented_s1_3 :
    gamma3ToPresented datum firstStableInStageThree = presentedGenerator datum 2 := by
  rw [gamma3ToPresented, MonoidHom.comp_apply,
    show firstStableInStageThree = BorisovG0HNN.hnnS1 from rfl,
    BorisovG0HNN.fromHNN_hnnS1]
  simp [BorisovG0HNN.presentedS1, BorisovIntersections.evalWord,
    BorisovIntersections.s1Word, FP.evalWord, g0Generator,
    presentedGenerator]

@[simp] theorem gamma3ToPresented_s2_3 :
    gamma3ToPresented datum secondStableInStageThree = presentedGenerator datum 3 := by
  rw [gamma3ToPresented, MonoidHom.comp_apply,
    show secondStableInStageThree = BorisovG0HNN.hnnS2 from rfl,
    BorisovG0HNN.fromHNN_hnnS2]
  simp [BorisovG0HNN.presentedS2, BorisovIntersections.evalWord,
    BorisovIntersections.s2Word, FP.evalWord, g0Generator,
    presentedGenerator]

@[simp] theorem gamma3ToPresented_positive3 (w : List (Fin 2)) :
    gamma3ToPresented datum (positive3 w) =
      Thue.evalPositive (presentedGenerator datum 2)
        (presentedGenerator datum 3) w := by
  simp only [positive3, Thue.evalPositive, map_list_prod, List.map_map]
  induction w with
  | nil => rfl
  | cons i w ih =>
      simp only [List.map_cons, List.prod_cons]
      rw [ih]
      fin_cases i <;> simp

private theorem presented_c_commutes_stable (beta : Fin 2) :
    Commute (presentedGenerator datum (if beta = 0 then 2 else 3))
      (presentedGenerator datum 4) := by
  fin_cases beta
  · have h := full_relator_eq_one datum 4
    have h' :
        (presentedGenerator datum 2)⁻¹ *
            (presentedGenerator datum 4)⁻¹ *
            presentedGenerator datum 2 * presentedGenerator datum 4 = 1 := by
      simpa [Borisov.presentation, Borisov.s1Word, Borisov.cWord] using h
    simpa using (inverse_commutator_eq_one_iff_commute _ _).mp h'
  · have h := full_relator_eq_one datum 5
    have h' :
        (presentedGenerator datum 3)⁻¹ *
            (presentedGenerator datum 4)⁻¹ *
            presentedGenerator datum 3 * presentedGenerator datum 4 = 1 := by
      simpa [Borisov.presentation, Borisov.s2Word, Borisov.cWord] using h
    simpa using (inverse_commutator_eq_one_iff_commute _ _).mp h'

private theorem presented_c_conjugates_stable (beta : Fin 2) :
    (presentedGenerator datum 4)⁻¹ *
        presentedGenerator datum (if beta = 0 then 2 else 3) *
        presentedGenerator datum 4 =
      presentedGenerator datum (if beta = 0 then 2 else 3) := by
  have h := presented_c_commutes_stable datum beta
  calc
    (presentedGenerator datum 4)⁻¹ *
          presentedGenerator datum (if beta = 0 then 2 else 3) *
          presentedGenerator datum 4 =
        (presentedGenerator datum 4)⁻¹ *
          (presentedGenerator datum (if beta = 0 then 2 else 3) *
            presentedGenerator datum 4) := by simp [mul_assoc]
    _ = (presentedGenerator datum 4)⁻¹ *
          (presentedGenerator datum 4 *
            presentedGenerator datum (if beta = 0 then 2 else 3)) := by
          rw [h.eq]
    _ = presentedGenerator datum (if beta = 0 then 2 else 3) := by simp

private theorem presented_c_simulation (i : Fin 3) :
    (presentedGenerator datum 4)⁻¹ *
        presentedGenerator datum 0 ^ (i.val + 1) *
        Thue.evalPositive (presentedGenerator datum 2)
          (presentedGenerator datum 3) (datum.F i) *
        presentedGenerator datum 1 ^ (i.val + 1) *
        presentedGenerator datum 4 =
      presentedGenerator datum 0 ^ (i.val + 1) *
        Thue.evalPositive (presentedGenerator datum 2)
          (presentedGenerator datum 3) (datum.E i) *
        presentedGenerator datum 1 ^ (i.val + 1) := by
  have hrel : Word.eval (presentedGenerator datum)
      (Borisov.simulationRelator datum i) = 1 := by
    fin_cases i
    · simpa [Borisov.presentation] using full_relator_eq_one datum 6
    · simpa [Borisov.presentation] using full_relator_eq_one datum 7
    · simpa [Borisov.presentation] using full_relator_eq_one datum 8
  rw [Borisov.simulationRelator, Word.eval_relation_eq_one_iff] at hrel
  simpa [Borisov.dWord, Borisov.eWord, Borisov.cWord, mul_assoc] using hrel

private theorem presented_c_conjugates_basis (q : RuleBasis) :
    (presentedGenerator datum 4)⁻¹ *
        gamma3ToPresented datum (uBasis datum q) *
        presentedGenerator datum 4 =
      gamma3ToPresented datum (vBasis datum q) := by
  cases q with
  | inl betaIndex =>
      fin_cases betaIndex
      · simpa [uBasis, vBasis, stable3] using
          presented_c_conjugates_stable datum (0 : Fin 2)
      · simpa [uBasis, vBasis, stable3] using
          presented_c_conjugates_stable datum (1 : Fin 2)
  | inr i =>
      simpa [uBasis, vBasis, a3, b3, map_mul, map_pow, mul_assoc] using
        presented_c_simulation datum i

private theorem presented_c_conjugates_uLift
    (x : FreeGroup RuleBasis) :
    (presentedGenerator datum 4)⁻¹ *
        gamma3ToPresented datum (uLift datum x) *
        presentedGenerator datum 4 =
      gamma3ToPresented datum (vLift datum x) := by
  have heq :
      (MulAut.conj (presentedGenerator datum 4)⁻¹).toMonoidHom.comp
          ((gamma3ToPresented datum).comp (uLift datum)) =
        (gamma3ToPresented datum).comp (vLift datum) := by
    apply FreeGroup.ext_hom
    intro q
    simpa [MonoidHom.comp_apply, uLift, vLift] using
      presented_c_conjugates_basis datum q
  simpa [MonoidHom.comp_apply] using DFunLike.congr_fun heq x

theorem c_lift_condition (a : U datum) :
    (presentedGenerator datum 4)⁻¹ *
        gamma3ToPresented datum (a : Gamma3) =
      gamma3ToPresented datum (cEquiv datum hfree a : Gamma3) *
        (presentedGenerator datum 4)⁻¹ := by
  rcases a.property with ⟨x, hx⟩
  let ax : U datum := ⟨uLift datum x, ⟨x, rfl⟩⟩
  have hax : a = ax := by
    apply Subtype.ext
    exact hx.symm
  subst a
  have hphi : ((cEquiv datum hfree ax : V datum) : Gamma3) =
      vLift datum x := by
    simp [ax, cEquiv, rangeEquiv_apply_range]
  calc
    (presentedGenerator datum 4)⁻¹ *
          gamma3ToPresented datum (ax : Gamma3) =
        ((presentedGenerator datum 4)⁻¹ *
            gamma3ToPresented datum (uLift datum x) *
            presentedGenerator datum 4) *
          (presentedGenerator datum 4)⁻¹ := by
            simp [ax, mul_assoc]
    _ = gamma3ToPresented datum (vLift datum x) *
          (presentedGenerator datum 4)⁻¹ := by
            rw [presented_c_conjugates_uLift datum x]
    _ = gamma3ToPresented datum (cEquiv datum hfree ax : Gamma3) *
          (presentedGenerator datum 4)⁻¹ := by rw [hphi]

/-- Reverse map through Borisov's `c`-HNN extension. -/
def gamma2ToPresented : Gamma2 datum hfree →* Presented datum :=
  HNNExtension.lift (gamma3ToPresented datum)
    (presentedGenerator datum 4)⁻¹ (c_lift_condition datum hfree)

@[simp] theorem gamma2ToPresented_of3 (x : Gamma3) :
    gamma2ToPresented datum hfree (of3 datum hfree x) =
      gamma3ToPresented datum x := by
  simp [gamma2ToPresented, of3]

@[simp] theorem gamma2ToPresented_c :
    gamma2ToPresented datum hfree (c datum hfree) =
      presentedGenerator datum 4 := by
  simp [gamma2ToPresented, c]

private theorem presented_t_commutes_c :
    Commute (presentedGenerator datum 5) (presentedGenerator datum 4) := by
  have h := full_relator_eq_one datum 9
  have h' :
      (presentedGenerator datum 5)⁻¹ *
          (presentedGenerator datum 4)⁻¹ *
          presentedGenerator datum 5 * presentedGenerator datum 4 = 1 := by
    simpa [Borisov.presentation, Borisov.tWord, Borisov.cWord] using h
  exact (inverse_commutator_eq_one_iff_commute _ _).mp h'

private theorem presented_t_commutes_d :
    Commute (presentedGenerator datum 5) (presentedGenerator datum 0) := by
  have h := full_relator_eq_one datum 10
  have h' :
      (presentedGenerator datum 5)⁻¹ *
          (presentedGenerator datum 0)⁻¹ *
          presentedGenerator datum 5 * presentedGenerator datum 0 = 1 := by
    simpa [Borisov.presentation, Borisov.tWord, Borisov.dWord] using h
  exact (inverse_commutator_eq_one_iff_commute _ _).mp h'

private theorem CD_le_t_centralizer :
    CD datum hfree ≤
      (Subgroup.centralizer {presentedGenerator datum 5}).comap
        (gamma2ToPresented datum hfree) := by
  rw [CD, Subgroup.closure_le]
  intro x hx
  change gamma2ToPresented datum hfree x ∈
    Subgroup.centralizer {presentedGenerator datum 5}
  rw [Subgroup.mem_centralizer_singleton_iff]
  rcases hx with hx | hx
  · have hxc : x = c datum hfree := by simpa using hx
    subst x
    rw [gamma2ToPresented_c]
    exact (presented_t_commutes_c datum).eq.symm
  · have hxd : x = of3 datum hfree d3 := by simpa using hx
    subst x
    rw [gamma2ToPresented_of3, gamma3ToPresented_d3]
    exact (presented_t_commutes_d datum).eq.symm

/-- Reverse map through the `t` centralizer HNN extension. -/
def tStageToPresented : TStage datum hfree →* Presented datum :=
  HNNExtension.lift (gamma2ToPresented datum hfree)
    (presentedGenerator datum 5) (by
      intro a
      change presentedGenerator datum 5 *
          gamma2ToPresented datum hfree (a : Gamma2 datum hfree) =
        gamma2ToPresented datum hfree (a : Gamma2 datum hfree) *
          presentedGenerator datum 5
      have ha := CD_le_t_centralizer datum hfree a.property
      exact (Subgroup.mem_centralizer_singleton_iff.mp ha).symm)

@[simp] theorem tStageToPresented_of (x : Gamma2 datum hfree) :
    tStageToPresented datum hfree (toTStage datum hfree x) =
      gamma2ToPresented datum hfree x := by
  simp [tStageToPresented, toTStage, centralizerOf]

@[simp] theorem tStageToPresented_t :
    tStageToPresented datum hfree (tLetter datum hfree) =
      presentedGenerator datum 5 := by
  simp [tStageToPresented, tLetter, centralizerStable]

@[simp] theorem gamma2ToPresented_positive2 (w : List (Fin 2)) :
    gamma2ToPresented datum hfree (positive2 datum hfree w) =
      Thue.evalPositive (presentedGenerator datum 2)
        (presentedGenerator datum 3) w := by
  simp [positive2]

@[simp] theorem tStageToPresented_conjugatedT (w : List (Fin 2)) :
    tStageToPresented datum hfree (conjugatedT datum hfree w) =
      (Thue.evalPositive (presentedGenerator datum 2)
          (presentedGenerator datum 3) w)⁻¹ *
        presentedGenerator datum 5 *
        Thue.evalPositive (presentedGenerator datum 2)
          (presentedGenerator datum 3) w := by
  change tStageToPresented datum hfree
      ((toTStage datum hfree (positive2 datum hfree w))⁻¹ *
        tLetter datum hfree *
        toTStage datum hfree (positive2 datum hfree w)) = _
  rw [map_mul, map_mul, map_inv, tStageToPresented_of,
    tStageToPresented_t, gamma2ToPresented_positive2]

private theorem presented_k_commutes_c :
    Commute (presentedGenerator datum 6) (presentedGenerator datum 4) := by
  have h := full_relator_eq_one datum 11
  have h' :
      (presentedGenerator datum 6)⁻¹ *
          (presentedGenerator datum 4)⁻¹ *
          presentedGenerator datum 6 * presentedGenerator datum 4 = 1 := by
    simpa [Borisov.presentation, Borisov.kWord, Borisov.cWord] using h
  exact (inverse_commutator_eq_one_iff_commute _ _).mp h'

private theorem presented_k_commutes_e :
    Commute (presentedGenerator datum 6) (presentedGenerator datum 1) := by
  have h := full_relator_eq_one datum 12
  have h' :
      (presentedGenerator datum 6)⁻¹ *
          (presentedGenerator datum 1)⁻¹ *
          presentedGenerator datum 6 * presentedGenerator datum 1 = 1 := by
    simpa [Borisov.presentation, Borisov.kWord, Borisov.eWord] using h
  exact (inverse_commutator_eq_one_iff_commute _ _).mp h'

private theorem presented_k_commutes_p :
    Commute (presentedGenerator datum 6)
      ((Thue.evalPositive (presentedGenerator datum 2)
          (presentedGenerator datum 3) datum.P)⁻¹ *
        presentedGenerator datum 5 *
        Thue.evalPositive (presentedGenerator datum 2)
          (presentedGenerator datum 3) datum.P) := by
  have h := full_relator_eq_one datum 13
  have h' :
      (presentedGenerator datum 6)⁻¹ *
          ((Thue.evalPositive (presentedGenerator datum 2)
            (presentedGenerator datum 3) datum.P)⁻¹ *
            presentedGenerator datum 5 *
            Thue.evalPositive (presentedGenerator datum 2)
              (presentedGenerator datum 3) datum.P)⁻¹ *
          presentedGenerator datum 6 *
          ((Thue.evalPositive (presentedGenerator datum 2)
            (presentedGenerator datum 3) datum.P)⁻¹ *
            presentedGenerator datum 5 *
            Thue.evalPositive (presentedGenerator datum 2)
              (presentedGenerator datum 3) datum.P) = 1 := by
    simpa [Borisov.presentation, Borisov.kWord, Borisov.pWord,
      Borisov.tWord, mul_assoc] using h
  exact (inverse_commutator_eq_one_iff_commute _ _).mp h'

private theorem CE_le_k_centralizer :
    CE datum hfree ≤
      (Subgroup.centralizer {presentedGenerator datum 6}).comap
        (gamma2ToPresented datum hfree) := by
  rw [CE, Subgroup.closure_le]
  intro x hx
  change gamma2ToPresented datum hfree x ∈
    Subgroup.centralizer {presentedGenerator datum 6}
  rw [Subgroup.mem_centralizer_singleton_iff]
  rcases hx with hx | hx
  · have hxc : x = c datum hfree := by simpa using hx
    subst x
    rw [gamma2ToPresented_c]
    exact (presented_k_commutes_c datum).eq.symm
  · have hxe : x = of3 datum hfree e3 := by simpa using hx
    subst x
    rw [gamma2ToPresented_of3, gamma3ToPresented_e3]
    exact (presented_k_commutes_e datum).eq.symm

private theorem KSubgroup_le_k_centralizer :
    KSubgroup datum hfree ≤
      (Subgroup.centralizer {presentedGenerator datum 6}).comap
        (tStageToPresented datum hfree) := by
  rw [KSubgroup, generatedWith, Subgroup.closure_le]
  intro x hx
  change tStageToPresented datum hfree x ∈
    Subgroup.centralizer {presentedGenerator datum 6}
  rw [Subgroup.mem_centralizer_singleton_iff]
  rcases hx with hx | hx
  · rcases hx with ⟨a, ha, rfl⟩
    rw [tStageToPresented_of]
    have hmem := CE_le_k_centralizer datum hfree ha
    exact Subgroup.mem_centralizer_singleton_iff.mp hmem
  · have hx' : x = conjugatedT datum hfree datum.P := by simpa using hx
    subst x
    rw [tStageToPresented_conjugatedT]
    exact (presented_k_commutes_p datum).eq.symm

/-- The complete reverse homomorphism from the semantic final HNN model to
Borisov's fourteen-relator presentation. -/
def fromFinalModel : FinalStage datum hfree →* Presented datum :=
  HNNExtension.lift (tStageToPresented datum hfree)
    (presentedGenerator datum 6) (by
      intro a
      change presentedGenerator datum 6 *
          tStageToPresented datum hfree (a : TStage datum hfree) =
        tStageToPresented datum hfree (a : TStage datum hfree) *
          presentedGenerator datum 6
      have ha := KSubgroup_le_k_centralizer datum hfree a.property
      exact (Subgroup.mem_centralizer_singleton_iff.mp ha).symm)

@[simp] theorem fromFinalModel_of (x : TStage datum hfree) :
    fromFinalModel datum hfree (toFinalStage datum hfree x) =
      tStageToPresented datum hfree x := by
  simp [fromFinalModel, toFinalStage, centralizerOf]

@[simp] theorem fromFinalModel_k :
    fromFinalModel datum hfree (kLetter datum hfree) =
      presentedGenerator datum 6 := by
  simp [fromFinalModel, kLetter, centralizerStable]

@[simp] theorem fromFinalModel_modelD :
    fromFinalModel datum hfree (modelD datum hfree) =
      presentedGenerator datum 0 := by
  simp [modelD, cStageToFinal]

@[simp] theorem fromFinalModel_modelE :
    fromFinalModel datum hfree (modelE datum hfree) =
      presentedGenerator datum 1 := by
  simp [modelE, cStageToFinal]

@[simp] theorem fromFinalModel_modelS1 :
    fromFinalModel datum hfree (modelS1 datum hfree) =
      presentedGenerator datum 2 := by
  simp [modelS1, cStageToFinal]

@[simp] theorem fromFinalModel_modelS2 :
    fromFinalModel datum hfree (modelS2 datum hfree) =
      presentedGenerator datum 3 := by
  simp [modelS2, cStageToFinal]

@[simp] theorem fromFinalModel_modelC :
    fromFinalModel datum hfree (modelC datum hfree) =
      presentedGenerator datum 4 := by
  simp [modelC, cStageToFinal]

@[simp] theorem fromFinalModel_modelT :
    fromFinalModel datum hfree (modelT datum hfree) =
      presentedGenerator datum 5 := by
  simp [modelT]

@[simp] theorem fromFinalModel_modelK :
    fromFinalModel datum hfree (modelK datum hfree) =
      presentedGenerator datum 6 := by
  simp [modelK]

theorem fromFinalModel_comp_toFinalModel :
    (fromFinalModel datum hfree).comp (toFinalModel datum hfree) =
      MonoidHom.id (Presented datum) := by
  apply PresentedGroup.ext
  intro i
  fin_cases i <;> simp [modelGenerator, presentedGenerator]

theorem toFinalModel_injective_internal :
    Function.Injective (toFinalModel datum hfree) := by
  exact Function.LeftInverse.injective
    (fun x => DFunLike.congr_fun
      (fromFinalModel_comp_toFinalModel datum hfree) x)

end

end BorisovFinalModelInjective

namespace BorisovFinalModel

/-- The canonical homomorphism from Borisov's fourteen-relator presentation
to its iterated-HNN semantic model is injective.  The proof constructs an
explicit left inverse through all five HNN stages. -/
theorem _root_.Undecidability.BorisovFinalModel.toFinalModel_injective
    (datum : Thue.StandingDatum)
    (hfree : BorisovCStage.RankFiveFree datum) :
    Function.Injective (toFinalModel datum hfree) :=
  BorisovFinalModelInjective.toFinalModel_injective_internal datum hfree

end BorisovFinalModel
end Undecidability
