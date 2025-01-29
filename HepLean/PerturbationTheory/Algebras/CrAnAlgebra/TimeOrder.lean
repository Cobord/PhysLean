/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.FieldSpecification.TimeOrder
import HepLean.PerturbationTheory.Algebras.CrAnAlgebra.SuperCommute
import HepLean.PerturbationTheory.Koszul.KoszulSign
/-!

# Time Ordering in the CrAnAlgebra

-/

namespace FieldSpecification
variable {𝓕 : FieldSpecification}
open FieldStatistic

namespace CrAnAlgebra

noncomputable section
open HepLean.List
/-!

## Time order

-/

/-- Time ordering for the `CrAnAlgebra`. -/
def timeOrder : CrAnAlgebra 𝓕 →ₗ[ℂ] CrAnAlgebra 𝓕 :=
  Basis.constr ofCrAnListBasis ℂ fun φs =>
  crAnTimeOrderSign φs • ofCrAnList (crAnTimeOrderList φs)

@[inherit_doc timeOrder]
scoped[FieldSpecification.CrAnAlgebra] notation "𝓣ᶠ(" a ")" => timeOrder a

lemma timeOrder_ofCrAnList (φs : List 𝓕.CrAnStates) :
    𝓣ᶠ(ofCrAnList φs) = crAnTimeOrderSign φs • ofCrAnList (crAnTimeOrderList φs) := by
  rw [← ofListBasis_eq_ofList]
  simp only [timeOrder, Basis.constr_basis]

lemma timeOrder_timeOrder_mid (a b c : 𝓕.CrAnAlgebra) : 𝓣ᶠ(a * b * c) = 𝓣ᶠ(a * 𝓣ᶠ(b) * c) := by
  let pc (c : 𝓕.CrAnAlgebra) (hc : c ∈ Submodule.span ℂ (Set.range ofCrAnListBasis)) :
    Prop := 𝓣ᶠ(a * b * c) = 𝓣ᶠ(a * 𝓣ᶠ(b) * c)
  change pc c (Basis.mem_span _ c)
  apply Submodule.span_induction
  · intro x hx
    obtain ⟨φs, rfl⟩ := hx
    simp [pc]
    let pb (b : 𝓕.CrAnAlgebra) (hb : b ∈ Submodule.span ℂ (Set.range ofCrAnListBasis)) :
      Prop := 𝓣ᶠ(a * b * ofCrAnList φs) = 𝓣ᶠ(a * 𝓣ᶠ(b) * ofCrAnList φs)
    change pb b (Basis.mem_span _ b)
    apply Submodule.span_induction
    · intro x hx
      obtain ⟨φs', rfl⟩ := hx
      simp [pb]
      let pa (a : 𝓕.CrAnAlgebra) (ha : a ∈ Submodule.span ℂ (Set.range ofCrAnListBasis)) :
        Prop := 𝓣ᶠ(a * ofCrAnList φs' * ofCrAnList φs) = 𝓣ᶠ(a * 𝓣ᶠ(ofCrAnList φs') * ofCrAnList φs)
      change pa a (Basis.mem_span _ a)
      apply Submodule.span_induction
      · intro x hx
        obtain ⟨φs'', rfl⟩ := hx
        simp [pa]
        rw [timeOrder_ofCrAnList]
        simp only [← ofCrAnList_append, Algebra.mul_smul_comm,
          Algebra.smul_mul_assoc, map_smul]
        rw [timeOrder_ofCrAnList, timeOrder_ofCrAnList, smul_smul]
        congr 1
        · simp only [crAnTimeOrderSign,  crAnTimeOrderList]
          rw [Wick.koszulSign_of_append_eq_insertionSort, mul_comm]
        · congr 1
          simp only [crAnTimeOrderList]
          rw [insertionSort_append_insertionSort_append]
      · simp [pa]
      · intro x y hx hy h1 h2
        simp_all [pa, add_mul]
      · intro x hx h
        simp_all [pa]
    · simp [pb]
    · intro x y hx hy h1 h2
      simp_all [pb, mul_add, add_mul]
    · intro x hx h
      simp_all [pb]
  · simp [pc]
  · intro x y hx hy h1 h2
    simp_all [pc, mul_add]
  · intro x hx h hp
    simp_all [pc]

lemma timeOrder_timeOrder_right (a b : 𝓕.CrAnAlgebra) : 𝓣ᶠ(a * b) = 𝓣ᶠ(a * 𝓣ᶠ(b)) := by
  trans 𝓣ᶠ(a * b * 1)
  · simp
  · rw [timeOrder_timeOrder_mid]
    simp

lemma timeOrder_timeOrder_left (a b : 𝓕.CrAnAlgebra) : 𝓣ᶠ(a * b) = 𝓣ᶠ(𝓣ᶠ(a) * b) := by
  trans 𝓣ᶠ(1 * a * b)
  · simp
  · rw [timeOrder_timeOrder_mid]
    simp

lemma timeOrder_ofStateList (φs : List 𝓕.States) :
    𝓣ᶠ(ofStateList φs) = timeOrderSign φs • ofStateList (timeOrderList φs) := by
  conv_lhs =>
    rw [ofStateList_sum, map_sum]
    enter [2, x]
    rw [timeOrder_ofCrAnList]
  simp only [crAnTimeOrderSign_crAnSection]
  rw [← Finset.smul_sum]
  congr
  rw [ofStateList_sum, sum_crAnSections_timeOrder]
  rfl

lemma timeOrder_ofStateList_nil : timeOrder (𝓕 := 𝓕) (ofStateList []) = 1 := by
  rw [timeOrder_ofStateList]
  simp [timeOrderSign, Wick.koszulSign, timeOrderList]

@[simp]
lemma timeOrder_ofStateList_singleton (φ : 𝓕.States) : 𝓣ᶠ(ofStateList [φ]) = ofStateList [φ] := by
  simp [timeOrder_ofStateList, timeOrderSign, timeOrderList]

lemma timeOrder_ofState_ofState_ordered {φ ψ : 𝓕.States} (h : timeOrderRel φ ψ) :
    𝓣ᶠ(ofState φ * ofState ψ) = ofState φ * ofState ψ := by
  rw [← ofStateList_singleton, ← ofStateList_singleton, ← ofStateList_append, timeOrder_ofStateList]
  simp only [List.singleton_append]
  rw [timeOrderSign_pair_ordered h, timeOrderList_pair_ordered h]
  simp

lemma timeOrder_ofState_ofState_not_ordered {φ ψ : 𝓕.States} (h : ¬ timeOrderRel φ ψ) :
    𝓣ᶠ(ofState φ * ofState ψ) = 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ ψ) • ofState ψ * ofState φ := by
  rw [← ofStateList_singleton, ← ofStateList_singleton,
    ← ofStateList_append, timeOrder_ofStateList]
  simp only [List.singleton_append, instCommGroup.eq_1, Algebra.smul_mul_assoc]
  rw [timeOrderSign_pair_not_ordered h, timeOrderList_pair_not_ordered h]
  simp [← ofStateList_append]

lemma timeOrder_ofState_ofState_not_ordered_eq_timeOrder {φ ψ : 𝓕.States} (h : ¬ timeOrderRel φ ψ) :
    𝓣ᶠ(ofState φ * ofState ψ) = 𝓢(𝓕 |>ₛ φ, 𝓕 |>ₛ ψ) • 𝓣ᶠ(ofState ψ * ofState φ) := by
  rw [timeOrder_ofState_ofState_not_ordered h]
  rw [timeOrder_ofState_ofState_ordered]
  simp only [instCommGroup.eq_1, Algebra.smul_mul_assoc]
  have hx := IsTotal.total (r := timeOrderRel) ψ φ
  simp_all

lemma timeOrder_superCommute_ofCrAnState_ofCrAnState_not_crAnTimeOrderRel
    {φ ψ : 𝓕.CrAnStates} (h : ¬ crAnTimeOrderRel φ ψ) :
    𝓣ᶠ([ofCrAnState φ, ofCrAnState ψ]ₛca) = 0 := by
  rw [superCommute_ofCrAnState_ofCrAnState]
  simp only [instCommGroup.eq_1, Algebra.smul_mul_assoc, map_sub, map_smul]
  rw [← ofCrAnList_singleton, ← ofCrAnList_singleton,
    ← ofCrAnList_append, ← ofCrAnList_append, timeOrder_ofCrAnList, timeOrder_ofCrAnList]
  simp only [List.singleton_append]
  rw [crAnTimeOrderSign_pair_not_ordered h, crAnTimeOrderList_pair_not_ordered h]
  rw [sub_eq_zero, smul_smul]
  have h1 := IsTotal.total (r := crAnTimeOrderRel) φ ψ
  congr
  · rw [crAnTimeOrderSign_pair_ordered, exchangeSign_symm]
    simp only [instCommGroup.eq_1, mul_one]
    simp_all
  · rw [crAnTimeOrderList_pair_ordered]
    simp_all

lemma timeOrder_superCommute_ofCrAnState_ofCrAnState_not_crAnTimeOrderRel_right
    {φ ψ : 𝓕.CrAnStates} (h : ¬ crAnTimeOrderRel φ ψ) (a : 𝓕.CrAnAlgebra) :
    𝓣ᶠ(a * [ofCrAnState φ, ofCrAnState ψ]ₛca) = 0 := by
  rw [timeOrder_timeOrder_right,
    timeOrder_superCommute_ofCrAnState_ofCrAnState_not_crAnTimeOrderRel h]
  simp


lemma timeOrder_superCommute_ofCrAnState_ofCrAnState_not_crAnTimeOrderRel_left
    {φ ψ : 𝓕.CrAnStates} (h : ¬ crAnTimeOrderRel φ ψ) (a : 𝓕.CrAnAlgebra) :
    𝓣ᶠ([ofCrAnState φ, ofCrAnState ψ]ₛca * a) = 0 := by
  rw [timeOrder_timeOrder_left,
    timeOrder_superCommute_ofCrAnState_ofCrAnState_not_crAnTimeOrderRel h]
  simp

lemma timeOrder_superCommute_ofCrAnState_ofCrAnState_not_crAnTimeOrderRel_mid
    {φ ψ : 𝓕.CrAnStates} (h : ¬ crAnTimeOrderRel φ ψ) (a b : 𝓕.CrAnAlgebra) :
    𝓣ᶠ(a * [ofCrAnState φ, ofCrAnState ψ]ₛca * b) = 0 := by
  rw [timeOrder_timeOrder_mid,
    timeOrder_superCommute_ofCrAnState_ofCrAnState_not_crAnTimeOrderRel h]
  simp

lemma timeOrder_superCommute_superCommute_ofCrAnState_not_crAnTimeOrderRel
    {φ1 φ2 : 𝓕.CrAnStates} (h : ¬ crAnTimeOrderRel φ1 φ2) (a : 𝓕.CrAnAlgebra):
    𝓣ᶠ([a, [ofCrAnState φ1, ofCrAnState φ2]ₛca]ₛca) = 0 := by
  rw [← bosonicProj_add_fermionicProj a]
  simp
  rw [bosonic_superCommute (Submodule.coe_mem (bosonicProj a))]
  simp
  rw [timeOrder_superCommute_ofCrAnState_ofCrAnState_not_crAnTimeOrderRel_left h]
  rw [timeOrder_superCommute_ofCrAnState_ofCrAnState_not_crAnTimeOrderRel_right h]
  simp
  rw [← ofCrAnList_singleton, ← ofCrAnList_singleton]
  rcases superCommute_ofCrAnList_ofCrAnList_bosonic_or_fermionic [φ1] [φ2] with h' | h'
  · rw [superCommute_bonsonic h']
    simp [ofCrAnList_singleton]
    rw [timeOrder_superCommute_ofCrAnState_ofCrAnState_not_crAnTimeOrderRel_left h]
    rw [timeOrder_superCommute_ofCrAnState_ofCrAnState_not_crAnTimeOrderRel_right h]
    simp
  · rw [superCommute_fermionic_fermionic (Submodule.coe_mem (fermionicProj a)) h']
    simp [ofCrAnList_singleton]
    rw [timeOrder_superCommute_ofCrAnState_ofCrAnState_not_crAnTimeOrderRel_left h]
    rw [timeOrder_superCommute_ofCrAnState_ofCrAnState_not_crAnTimeOrderRel_right h]
    simp

lemma timeOrder_superCommute_ofCrAnState_superCommute_not_crAnTimeOrderRel
    {φ1 φ2 φ3 : 𝓕.CrAnStates} (h12 : ¬ crAnTimeOrderRel φ1 φ2)
    (h13 : ¬ crAnTimeOrderRel φ1 φ3) :
    𝓣ᶠ([ofCrAnState φ1, [ofCrAnState φ2, ofCrAnState φ3]ₛca]ₛca) = 0 := by
  rw [← ofCrAnList_singleton, ← ofCrAnList_singleton, ← ofCrAnList_singleton]
  rw [summerCommute_jacobi_ofCrAnList]
  simp [ofCrAnList_singleton]
  right
  rw [timeOrder_superCommute_superCommute_ofCrAnState_not_crAnTimeOrderRel h12 ]
  rw [superCommute_ofCrAnState_ofCrAnState_symm φ3]
  simp
  rw [timeOrder_superCommute_superCommute_ofCrAnState_not_crAnTimeOrderRel h13]
  simp

lemma timeOrder_superCommute_ofCrAnState_superCommute_not_crAnTimeOrderRel'
    {φ1 φ2 φ3 : 𝓕.CrAnStates} (h12 : ¬ crAnTimeOrderRel φ2 φ1)
    (h13 : ¬ crAnTimeOrderRel φ3 φ1) :
    𝓣ᶠ([ofCrAnState φ1, [ofCrAnState φ2, ofCrAnState φ3]ₛca]ₛca) = 0 := by
  rw [← ofCrAnList_singleton, ← ofCrAnList_singleton, ← ofCrAnList_singleton]
  rw [summerCommute_jacobi_ofCrAnList]
  simp [ofCrAnList_singleton]
  right
  rw [superCommute_ofCrAnState_ofCrAnState_symm φ1]
  simp
  rw [timeOrder_superCommute_superCommute_ofCrAnState_not_crAnTimeOrderRel h12 ]
  simp
  rw [timeOrder_superCommute_superCommute_ofCrAnState_not_crAnTimeOrderRel h13]
  simp

lemma timeOrder_superCommute_ofCrAnState_superCommute_all_not_crAnTimeOrderRel
    (φ1 φ2 φ3 : 𝓕.CrAnStates) (h : ¬ (
      crAnTimeOrderRel φ1 φ2 ∧ crAnTimeOrderRel φ1 φ3 ∧
      crAnTimeOrderRel φ2 φ1 ∧ crAnTimeOrderRel φ2 φ3 ∧
      crAnTimeOrderRel φ3 φ1 ∧ crAnTimeOrderRel φ3 φ2)) :
    𝓣ᶠ([ofCrAnState φ1, [ofCrAnState φ2, ofCrAnState φ3]ₛca]ₛca) = 0 := by
  simp at h
  by_cases h23 : ¬ crAnTimeOrderRel φ2 φ3
  · simp_all
    rw [timeOrder_superCommute_superCommute_ofCrAnState_not_crAnTimeOrderRel h23]
  simp_all
  by_cases h32 : ¬ crAnTimeOrderRel φ3 φ2
  · simp_all
    rw [superCommute_ofCrAnState_ofCrAnState_symm]
    simp
    rw [timeOrder_superCommute_superCommute_ofCrAnState_not_crAnTimeOrderRel h32]
    simp
  simp_all
  by_cases h12 : ¬ crAnTimeOrderRel φ1 φ2
  · have h13 : ¬ crAnTimeOrderRel φ1 φ3 := by
      intro h13
      apply h12
      exact IsTrans.trans φ1 φ3 φ2 h13 h32
    rw [timeOrder_superCommute_ofCrAnState_superCommute_not_crAnTimeOrderRel h12 h13]
  simp_all
  have h13 : crAnTimeOrderRel φ1 φ3 := IsTrans.trans φ1 φ2 φ3 h12 h23
  simp_all
  by_cases h21 : ¬ crAnTimeOrderRel φ2 φ1
  · simp_all
    have h31 : ¬ crAnTimeOrderRel φ3 φ1 := by
      intro h31
      apply h21
      exact IsTrans.trans φ2 φ3 φ1 h23 h31
    rw [timeOrder_superCommute_ofCrAnState_superCommute_not_crAnTimeOrderRel' h21 h31]
  simp_all
  refine False.elim (h ?_)
  exact IsTrans.trans φ3 φ2 φ1 h32 h21


lemma timeOrder_superCommute_ofCrAnState_ofCrAnState_eq_time
    {φ ψ : 𝓕.CrAnStates} (h1 : crAnTimeOrderRel φ ψ) (h2 : crAnTimeOrderRel ψ φ) :
    𝓣ᶠ([ofCrAnState φ, ofCrAnState ψ]ₛca) = [ofCrAnState φ, ofCrAnState ψ]ₛca := by
  rw [superCommute_ofCrAnState_ofCrAnState]
  simp only [instCommGroup.eq_1, Algebra.smul_mul_assoc, map_sub, map_smul]
  rw [← ofCrAnList_singleton, ← ofCrAnList_singleton,
    ← ofCrAnList_append, ← ofCrAnList_append, timeOrder_ofCrAnList, timeOrder_ofCrAnList]
  simp only [List.singleton_append]
  rw [crAnTimeOrderSign_pair_ordered h1, crAnTimeOrderList_pair_ordered h1,
    crAnTimeOrderSign_pair_ordered h2, crAnTimeOrderList_pair_ordered h2]
  simp

/-!

## Interaction with maxTimeField

-/

/-- In the state algebra time, ordering obeys `T(φ₀φ₁…φₙ) = s * φᵢ * T(φ₀φ₁…φᵢ₋₁φᵢ₊₁…φₙ)`
  where `φᵢ` is the state
  which has maximum time and `s` is the exchange sign of `φᵢ` and `φ₀φ₁…φᵢ₋₁`. -/
lemma timeOrder_eq_maxTimeField_mul (φ : 𝓕.States) (φs : List 𝓕.States) :
    𝓣ᶠ(ofStateList (φ :: φs)) =
    𝓢(𝓕 |>ₛ maxTimeField φ φs, 𝓕 |>ₛ (φ :: φs).take (maxTimeFieldPos φ φs)) •
    ofState (maxTimeField φ φs) * 𝓣ᶠ(ofStateList (eraseMaxTimeField φ φs)) := by
  rw [timeOrder_ofStateList, timeOrderList_eq_maxTimeField_timeOrderList]
  rw [ofStateList_cons, timeOrder_ofStateList]
  simp only [instCommGroup.eq_1, Algebra.mul_smul_comm, Algebra.smul_mul_assoc, smul_smul]
  congr
  rw [timerOrderSign_of_eraseMaxTimeField, mul_assoc]
  simp

/-- In the state algebra time, ordering obeys `T(φ₀φ₁…φₙ) = s * φᵢ * T(φ₀φ₁…φᵢ₋₁φᵢ₊₁…φₙ)`
  where `φᵢ` is the state
  which has maximum time and `s` is the exchange sign of `φᵢ` and `φ₀φ₁…φᵢ₋₁`.
  Here `s` is written using finite sets. -/
lemma timeOrder_eq_maxTimeField_mul_finset (φ : 𝓕.States) (φs : List 𝓕.States) :
    𝓣ᶠ(ofStateList (φ :: φs)) = 𝓢(𝓕 |>ₛ maxTimeField φ φs, 𝓕 |>ₛ ⟨(eraseMaxTimeField φ φs).get,
      (Finset.filter (fun x =>
        (maxTimeFieldPosFin φ φs).succAbove x < maxTimeFieldPosFin φ φs) Finset.univ)⟩) •
      ofState (maxTimeField φ φs) * 𝓣ᶠ(ofStateList (eraseMaxTimeField φ φs)) := by
  rw [timeOrder_eq_maxTimeField_mul]
  congr 3
  apply FieldStatistic.ofList_perm
  nth_rewrite 1 [← List.finRange_map_get (φ :: φs)]
  simp only [List.length_cons, eraseMaxTimeField, insertionSortDropMinPos]
  rw [eraseIdx_get, ← List.map_take, ← List.map_map]
  refine List.Perm.map (φ :: φs).get ?_
  apply (List.perm_ext_iff_of_nodup _ _).mpr
  · intro i
    simp only [List.length_cons, maxTimeFieldPos, mem_take_finrange, Fin.val_fin_lt, List.mem_map,
      Finset.mem_sort, Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply]
    refine Iff.intro (fun hi => ?_) (fun h => ?_)
    · have h2 := (maxTimeFieldPosFin φ φs).2
      simp only [eraseMaxTimeField, insertionSortDropMinPos, List.length_cons, Nat.succ_eq_add_one,
        maxTimeFieldPosFin, insertionSortMinPosFin] at h2
      use ⟨i, by omega⟩
      apply And.intro
      · simp only [Fin.succAbove, List.length_cons, Fin.castSucc_mk, maxTimeFieldPosFin,
        insertionSortMinPosFin, Nat.succ_eq_add_one, Fin.mk_lt_mk, Fin.val_fin_lt, Fin.succ_mk]
        rw [Fin.lt_def]
        split
        · simp only [Fin.val_fin_lt]
          omega
        · omega
      · simp only [Fin.succAbove, List.length_cons, Fin.castSucc_mk, Fin.succ_mk, Fin.ext_iff,
        Fin.coe_cast]
        split
        · simp
        · simp_all [Fin.lt_def]
    · obtain ⟨j, h1, h2⟩ := h
      subst h2
      simp only [Fin.lt_def, Fin.coe_cast]
      exact h1
  · exact List.Sublist.nodup (List.take_sublist _ _) <|
      List.nodup_finRange (φs.length + 1)
  · refine List.Nodup.map ?_ ?_
    · refine Function.Injective.comp ?hf.hg Fin.succAbove_right_injective
      exact Fin.cast_injective (eraseIdx_length (φ :: φs) (insertionSortMinPos timeOrderRel φ φs))
    · exact Finset.sort_nodup (fun x1 x2 => x1 ≤ x2)
        (Finset.filter (fun x => (maxTimeFieldPosFin φ φs).succAbove x < maxTimeFieldPosFin φ φs)
          Finset.univ)

end

end CrAnAlgebra

end FieldSpecification
