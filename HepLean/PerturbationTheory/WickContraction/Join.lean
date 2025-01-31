/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.WickContraction.TimeContract
import HepLean.PerturbationTheory.WickContraction.StaticContract
import HepLean.PerturbationTheory.Algebras.FieldOpAlgebra.TimeContraction
import HepLean.PerturbationTheory.WickContraction.SubContraction
import HepLean.PerturbationTheory.WickContraction.Singleton

/-!

# Join of contractions

-/

open FieldSpecification
variable {𝓕 : FieldSpecification}

namespace WickContraction
variable {n : ℕ} (c : WickContraction n)
open HepLean.List
open FieldOpAlgebra

def join {φs : List 𝓕.States} (φsΛ : WickContraction φs.length)
    (φsucΛ : WickContraction [φsΛ]ᵘᶜ.length) : WickContraction φs.length :=
  ⟨φsΛ.1 ∪ φsucΛ.1.map (Finset.mapEmbedding uncontractedListEmd).toEmbedding, by
    intro a ha
    simp at ha
    rcases ha with ha | ha
    · exact φsΛ.2.1 a ha
    · obtain ⟨a, ha, rfl⟩ := ha
      rw [Finset.mapEmbedding_apply]
      simp only [Finset.card_map]
      exact φsucΛ.2.1 a ha, by
    intro a ha b hb
    simp at ha hb
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact φsΛ.2.2 a ha b hb
    · obtain ⟨b, hb, rfl⟩ := hb
      right
      symm
      rw [Finset.mapEmbedding_apply]
      apply uncontractedListEmd_finset_disjoint_left
      exact ha
    · obtain ⟨a, ha, rfl⟩ := ha
      right
      rw [Finset.mapEmbedding_apply]
      apply uncontractedListEmd_finset_disjoint_left
      exact hb
    · obtain ⟨a, ha, rfl⟩ := ha
      obtain ⟨b, hb, rfl⟩ := hb
      simp only [EmbeddingLike.apply_eq_iff_eq]
      rw [Finset.mapEmbedding_apply, Finset.mapEmbedding_apply]
      rw [Finset.disjoint_map]
      exact φsucΛ.2.2 a ha b hb⟩

lemma join_congr {φs : List 𝓕.States} {φsΛ : WickContraction φs.length}
    {φsucΛ : WickContraction [φsΛ]ᵘᶜ.length} {φsΛ' : WickContraction φs.length}
    (h1 : φsΛ = φsΛ')  :
    join φsΛ φsucΛ = join φsΛ' (congr (by simp [h1]) φsucΛ):= by
  subst h1
  rfl



def joinLiftLeft {φs : List 𝓕.States} {φsΛ : WickContraction φs.length}
    {φsucΛ : WickContraction [φsΛ]ᵘᶜ.length} : φsΛ.1 → (join φsΛ φsucΛ).1 :=
  fun a => ⟨a, by simp [join]⟩

lemma jointLiftLeft_injective {φs : List 𝓕.States} {φsΛ : WickContraction φs.length}
    {φsucΛ : WickContraction [φsΛ]ᵘᶜ.length} :
    Function.Injective (@joinLiftLeft _ _ φsΛ φsucΛ) := by
  intro a b h
  simp only [joinLiftLeft] at h
  rw [Subtype.mk_eq_mk] at h
  refine Subtype.eq h

def joinLiftRight {φs : List 𝓕.States} {φsΛ : WickContraction φs.length}
    {φsucΛ : WickContraction [φsΛ]ᵘᶜ.length} : φsucΛ.1 → (join φsΛ φsucΛ).1 :=
  fun a => ⟨a.1.map uncontractedListEmd, by
    simp only [join, Finset.le_eq_subset, Finset.mem_union, Finset.mem_map,
      RelEmbedding.coe_toEmbedding]
    right
    use a.1
    simp only [Finset.coe_mem, true_and]
    rfl⟩

lemma joinLiftRight_injective {φs : List 𝓕.States} {φsΛ : WickContraction φs.length}
    {φsucΛ : WickContraction [φsΛ]ᵘᶜ.length} :
    Function.Injective (@joinLiftRight _ _ φsΛ φsucΛ) := by
  intro a b h
  simp only [joinLiftRight] at h
  rw [Subtype.mk_eq_mk] at h
  simp only [Finset.map_inj] at h
  refine Subtype.eq h

lemma jointLiftLeft_disjoint_joinLiftRight {φs : List 𝓕.States} {φsΛ : WickContraction φs.length}
    {φsucΛ : WickContraction [φsΛ]ᵘᶜ.length} (a : φsΛ.1) (b : φsucΛ.1) :
    Disjoint (@joinLiftLeft _ _ _ φsucΛ a).1 (joinLiftRight b).1 := by
  simp only [joinLiftLeft, joinLiftRight]
  symm
  apply uncontractedListEmd_finset_disjoint_left
  exact a.2

lemma jointLiftLeft_neq_joinLiftRight {φs : List 𝓕.States} {φsΛ : WickContraction φs.length}
    {φsucΛ : WickContraction [φsΛ]ᵘᶜ.length} (a : φsΛ.1) (b : φsucΛ.1) :
    joinLiftLeft a ≠ joinLiftRight b := by
  by_contra hn
  have h1 := jointLiftLeft_disjoint_joinLiftRight a b
  rw [hn] at h1
  simp at h1
  have hj := (join φsΛ φsucΛ).2.1 (joinLiftRight b).1 (joinLiftRight b).2
  rw [h1] at hj
  simp at hj

def joinLift {φs : List 𝓕.States} {φsΛ : WickContraction φs.length}
    {φsucΛ : WickContraction [φsΛ]ᵘᶜ.length} : φsΛ.1 ⊕ φsucΛ.1 → (join φsΛ φsucΛ).1 := fun a =>
  match a with
  | Sum.inl a => joinLiftLeft a
  | Sum.inr a => joinLiftRight a

lemma joinLift_injective {φs : List 𝓕.States} {φsΛ : WickContraction φs.length}
    {φsucΛ : WickContraction [φsΛ]ᵘᶜ.length} : Function.Injective (@joinLift _ _ φsΛ φsucΛ) := by
  intro a b h
  match a, b with
  | Sum.inl a, Sum.inl b =>
    simp
    exact jointLiftLeft_injective h
  | Sum.inr a, Sum.inr b =>
    simp
    exact joinLiftRight_injective h
  | Sum.inl a, Sum.inr b =>
    simp [joinLift] at h
    have h1 := jointLiftLeft_neq_joinLiftRight a b
    simp_all
  | Sum.inr a, Sum.inl b =>
    simp [joinLift] at h
    have h1 := jointLiftLeft_neq_joinLiftRight b a
    simp_all

lemma joinLift_surjective {φs : List 𝓕.States} {φsΛ : WickContraction φs.length}
    {φsucΛ : WickContraction [φsΛ]ᵘᶜ.length} : Function.Surjective (@joinLift _ _ φsΛ φsucΛ) := by
  intro a
  have ha2 := a.2
  simp  [- Finset.coe_mem, join] at ha2
  rcases ha2 with ha2 | ⟨a2, ha3⟩
  · use Sum.inl ⟨a, ha2⟩
    simp [joinLift, joinLiftLeft]
  · rw [Finset.mapEmbedding_apply] at ha3
    use Sum.inr ⟨a2, ha3.1⟩
    simp [joinLift, joinLiftRight]
    refine Subtype.eq ?_
    exact ha3.2

lemma joinLift_bijective {φs : List 𝓕.States} {φsΛ : WickContraction φs.length}
    {φsucΛ : WickContraction [φsΛ]ᵘᶜ.length} : Function.Bijective (@joinLift _ _ φsΛ φsucΛ) := by
  apply And.intro
  · exact joinLift_injective
  · exact joinLift_surjective

lemma prod_join {φs : List 𝓕.States} (φsΛ : WickContraction φs.length)
    (φsucΛ : WickContraction [φsΛ]ᵘᶜ.length) (f : (join φsΛ φsucΛ).1  → M) [ CommMonoid M]:
      ∏ (a : (join φsΛ φsucΛ).1), f a = (∏ (a : φsΛ.1), f (joinLiftLeft a)) *
      ∏ (a : φsucΛ.1), f (joinLiftRight a) := by
  let e1 := Equiv.ofBijective (@joinLift _ _ φsΛ φsucΛ) joinLift_bijective
  rw [← e1.prod_comp]
  simp only [Fintype.prod_sum_type, Finset.univ_eq_attach]
  rfl

@[simp]
lemma join_fstFieldOfContract_joinLiftRight {φs : List 𝓕.States} (φsΛ : WickContraction φs.length)
    (φsucΛ : WickContraction [φsΛ]ᵘᶜ.length) (a : φsucΛ.1) :
    (join φsΛ φsucΛ).fstFieldOfContract (joinLiftRight a) =
    uncontractedListEmd (φsucΛ.fstFieldOfContract a) := by
  apply eq_fstFieldOfContract_of_mem _ _ _ (uncontractedListEmd (φsucΛ.sndFieldOfContract a))
  · simp [joinLiftRight]
  · simp [joinLiftRight]
  · apply uncontractedListEmd_strictMono
    exact fstFieldOfContract_lt_sndFieldOfContract φsucΛ a

@[simp]
lemma join_sndFieldOfContract_joinLiftRight {φs : List 𝓕.States} (φsΛ : WickContraction φs.length)
    (φsucΛ : WickContraction [φsΛ]ᵘᶜ.length) (a : φsucΛ.1) :
    (join φsΛ φsucΛ).sndFieldOfContract (joinLiftRight a) =
    uncontractedListEmd (φsucΛ.sndFieldOfContract a) := by
  apply eq_sndFieldOfContract_of_mem _ _ (uncontractedListEmd (φsucΛ.fstFieldOfContract a))
  · simp [joinLiftRight]
  · simp [joinLiftRight]
  · apply uncontractedListEmd_strictMono
    exact fstFieldOfContract_lt_sndFieldOfContract φsucΛ a

@[simp]
lemma join_fstFieldOfContract_joinLiftLeft {φs : List 𝓕.States} (φsΛ : WickContraction φs.length)
    (φsucΛ : WickContraction [φsΛ]ᵘᶜ.length) (a : φsΛ.1) :
    (join φsΛ φsucΛ).fstFieldOfContract (joinLiftLeft a) =
    (φsΛ.fstFieldOfContract a) := by
  apply eq_fstFieldOfContract_of_mem _ _ _ (φsΛ.sndFieldOfContract a)
  · simp [joinLiftLeft]
  · simp [joinLiftLeft]
  · exact fstFieldOfContract_lt_sndFieldOfContract φsΛ a

@[simp]
lemma join_sndFieldOfContract_joinLift {φs : List 𝓕.States} (φsΛ : WickContraction φs.length)
    (φsucΛ : WickContraction [φsΛ]ᵘᶜ.length) (a : φsΛ.1) :
    (join φsΛ φsucΛ).sndFieldOfContract (joinLiftLeft a) =
    (φsΛ.sndFieldOfContract a) := by
  apply eq_sndFieldOfContract_of_mem _ _ (φsΛ.fstFieldOfContract a) (φsΛ.sndFieldOfContract a)
  · simp [joinLiftLeft]
  · simp [joinLiftLeft]
  · exact fstFieldOfContract_lt_sndFieldOfContract φsΛ a


lemma join_card {φs : List 𝓕.States} {φsΛ : WickContraction φs.length}
    {φsucΛ : WickContraction [φsΛ]ᵘᶜ.length} :
    (join φsΛ φsucΛ).1.card = φsΛ.1.card + φsucΛ.1.card := by
  simp [join]
  rw [Finset.card_union_of_disjoint]
  simp
  rw [@Finset.disjoint_left]
  intro a ha
  simp
  intro x hx
  by_contra hn
  have hdis : Disjoint (Finset.map uncontractedListEmd x)  a := by
    exact uncontractedListEmd_finset_disjoint_left x a ha
  rw [Finset.mapEmbedding_apply] at hn
  rw [hn] at hdis
  simp at hdis
  have hcard := φsΛ.2.1 a ha
  simp_all

@[simp]
lemma empty_join {φs : List 𝓕.States} (φsΛ : WickContraction [empty (n := φs.length)]ᵘᶜ.length) :
    join empty φsΛ = congr (by simp) φsΛ := by
  apply Subtype.ext
  simp [join]
  ext a
  conv_lhs =>
    left
    left
    rw [empty]
  simp
  rw [mem_congr_iff]
  apply Iff.intro
  · intro h
    obtain ⟨a, ha, rfl⟩ := h
    rw [Finset.mapEmbedding_apply]
    rw [Finset.map_map]
    apply Set.mem_of_eq_of_mem _ ha
    trans Finset.map (Equiv.refl _).toEmbedding a
    rfl
    simp
  · intro h
    use Finset.map (finCongr (by simp)).toEmbedding a
    simp [h]
    trans Finset.map (Equiv.refl _).toEmbedding a
    rw [Finset.mapEmbedding_apply, Finset.map_map]
    rfl
    simp

@[simp]
lemma join_empty {φs : List 𝓕.States} (φsΛ : WickContraction φs.length) :
    join φsΛ empty = φsΛ := by
  apply Subtype.ext
  ext a
  simp [join, empty]

lemma join_timeContract {φs : List 𝓕.States} (φsΛ : WickContraction φs.length)
    (φsucΛ : WickContraction [φsΛ]ᵘᶜ.length) :
    (join φsΛ φsucΛ).timeContract = φsΛ.timeContract * φsucΛ.timeContract := by
  simp only [timeContract, List.get_eq_getElem]
  rw [prod_join]
  congr 1
  congr
  funext a
  simp

lemma mem_join_uncontracted_of_mem_right_uncontracted {φs : List 𝓕.States}
    (φsΛ : WickContraction φs.length)
    (φsucΛ : WickContraction [φsΛ]ᵘᶜ.length) (i : Fin [φsΛ]ᵘᶜ.length)
    (ha : i ∈ φsucΛ.uncontracted) :
    uncontractedListEmd i ∈ (join φsΛ φsucΛ).uncontracted := by
  rw [mem_uncontracted_iff_not_contracted]
  intro p hp
  simp [join] at hp
  rcases hp with hp | hp
  · have hi :  uncontractedListEmd i  ∈ φsΛ.uncontracted := by
      exact uncontractedListEmd_mem_uncontracted i
    rw [mem_uncontracted_iff_not_contracted] at hi
    exact hi p hp
  · obtain ⟨p, hp, rfl⟩ := hp
    rw [Finset.mapEmbedding_apply]
    simp
    rw [mem_uncontracted_iff_not_contracted] at ha
    exact ha p hp

lemma exists_mem_left_uncontracted_of_mem_join_uncontracted {φs : List 𝓕.States}
    (φsΛ : WickContraction φs.length)
    (φsucΛ : WickContraction [φsΛ]ᵘᶜ.length) (i : Fin φs.length)
    (ha : i ∈ (join φsΛ φsucΛ).uncontracted) :
    i ∈ φsΛ.uncontracted := by
  rw [@mem_uncontracted_iff_not_contracted]
  rw [@mem_uncontracted_iff_not_contracted] at ha
  simp [join] at ha
  intro p hp
  have hp' := ha p
  simp_all

lemma exists_mem_right_uncontracted_of_mem_join_uncontracted {φs : List 𝓕.States}
    (φsΛ : WickContraction φs.length)
    (φsucΛ : WickContraction [φsΛ]ᵘᶜ.length) (i : Fin φs.length)
    (hi : i ∈ (join φsΛ φsucΛ).uncontracted) :
    ∃ a, uncontractedListEmd a = i ∧ a ∈ φsucΛ.uncontracted := by
  have hi' := exists_mem_left_uncontracted_of_mem_join_uncontracted _ _ i hi
  obtain ⟨j, rfl⟩ := uncontractedListEmd_surjective_mem_uncontracted i hi'
  use j
  simp
  rw [mem_uncontracted_iff_not_contracted] at hi
  rw [mem_uncontracted_iff_not_contracted]
  intro p hp
  have hip := hi (p.map uncontractedListEmd) (by
    simp [join]
    right
    use p
    simp [hp]
    rw [Finset.mapEmbedding_apply])
  simpa using hip

lemma join_uncontractedList {φs : List 𝓕.States} (φsΛ : WickContraction φs.length)
    (φsucΛ : WickContraction [φsΛ]ᵘᶜ.length) :
    (join φsΛ φsucΛ).uncontractedList = List.map uncontractedListEmd φsucΛ.uncontractedList := by
  rw [uncontractedList_eq_sort]
  rw [uncontractedList_eq_sort]
  rw [fin_finset_sort_map_monotone]
  congr
  ext a
  simp
  apply Iff.intro
  · intro h
    obtain ⟨a, rfl, ha⟩ := exists_mem_right_uncontracted_of_mem_join_uncontracted _ _ a h
    use a, ha
  · intro h
    obtain ⟨a, ha, rfl⟩ := h
    exact mem_join_uncontracted_of_mem_right_uncontracted φsΛ φsucΛ a ha
  · intro a b h
    exact uncontractedListEmd_strictMono h

lemma join_uncontractedList_get {φs : List 𝓕.States} (φsΛ : WickContraction φs.length)
    (φsucΛ : WickContraction [φsΛ]ᵘᶜ.length) :
    ((join φsΛ φsucΛ).uncontractedList).get =
    φsΛ.uncontractedListEmd ∘  (φsucΛ.uncontractedList).get ∘ (
        Fin.cast (by rw [join_uncontractedList]; simp) ):= by
  have  h1 {n : ℕ} (l1 l2 : List (Fin  n)) (h : l1 = l2) :   l1.get = l2.get ∘ Fin.cast (by rw [h]):= by
    subst h
    rfl
  have hl := h1 _ _ (join_uncontractedList φsΛ φsucΛ)
  conv_lhs => rw [h1 _ _ (join_uncontractedList φsΛ φsucΛ)]
  ext i
  simp

lemma join_uncontractedListGet {φs : List 𝓕.States} (φsΛ : WickContraction φs.length)
    (φsucΛ : WickContraction [φsΛ]ᵘᶜ.length) :
    (join φsΛ φsucΛ).uncontractedListGet = φsucΛ.uncontractedListGet := by
  simp [uncontractedListGet, join_uncontractedList]
  intro a ha
  simp [uncontractedListEmd, uncontractedIndexEquiv]
  rfl

lemma join_uncontractedListEmb  {φs : List 𝓕.States} (φsΛ : WickContraction φs.length)
    (φsucΛ : WickContraction [φsΛ]ᵘᶜ.length) :
    (join φsΛ φsucΛ).uncontractedListEmd =
    ((finCongr (congrArg List.length (join_uncontractedListGet _ _))).toEmbedding.trans φsucΛ.uncontractedListEmd).trans φsΛ.uncontractedListEmd := by
  refine Function.Embedding.ext_iff.mpr (congrFun ?_)
  change uncontractedListEmd.toFun = _
  rw [uncontractedListEmd_toFun_eq_get]
  rw [join_uncontractedList_get]
  rfl

lemma join_assoc {φs : List 𝓕.States} (φsΛ : WickContraction φs.length)
    (φsucΛ : WickContraction [φsΛ]ᵘᶜ.length) (φsucΛ' : WickContraction [φsΛ.join φsucΛ]ᵘᶜ.length) :
    join (join φsΛ φsucΛ) (φsucΛ') = join φsΛ (join φsucΛ (congr
      (congrArg List.length (join_uncontractedListGet _ _)) φsucΛ')) := by
  apply Subtype.ext
  ext a
  by_cases ha : a ∈ φsΛ.1
  · simp [ha, join]
  simp [ha, join]
  apply Iff.intro
  · intro h
    rcases h with h | h
    · obtain ⟨a, ha', rfl⟩ := h
      use a
      simp [ha']
    · obtain ⟨a, ha', rfl⟩ := h
      let a' := congrLift (congrArg List.length (join_uncontractedListGet _ _))  ⟨a, ha'⟩
      let a'' := joinLiftRight  a'
      use a''
      apply And.intro
      · right
        use a'
        apply And.intro
        · exact a'.2
        · simp only [joinLiftRight, a'']
          rfl
      · simp only [a'']
        rw [Finset.mapEmbedding_apply, Finset.mapEmbedding_apply]
        simp only [a', joinLiftRight, congrLift]
        rw [join_uncontractedListEmb]
        simp [Finset.map_map]
  · intro h
    obtain ⟨a, ha', rfl⟩ := h
    rcases ha' with ha' | ha'
    · left
      use a
    · obtain ⟨a, ha', rfl⟩ := ha'
      right
      let a' := congrLiftInv _ ⟨a, ha'⟩
      use a'
      simp
      simp only [a']
      rw [Finset.mapEmbedding_apply]
      rw [join_uncontractedListEmb]
      simp only [congrLiftInv, ← Finset.map_map]
      congr
      rw [Finset.map_map]
      change Finset.map (Equiv.refl _).toEmbedding a = _
      simp only [Equiv.refl_toEmbedding, Finset.map_refl]

@[simp]
lemma join_getDual?_apply_uncontractedListEmb_eq_none_iff  {φs : List 𝓕.States} (φsΛ : WickContraction φs.length)
    (φsucΛ : WickContraction [φsΛ]ᵘᶜ.length) (i : Fin [φsΛ]ᵘᶜ.length) :
    (join φsΛ φsucΛ).getDual?  (uncontractedListEmd i) = none
    ↔ φsucΛ.getDual? i = none := by
  rw [getDual?_eq_none_iff_mem_uncontracted, getDual?_eq_none_iff_mem_uncontracted]
  apply Iff.intro
  · intro h
    obtain ⟨a, ha', ha⟩ := exists_mem_right_uncontracted_of_mem_join_uncontracted _ _ (uncontractedListEmd i) h
    simp at ha'
    subst ha'
    exact ha
  · intro h
    exact mem_join_uncontracted_of_mem_right_uncontracted φsΛ φsucΛ i h

@[simp]
lemma join_getDual?_apply_uncontractedListEmb_isSome_iff {φs : List 𝓕.States} (φsΛ : WickContraction φs.length)
    (φsucΛ : WickContraction [φsΛ]ᵘᶜ.length) (i : Fin [φsΛ]ᵘᶜ.length) :
     ((join φsΛ φsucΛ).getDual?  (uncontractedListEmd i)).isSome
    ↔ (φsucΛ.getDual? i).isSome := by
  rw [← Decidable.not_iff_not]
  simp

lemma join_getDual?_apply_uncontractedListEmb_some {φs : List 𝓕.States} (φsΛ : WickContraction φs.length)
    (φsucΛ : WickContraction [φsΛ]ᵘᶜ.length) (i : Fin [φsΛ]ᵘᶜ.length)
    (hi :((join φsΛ φsucΛ).getDual?  (uncontractedListEmd i)).isSome) :
    ((join φsΛ φsucΛ).getDual?  (uncontractedListEmd i)) =
    some (uncontractedListEmd ((φsucΛ.getDual? i).get (by simpa using hi)))  := by
  rw [getDual?_eq_some_iff_mem]
  simp [join]
  right
  use {i, (φsucΛ.getDual? i).get (by simpa using hi)}
  simp
  rw [Finset.mapEmbedding_apply]
  simp

@[simp]
lemma join_getDual?_apply_uncontractedListEmb {φs : List 𝓕.States} (φsΛ : WickContraction φs.length)
    (φsucΛ : WickContraction [φsΛ]ᵘᶜ.length) (i : Fin [φsΛ]ᵘᶜ.length) :
    ((join φsΛ φsucΛ).getDual?  (uncontractedListEmd i)) = Option.map uncontractedListEmd (φsucΛ.getDual? i) := by
  by_cases h : (φsucΛ.getDual? i).isSome
  · rw [join_getDual?_apply_uncontractedListEmb_some]
    have h1 : (φsucΛ.getDual? i)  =(φsucΛ.getDual? i).get (by simpa using h) :=
      Eq.symm (Option.some_get h)
    conv_rhs => rw [h1]
    simp  [- Option.some_get]
    exact (join_getDual?_apply_uncontractedListEmb_isSome_iff φsΛ φsucΛ i).mpr h
  · simp only [Bool.not_eq_true, Option.not_isSome, Option.isNone_iff_eq_none] at h
    rw [h]
    simp
    exact h

/-!

## Subcontractions and quotient contractions

-/

section

variable {φs : List 𝓕.States} (φsΛ : WickContraction φs.length)

lemma join_sub_quot (S : Finset (Finset (Fin φs.length))) (ha : S ⊆ φsΛ.1) :
    join (subContraction S ha) (quotContraction S ha) = φsΛ := by
  apply Subtype.ext
  ext a
  simp [join]
  apply Iff.intro
  · intro h
    rcases h with h | h
    · exact mem_of_mem_subContraction h
    · obtain ⟨a, ha, rfl⟩ := h
      apply mem_of_mem_quotContraction ha
  · intro h
    have h1 := mem_subContraction_or_quotContraction (S := S) (a := a) (hs := ha) h
    rcases h1 with h1 | h1
    · simp [h1]
    · right
      obtain ⟨a, rfl, ha⟩ := h1
      use a
      simp [ha]
      rw [Finset.mapEmbedding_apply]

lemma subContraction_card_plus_quotContraction_card_eq (S : Finset (Finset (Fin φs.length)))
    (ha : S ⊆ φsΛ.1) :
    (subContraction S ha).1.card + (quotContraction S ha).1.card = φsΛ.1.card := by
  rw [← join_card]
  simp [join_sub_quot]

end
open FieldStatistic

lemma stat_signFinset_right {φs : List 𝓕.States} (φsΛ : WickContraction φs.length)
    (φsucΛ : WickContraction [φsΛ]ᵘᶜ.length) (i j : Fin [φsΛ]ᵘᶜ.length) :
    (𝓕 |>ₛ ⟨[φsΛ]ᵘᶜ.get, φsucΛ.signFinset i j⟩) =
    (𝓕 |>ₛ ⟨φs.get, (φsucΛ.signFinset i j).map uncontractedListEmd⟩) := by
  simp [ofFinset]
  congr 1
  rw [← fin_finset_sort_map_monotone]
  simp
  intro i j h
  exact uncontractedListEmd_strictMono h

lemma signFinset_right_map_uncontractedListEmd_eq_filter {φs : List 𝓕.States}
    (φsΛ : WickContraction φs.length) (φsucΛ : WickContraction [φsΛ]ᵘᶜ.length)
    (i j : Fin [φsΛ]ᵘᶜ.length) : (φsucΛ.signFinset i j).map uncontractedListEmd =
    ((join φsΛ φsucΛ).signFinset (uncontractedListEmd i) (uncontractedListEmd j)).filter
    (fun c => c ∈ φsΛ.uncontracted) := by
  ext a
  simp
  apply Iff.intro
  · intro h
    obtain ⟨a, ha, rfl⟩ := h
    apply And.intro
    · simp_all [signFinset]
      apply And.intro
      · exact uncontractedListEmd_strictMono ha.1
      · apply And.intro
        · exact uncontractedListEmd_strictMono ha.2.1
        · have ha2 := ha.2.2
          simp_all
          rcases ha2 with ha2 | ha2
          · simp [ha2]
          · right
            intro h
            have h1 : (φsucΛ.getDual? a) = some ((φsucΛ.getDual? a).get h) :=
              Eq.symm (Option.some_get h)
            apply lt_of_lt_of_eq (uncontractedListEmd_strictMono (ha2 h))
            rw [Option.get_map]
    · exact uncontractedListEmd_mem_uncontracted a
  · intro h
    have h2 := h.2
    have h2' := uncontractedListEmd_surjective_mem_uncontracted a h.2
    obtain ⟨a, rfl⟩ := h2'
    use a
    have h1 := h.1
    simp_all [signFinset]
    apply And.intro
    · have h1 := h.1
      rw [StrictMono.lt_iff_lt] at h1
      exact h1
      exact fun _ _ h => uncontractedListEmd_strictMono h
    · apply And.intro
      · have h1 := h.2.1
        rw [StrictMono.lt_iff_lt] at h1
        exact h1
        exact fun _ _ h => uncontractedListEmd_strictMono h
      · have h1 := h.2.2
        simp_all
        rcases h1 with h1 | h1
        · simp [h1]
        · right
          intro h
          have h1' := h1 h
          have hl : uncontractedListEmd i < uncontractedListEmd ((φsucΛ.getDual? a).get h) := by
            apply lt_of_lt_of_eq h1'
            simp [Option.get_map]
          rw [StrictMono.lt_iff_lt] at hl
          exact hl
          exact fun _ _ h => uncontractedListEmd_strictMono h

lemma sign_right_eq_prod_mul_prod {φs : List 𝓕.States} (φsΛ : WickContraction φs.length)
    (φsucΛ : WickContraction [φsΛ]ᵘᶜ.length) :
    φsucΛ.sign = (∏ a, 𝓢(𝓕|>ₛ [φsΛ]ᵘᶜ[φsucΛ.sndFieldOfContract a], 𝓕|>ₛ ⟨φs.get ,
    ((join φsΛ φsucΛ).signFinset (uncontractedListEmd (φsucΛ.fstFieldOfContract a)) (uncontractedListEmd (φsucΛ.sndFieldOfContract a))).filter
      (fun c => ¬  c ∈ φsΛ.uncontracted)⟩)) *
    (∏ a, 𝓢(𝓕|>ₛ [φsΛ]ᵘᶜ[φsucΛ.sndFieldOfContract a], 𝓕|>ₛ ⟨φs.get ,
      ((join φsΛ φsucΛ).signFinset (uncontractedListEmd (φsucΛ.fstFieldOfContract a))
        (uncontractedListEmd (φsucΛ.sndFieldOfContract a)))⟩)) := by
  rw [← Finset.prod_mul_distrib, sign]
  congr
  funext a
  rw [← map_mul]
  congr
  rw [stat_signFinset_right, signFinset_right_map_uncontractedListEmd_eq_filter]
  rw [ofFinset_filter]

lemma join_singleton_signFinset_eq_filter {φs : List 𝓕.States}
    {i j : Fin φs.length} (h : i < j)
    (φsucΛ : WickContraction [singleton h]ᵘᶜ.length)  :
    (join (singleton h) φsucΛ).signFinset i j =
    ((singleton h).signFinset i j).filter (fun c => ¬
    (((join (singleton h) φsucΛ).getDual? c).isSome ∧
    ((h1 : ((join (singleton h) φsucΛ).getDual? c).isSome) →
    (((join (singleton h) φsucΛ).getDual? c).get h1) < i))) := by
  ext a
  simp [signFinset, and_assoc]
  intro h1 h2
  have h1 : (singleton h).getDual? a = none  := by
    rw [singleton_getDual?_eq_none_iff_neq]
    omega
  simp [h1]
  apply Iff.intro
  · intro h1 h2
    rcases h1 with h1 | h1
    · simp [h1]
      have h2' : ¬  (((singleton h).join φsucΛ).getDual? a).isSome := by
        exact Option.not_isSome_iff_eq_none.mpr h1
      exact h2' h2
    use h2
    have h1 := h1 h2
    omega
  · intro h2
    by_cases h2' :  (((singleton h).join φsucΛ).getDual? a).isSome = true
    · have h2 := h2 h2'
      obtain ⟨hb, h2⟩ := h2
      right
      intro hl
      apply lt_of_le_of_ne h2
      by_contra hn
      have hij : ((singleton h).join φsucΛ).getDual? i = j := by
        rw [@getDual?_eq_some_iff_mem]
        simp [join, singleton]
      simp [hn] at hij
      omega
    · simp at h2'
      simp [h2']


lemma join_singleton_left_signFinset_eq_filter {φs : List 𝓕.States}
    {i j : Fin φs.length} (h : i < j)
    (φsucΛ : WickContraction [singleton h]ᵘᶜ.length)  :
    (𝓕 |>ₛ ⟨φs.get, (singleton h).signFinset i j⟩)
    = (𝓕 |>ₛ ⟨φs.get, (join (singleton h) φsucΛ).signFinset i j⟩) *
      (𝓕 |>ₛ ⟨φs.get, ((singleton h).signFinset i j).filter (fun c =>
      (((join (singleton h) φsucΛ).getDual? c).isSome ∧
      ((h1 : ((join (singleton h) φsucΛ).getDual? c).isSome) →
      (((join (singleton h) φsucΛ).getDual? c).get h1) < i)))⟩) := by
  conv_rhs =>
    left
    rw [join_singleton_signFinset_eq_filter]
  rw [mul_comm]
  exact (ofFinset_filter_mul_neg 𝓕.statesStatistic _ _ _).symm

def joinSignRightExtra {φs : List 𝓕.States}
    {i j : Fin φs.length} (h : i < j)
    (φsucΛ : WickContraction [singleton h]ᵘᶜ.length)  : ℂ :=
    ∏ a, 𝓢(𝓕|>ₛ [singleton h]ᵘᶜ[φsucΛ.sndFieldOfContract a], 𝓕|>ₛ ⟨φs.get ,
    ((join (singleton h) φsucΛ).signFinset (uncontractedListEmd (φsucΛ.fstFieldOfContract a))
    (uncontractedListEmd (φsucΛ.sndFieldOfContract a))).filter
    (fun c => ¬  c ∈ (singleton h).uncontracted)⟩)


def joinSignLeftExtra {φs : List 𝓕.States}
    {i j : Fin φs.length} (h : i < j)
    (φsucΛ : WickContraction [singleton h]ᵘᶜ.length)  : ℂ :=
    𝓢(𝓕 |>ₛ φs[j], (𝓕 |>ₛ ⟨φs.get, ((singleton h).signFinset i j).filter (fun c =>
      (((join (singleton h) φsucΛ).getDual? c).isSome ∧
      ((h1 : ((join (singleton h) φsucΛ).getDual? c).isSome) →
      (((join (singleton h) φsucΛ).getDual? c).get h1) < i)))⟩))

lemma join_singleton_sign_left {φs : List 𝓕.States}
    {i j : Fin φs.length} (h : i < j)
    (φsucΛ : WickContraction [singleton h]ᵘᶜ.length)  :
    (singleton h).sign = 𝓢(𝓕 |>ₛ φs[j], (𝓕 |>ₛ ⟨φs.get, (join (singleton h) φsucΛ).signFinset i j⟩)) *
    (joinSignLeftExtra h φsucΛ) := by
  rw [singleton_sign_expand]
  rw [join_singleton_left_signFinset_eq_filter h φsucΛ]
  rw [map_mul]
  rfl


lemma join_singleton_sign_right {φs : List 𝓕.States}
    {i j : Fin φs.length} (h : i < j)
    (φsucΛ : WickContraction [singleton h]ᵘᶜ.length)  :
    φsucΛ.sign =
    (joinSignRightExtra h φsucΛ) *
    (∏ a, 𝓢(𝓕|>ₛ [singleton h]ᵘᶜ[φsucΛ.sndFieldOfContract a], 𝓕|>ₛ ⟨φs.get ,
      ((join (singleton h) φsucΛ).signFinset (uncontractedListEmd (φsucΛ.fstFieldOfContract a))
        (uncontractedListEmd (φsucΛ.sndFieldOfContract a)))⟩))  := by
  rw [sign_right_eq_prod_mul_prod]
  rfl

@[simp]
lemma join_singleton_getDual?_left {φs : List 𝓕.States}
    {i j : Fin φs.length} (h : i < j)
    (φsucΛ : WickContraction [singleton h]ᵘᶜ.length)  :
    (join (singleton h) φsucΛ).getDual? i = some j := by
  rw [@getDual?_eq_some_iff_mem]
  simp [singleton, join]

@[simp]
lemma join_singleton_getDual?_right {φs : List 𝓕.States}
    {i j : Fin φs.length} (h : i < j)
    (φsucΛ : WickContraction [singleton h]ᵘᶜ.length)  :
    (join (singleton h) φsucΛ).getDual? j = some i := by
  rw [@getDual?_eq_some_iff_mem]
  simp [singleton, join]
  left
  exact Finset.pair_comm j i


lemma joinSignRightExtra_eq_i_j_finset_eq_if {φs : List 𝓕.States}
    {i j : Fin φs.length} (h : i < j)
    (φsucΛ : WickContraction [singleton h]ᵘᶜ.length)  :
    joinSignRightExtra h φsucΛ = ∏ a,
    𝓢((𝓕|>ₛ [singleton h]ᵘᶜ[φsucΛ.sndFieldOfContract a]),
    𝓕 |>ₛ ⟨φs.get, (if uncontractedListEmd (φsucΛ.fstFieldOfContract a) < j ∧
        j < uncontractedListEmd (φsucΛ.sndFieldOfContract a) ∧
        uncontractedListEmd (φsucΛ.fstFieldOfContract a) < i  then {j} else ∅)
        ∪ (if uncontractedListEmd (φsucΛ.fstFieldOfContract a) < i ∧
        i < uncontractedListEmd (φsucΛ.sndFieldOfContract a)  then {i} else ∅)⟩) := by
  rw [joinSignRightExtra]
  congr
  funext a
  congr
  rw [signFinset]
  rw [Finset.filter_comm]
  have h11 : (Finset.filter (fun c => c ∉ (singleton h).uncontracted) Finset.univ) = {i, j} := by
    ext x
    simp
    rw [@mem_uncontracted_iff_not_contracted]
    simp [singleton]
    omega
  rw [h11]
  ext x
  simp
  have hjneqfst := singleton_uncontractedEmd_neq_right h (φsucΛ.fstFieldOfContract a)
  have hjneqsnd := singleton_uncontractedEmd_neq_right h (φsucΛ.sndFieldOfContract a)
  have hineqfst := singleton_uncontractedEmd_neq_left h (φsucΛ.fstFieldOfContract a)
  have hineqsnd := singleton_uncontractedEmd_neq_left h (φsucΛ.sndFieldOfContract a)
  by_cases hj1 : ¬ uncontractedListEmd (φsucΛ.fstFieldOfContract a) < j
  · simp [hj1]
    have hi1 : ¬ uncontractedListEmd (φsucΛ.fstFieldOfContract a) < i := by omega
    simp [hi1]
    intro hxij h1 h2
    omega
  · have hj1 : uncontractedListEmd (φsucΛ.fstFieldOfContract a) < j := by
      omega
    by_cases hi1 : ¬ i < uncontractedListEmd (φsucΛ.sndFieldOfContract a)
    · simp [hi1]
      have hj2 : ¬ j < uncontractedListEmd (φsucΛ.sndFieldOfContract a) := by omega
      simp [hj2]
      intro hxij h1 h2
      omega
    · have hi1 : i < uncontractedListEmd (φsucΛ.sndFieldOfContract a) := by
        omega
      simp [hi1, hj1]
      by_cases hi2 : ¬  uncontractedListEmd (φsucΛ.fstFieldOfContract a) < i
      · simp [hi2]
        by_cases hj3 : ¬ j < uncontractedListEmd (φsucΛ.sndFieldOfContract a)
        · omega
        · have hj4 : j < uncontractedListEmd (φsucΛ.sndFieldOfContract a) := by omega
          intro h
          rcases h with h | h
          · subst h
            omega
          · subst h
            simp
            omega
      · have hi2 : uncontractedListEmd (φsucΛ.fstFieldOfContract a) < i := by omega
        simp [hi2]
        by_cases hj3 : ¬ j < uncontractedListEmd (φsucΛ.sndFieldOfContract a)
        · simp [hj3]
          apply Iff.intro
          · intro h
            omega
          · intro h
            subst h
            simp
            omega
        · have hj3 : j < uncontractedListEmd (φsucΛ.sndFieldOfContract a) := by omega
          simp [hj3]
          apply Iff.intro
          · intro h
            omega
          · intro h
            rcases h with h1 | h1
            · subst h1
              simp
              omega
            · subst h1
              simp
              omega


lemma joinSignLeftExtra_eq_joinSignRightExtra {φs : List 𝓕.States}
    {i j : Fin φs.length} (h : i < j) (hs : (𝓕 |>ₛ φs[i]) = (𝓕 |>ₛ φs[j]))
    (φsucΛ : WickContraction [singleton h]ᵘᶜ.length) :
    joinSignLeftExtra h φsucΛ = joinSignRightExtra h φsucΛ := by
  /- Simplifying joinSignLeftExtra. -/
  rw [joinSignLeftExtra]
  rw [ofFinset_eq_prod]
  rw [map_prod]
  let e2 : Fin φs.length ≃ {x // (((singleton h).join φsucΛ).getDual? x).isSome} ⊕ {x // ¬ (((singleton h).join φsucΛ).getDual? x).isSome} := by
    exact (Equiv.sumCompl fun a => (((singleton h).join φsucΛ).getDual? a).isSome = true).symm
  rw [← e2.symm.prod_comp]
  simp only [Fin.getElem_fin, Fintype.prod_sum_type, instCommGroup]
  conv_lhs =>
    enter [2, 2, x]
    simp only [Equiv.symm_symm, Equiv.sumCompl_apply_inl, Equiv.sumCompl_apply_inr, e2]
    rw [if_neg (
        by
        simp
        intro h1 h2
        have hx := x.2
        simp_all)]
  simp
  rw [← ((singleton h).join φsucΛ).sigmaContractedEquiv.prod_comp]
  erw [Finset.prod_sigma]
  conv_lhs =>
    enter [2, a]
    rw [prod_finset_eq_mul_fst_snd]
    simp [e2, sigmaContractedEquiv]
  rw [prod_join]
  rw [singleton_prod]
  simp only [join_fstFieldOfContract_joinLiftLeft, singleton_fstFieldOfContract,
    join_sndFieldOfContract_joinLift, singleton_sndFieldOfContract, lt_self_iff_false, and_false,
    ↓reduceIte, map_one, mul_one, join_fstFieldOfContract_joinLiftRight,
    join_sndFieldOfContract_joinLiftRight, getElem_uncontractedListEmd]
  rw [if_neg (by omega)]
  simp only [map_one, one_mul]
  /- Introducing joinSignRightExtra. -/
  rw [joinSignRightExtra_eq_i_j_finset_eq_if]
  congr
  funext a
  have hjneqfst := singleton_uncontractedEmd_neq_right h (φsucΛ.fstFieldOfContract a)
  have hjneqsnd := singleton_uncontractedEmd_neq_right h (φsucΛ.sndFieldOfContract a)
  have hineqfst := singleton_uncontractedEmd_neq_left h (φsucΛ.fstFieldOfContract a)
  have hineqsnd := singleton_uncontractedEmd_neq_left h (φsucΛ.sndFieldOfContract a)
  have hl : uncontractedListEmd (φsucΛ.fstFieldOfContract a) < uncontractedListEmd (φsucΛ.sndFieldOfContract a)  := by
    apply uncontractedListEmd_strictMono
    exact fstFieldOfContract_lt_sndFieldOfContract φsucΛ a
  by_cases hj1 : ¬ uncontractedListEmd (φsucΛ.fstFieldOfContract a) < j
  · have hi1 : ¬ uncontractedListEmd (φsucΛ.fstFieldOfContract a) < i := by omega
    simp [hj1, hi1]
  · have hj1 : uncontractedListEmd (φsucΛ.fstFieldOfContract a) < j := by omega
    simp [hj1]
    by_cases hi2 : ¬ i < uncontractedListEmd (φsucΛ.sndFieldOfContract a)
    · have hi1 :  ¬ i < uncontractedListEmd (φsucΛ.fstFieldOfContract a) := by omega
      have hj2 : ¬ j < uncontractedListEmd (φsucΛ.sndFieldOfContract a) := by omega
      simp [hi2, hj2, hi1]
    · have hi2 : i < uncontractedListEmd (φsucΛ.sndFieldOfContract a) := by omega
      have hi2n : ¬ uncontractedListEmd (φsucΛ.sndFieldOfContract a) < i := by omega
      simp [hi2, hi2n]
      by_cases hj2 : ¬ j < uncontractedListEmd (φsucΛ.sndFieldOfContract a)
      · simp [hj2]
        have hj2 :  uncontractedListEmd (φsucΛ.sndFieldOfContract a) < j:= by omega
        simp [hj2]
        by_cases hi1 : ¬ uncontractedListEmd (φsucΛ.fstFieldOfContract a) < i
        · simp [hi1]
        · have hi1 : uncontractedListEmd (φsucΛ.fstFieldOfContract a) < i := by omega
          simp [hi1, ofFinset_singleton]
          erw [hs]
          exact exchangeSign_symm (𝓕|>ₛφs[↑j]) (𝓕|>ₛ[singleton h]ᵘᶜ[↑(φsucΛ.sndFieldOfContract a)])
      · simp  at hj2
        simp [hj2]
        by_cases hi1 : ¬ uncontractedListEmd (φsucΛ.fstFieldOfContract a) < i
        · simp [hi1]
        · have hi1 : uncontractedListEmd (φsucΛ.fstFieldOfContract a) < i := by omega
          simp [hi1]
          have hj2 : ¬  uncontractedListEmd (φsucΛ.sndFieldOfContract a) < j := by omega
          simp [hj2]
          rw [← ofFinset_union_disjoint]
          simp only [instCommGroup, ofFinset_singleton, List.get_eq_getElem, hs]
          erw [hs]
          simp
          simp
          omega

lemma join_sign_singleton {φs : List 𝓕.States}
    {i j : Fin φs.length} (h : i < j) (hs : (𝓕 |>ₛ φs[i]) = (𝓕 |>ₛ φs[j]))
    (φsucΛ : WickContraction [singleton h]ᵘᶜ.length) :
    (join (singleton h) φsucΛ).sign = (singleton h).sign * φsucΛ.sign := by
  rw [join_singleton_sign_right]
  rw [join_singleton_sign_left h φsucΛ]
  rw [joinSignLeftExtra_eq_joinSignRightExtra h hs φsucΛ]
  rw [← mul_assoc]
  rw [mul_assoc _ _ (joinSignRightExtra h φsucΛ)]
  have h1 : (joinSignRightExtra h φsucΛ * joinSignRightExtra h φsucΛ) = 1 := by
    rw [← joinSignLeftExtra_eq_joinSignRightExtra h hs φsucΛ]
    simp [joinSignLeftExtra]
  simp only [instCommGroup, Fin.getElem_fin, h1, mul_one]
  rw [sign]
  rw [prod_join]
  congr
  · rw [singleton_prod]
    simp
  · funext a
    simp

lemma exists_contraction_pair_of_card_ge_zero {φs : List 𝓕.States} (φsΛ : WickContraction φs.length)
    (h : 0 < φsΛ.1.card) :
    ∃ a, a ∈ φsΛ.1 := by
  simpa using h

lemma exists_join_singleton_of_card_ge_zero {φs : List 𝓕.States} (φsΛ : WickContraction φs.length)
    (h : 0 < φsΛ.1.card) (hc : φsΛ.GradingCompliant) :
    ∃ (i j : Fin φs.length) (h : i < j) (φsucΛ : WickContraction [singleton h]ᵘᶜ.length),
    φsΛ = join (singleton h) φsucΛ ∧ (𝓕 |>ₛ φs[i]) = (𝓕 |>ₛ φs[j])
    ∧ φsucΛ.GradingCompliant ∧ φsucΛ.1.card + 1 = φsΛ.1.card := by
  obtain ⟨a, ha⟩ := exists_contraction_pair_of_card_ge_zero φsΛ h
  use φsΛ.fstFieldOfContract ⟨a, ha⟩
  use φsΛ.sndFieldOfContract ⟨a, ha⟩
  use φsΛ.fstFieldOfContract_lt_sndFieldOfContract ⟨a, ha⟩
  let φsucΛ :
     WickContraction [singleton (φsΛ.fstFieldOfContract_lt_sndFieldOfContract ⟨a, ha⟩)]ᵘᶜ.length :=
     congr (by simp [← subContraction_singleton_eq_singleton]) (φsΛ.quotContraction {a} (by simpa using ha))
  use φsucΛ
  simp [← subContraction_singleton_eq_singleton]
  apply And.intro
  · have h1 := join_congr (subContraction_singleton_eq_singleton _ ⟨a, ha⟩).symm (φsucΛ := φsucΛ)
    simp [h1, φsucΛ]
    rw [join_sub_quot]
  · apply And.intro  (hc ⟨a, ha⟩)
    apply And.intro
    · simp [φsucΛ]
      rw [gradingCompliant_congr (φs' := [(φsΛ.subContraction {a} (by simpa using ha))]ᵘᶜ)]
      simp
      exact quotContraction_gradingCompliant hc
      rw [← subContraction_singleton_eq_singleton]
    · simp [φsucΛ]
      have h1 := subContraction_card_plus_quotContraction_card_eq _ {a} (by simpa using ha)
      simp [subContraction] at h1
      omega

lemma join_sign_induction {φs : List 𝓕.States} (φsΛ : WickContraction φs.length)
    (φsucΛ : WickContraction [φsΛ]ᵘᶜ.length) (hc : φsΛ.GradingCompliant) :
    (n : ℕ) → (hn : φsΛ.1.card = n) →
    (join φsΛ φsucΛ).sign = φsΛ.sign * φsucΛ.sign
  | 0, hn => by
    rw [@card_zero_iff_empty] at hn
    subst hn
    simp [sign_empty]
    apply sign_congr
    simp
  | Nat.succ n, hn => by
    obtain ⟨i, j, hij, φsucΛ', rfl, h1, h2, h3⟩ := exists_join_singleton_of_card_ge_zero φsΛ (by simp [hn]) hc
    rw [join_assoc]
    rw [join_sign_singleton hij h1 ]
    rw [join_sign_singleton hij h1 ]
    have hn : φsucΛ'.1.card = n   := by
      omega
    rw [join_sign_induction φsucΛ' (congr (by simp [join_uncontractedListGet]) φsucΛ) h2
      n hn]
    rw [mul_assoc]
    simp [sign_congr]
    left
    left
    apply sign_congr
    exact join_uncontractedListGet (singleton hij) φsucΛ'

lemma join_sign {φs : List 𝓕.States} (φsΛ : WickContraction φs.length)
    (φsucΛ : WickContraction [φsΛ]ᵘᶜ.length) (hc : φsΛ.GradingCompliant) :
    (join φsΛ φsucΛ).sign = φsΛ.sign * φsucΛ.sign := by
  exact join_sign_induction φsΛ φsucΛ hc (φsΛ).1.card rfl

end WickContraction
