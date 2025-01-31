/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.WickContraction.TimeContract
import HepLean.PerturbationTheory.WickContraction.StaticContract
import HepLean.PerturbationTheory.Algebras.FieldOpAlgebra.TimeContraction
import HepLean.PerturbationTheory.WickContraction.SubContraction
/-!

# Singleton of contractions

-/

open FieldSpecification
variable {𝓕 : FieldSpecification}

namespace WickContraction
variable {n : ℕ} (c : WickContraction n)
open HepLean.List
open FieldOpAlgebra
open FieldStatistic

def singleton {i j : Fin n} (hij : i < j) : WickContraction n :=
  ⟨{{i, j}}, by
    intro i hi
    simp at hi
    subst hi
    rw [@Finset.card_eq_two]
    use i, j
    simp
    omega
    , by
    intro i hi j hj
    simp_all⟩

lemma mem_singleton {i j : Fin n} (hij : i < j) :
    {i, j} ∈ (singleton  hij).1  := by
  simp [singleton]

lemma mem_singleton_iff {i j : Fin n} (hij : i < j) {a : Finset (Fin n)} :
    a ∈ (singleton  hij).1 ↔ a = {i, j}  := by
  simp [singleton]

@[simp]
lemma of_singleton_eq {i j : Fin n} (hij : i < j) (a : (singleton hij).1):
    a = ⟨{i, j}, mem_singleton hij⟩ := by
  have ha2 := a.2
  rw [@mem_singleton_iff] at ha2
  exact Subtype.coe_eq_of_eq_mk ha2

lemma singleton_prod {φs : List 𝓕.States} {i j : Fin φs.length} (hij : i < j)
    (f : (singleton hij).1 → M) [CommMonoid M]  :
    ∏ a, f a = f ⟨{i,j}, mem_singleton hij⟩:= by
  simp [singleton]

@[simp]
lemma singleton_fstFieldOfContract {i j : Fin n} (hij : i < j) :
    (singleton hij).fstFieldOfContract ⟨{i, j}, mem_singleton hij⟩ = i := by
  refine eq_fstFieldOfContract_of_mem (singleton hij) ⟨{i, j}, mem_singleton hij⟩ i j ?_ ?_ ?_
  · simp
  · simp
  · exact hij

@[simp]
lemma singleton_sndFieldOfContract {i j : Fin n} (hij : i < j) :
    (singleton hij).sndFieldOfContract ⟨{i, j}, mem_singleton hij⟩ = j := by
  refine eq_sndFieldOfContract_of_mem (singleton hij) ⟨{i, j}, mem_singleton hij⟩ i j ?_ ?_ ?_
  · simp
  · simp
  · exact hij

lemma singleton_sign_expand {φs : List 𝓕.States} {i j : Fin φs.length} (hij : i < j) :
    (singleton hij).sign = 𝓢(𝓕 |>ₛ φs[j], 𝓕 |>ₛ ⟨φs.get, (singleton hij).signFinset i j⟩) := by
  rw [sign, singleton_prod]
  simp

lemma singleton_getDual?_eq_none_iff_neq {i j : Fin n} (hij : i < j) (a : Fin n) :
    (singleton hij).getDual? a = none ↔ (i ≠ a ∧ j ≠ a) := by
  rw [getDual?_eq_none_iff_mem_uncontracted]
  rw [mem_uncontracted_iff_not_contracted]
  simp [singleton]
  omega

lemma singleton_uncontractedEmd_neq_left {φs : List 𝓕.States} {i j : Fin φs.length} (hij : i < j)
    (a : Fin [singleton hij]ᵘᶜ.length ) :
    (singleton hij).uncontractedListEmd a ≠ i  := by
  by_contra hn
  have h1 : (singleton hij).uncontractedListEmd a ∈ (singleton hij).uncontracted := by
    simp [uncontractedListEmd]
  have h2 : i ∉  (singleton hij).uncontracted := by
    rw [mem_uncontracted_iff_not_contracted]
    simp [singleton]
  simp_all

lemma singleton_uncontractedEmd_neq_right {φs : List 𝓕.States} {i j : Fin φs.length} (hij : i < j)
    (a : Fin [singleton hij]ᵘᶜ.length ) :
    (singleton hij).uncontractedListEmd a ≠ j  := by
  by_contra hn
  have h1 : (singleton hij).uncontractedListEmd a ∈ (singleton hij).uncontracted := by
    simp [uncontractedListEmd]
  have h2 : j ∉  (singleton hij).uncontracted := by
    rw [mem_uncontracted_iff_not_contracted]
    simp [singleton]
  simp_all

@[simp]
lemma mem_signFinset {i j : Fin n} (hij : i < j) (a : Fin n) :
    a ∈ (singleton hij).signFinset i j ↔ i < a ∧ a < j := by
  simp [signFinset]
  intro h1 h2
  rw [@singleton_getDual?_eq_none_iff_neq]
  apply Or.inl
  omega

lemma subContraction_singleton_eq_singleton {φs : List 𝓕.States}
    (φsΛ : WickContraction φs.length)
    (a : φsΛ.1) : φsΛ.subContraction {a.1} (by simp) =
    singleton (φsΛ.fstFieldOfContract_lt_sndFieldOfContract a) := by
  apply Subtype.ext
  simp [subContraction, singleton]
  exact finset_eq_fstFieldOfContract_sndFieldOfContract φsΛ a

end WickContraction
