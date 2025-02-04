/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.PerturbationTheory.FieldSpecification.CrAnFieldOp
import HepLean.PerturbationTheory.FieldSpecification.CrAnSection
/-!

# Creation and annihlation free-algebra

This module defines the creation and annihilation algebra for a field structure.

The creation and annihilation algebra extends from the state algebra by adding information about
whether a state is a creation or annihilation operator.

The algebra is spanned by lists of creation/annihilation states.

The main structures defined in this module are:

* `FieldOpFreeAlgebra` - The creation and annihilation algebra
* `ofCrAnOpF` - Maps a creation/annihilation state to the algebra
* `ofCrAnListF` - Maps a list of creation/annihilation states to the algebra
* `ofFieldOpF` - Maps a state to a sum of creation and annihilation operators
* `crPartF` - The creation part of a state in the algebra
* `anPartF` - The annihilation part of a state in the algebra
* `superCommuteF` - The super commutator on the algebra

The key lemmas show how these operators interact, particularly focusing on the
super commutation relations between creation and annihilation operators.

-/

namespace FieldSpecification
variable {𝓕 : FieldSpecification}

/-- For a field specification `𝓕`, the algebra `𝓕.FieldOpFreeAlgebra` is
  the free algebra generated by creation and annihilation parts of field operators defined in
  `𝓕.CrAnFieldOp`.
  It represents the algebra containing all possible products and linear combinations
  of creation and annihilation parts of field operators, without imposing any conditions.
-/
abbrev FieldOpFreeAlgebra (𝓕 : FieldSpecification) : Type := FreeAlgebra ℂ 𝓕.CrAnFieldOp

namespace FieldOpFreeAlgebra

remark naming_convention := "
  For mathematicial objects defined in relation to `FieldOpFreeAlgebra` we will often postfix
  their names with an `F` to indicate that they are related to the free algebra.
  This is to avoid confusion when working within the context of `FieldOpAlgebra` which is defined
  as a quotient of `FieldOpFreeAlgebra`."

/-- Maps a creation and annihlation state to the creation and annihlation free-algebra. -/
def ofCrAnOpF (φ : 𝓕.CrAnFieldOp) : FieldOpFreeAlgebra 𝓕 :=
  FreeAlgebra.ι ℂ φ

/-- Maps a list creation and annihlation state to the creation and annihlation free-algebra
  by taking their product. -/
def ofCrAnListF (φs : List 𝓕.CrAnFieldOp) : FieldOpFreeAlgebra 𝓕 := (List.map ofCrAnOpF φs).prod

@[simp]
lemma ofCrAnListF_nil : ofCrAnListF ([] : List 𝓕.CrAnFieldOp) = 1 := rfl

lemma ofCrAnListF_cons (φ : 𝓕.CrAnFieldOp) (φs : List 𝓕.CrAnFieldOp) :
    ofCrAnListF (φ :: φs) = ofCrAnOpF φ * ofCrAnListF φs := rfl

lemma ofCrAnListF_append (φs φs' : List 𝓕.CrAnFieldOp) :
    ofCrAnListF (φs ++ φs') = ofCrAnListF φs * ofCrAnListF φs' := by
  simp [ofCrAnListF, List.map_append]

lemma ofCrAnListF_singleton (φ : 𝓕.CrAnFieldOp) :
    ofCrAnListF [φ] = ofCrAnOpF φ := by simp [ofCrAnListF]

/-- Maps a state to the sum of creation and annihilation operators in
  creation and annihilation free-algebra. -/
def ofFieldOpF (φ : 𝓕.FieldOp) : FieldOpFreeAlgebra 𝓕 :=
  ∑ (i : 𝓕.fieldOpToCrAnType φ), ofCrAnOpF ⟨φ, i⟩

/-- Maps a list of states to the creation and annihilation free-algebra by taking
  the product of their sums of creation and annihlation operators.
  Roughly `[φ1, φ2]` gets sent to `(φ1ᶜ+ φ1ᵃ) * (φ2ᶜ+ φ2ᵃ)` etc. -/
def ofFieldOpListF (φs : List 𝓕.FieldOp) : FieldOpFreeAlgebra 𝓕 := (List.map ofFieldOpF φs).prod

/-- Coercion from `List 𝓕.FieldOp` to `FieldOpFreeAlgebra 𝓕` through `ofFieldOpListF`. -/
instance : Coe (List 𝓕.FieldOp) (FieldOpFreeAlgebra 𝓕) := ⟨ofFieldOpListF⟩

@[simp]
lemma ofFieldOpListF_nil : ofFieldOpListF ([] : List 𝓕.FieldOp) = 1 := rfl

lemma ofFieldOpListF_cons (φ : 𝓕.FieldOp) (φs : List 𝓕.FieldOp) :
    ofFieldOpListF (φ :: φs) = ofFieldOpF φ * ofFieldOpListF φs := rfl

lemma ofFieldOpListF_singleton (φ : 𝓕.FieldOp) :
    ofFieldOpListF [φ] = ofFieldOpF φ := by simp [ofFieldOpListF]

lemma ofFieldOpListF_append (φs φs' : List 𝓕.FieldOp) :
    ofFieldOpListF (φs ++ φs') = ofFieldOpListF φs * ofFieldOpListF φs' := by
  dsimp only [ofFieldOpListF]
  rw [List.map_append, List.prod_append]

lemma ofFieldOpListF_sum (φs : List 𝓕.FieldOp) :
    ofFieldOpListF φs = ∑ (s : CrAnSection φs), ofCrAnListF s.1 := by
  induction φs with
  | nil => simp
  | cons φ φs ih =>
    rw [CrAnSection.sum_cons]
    dsimp only [CrAnSection.cons, ofCrAnListF_cons]
    conv_rhs =>
      enter [2, x]
      rw [← Finset.mul_sum]
    rw [← Finset.sum_mul, ofFieldOpListF_cons, ← ih]
    rfl

/-!

## Creation and annihilation parts of a state

-/

/-- The algebra map taking an element of the free-state algbra to
  the part of it in the creation and annihlation free algebra
  spanned by creation operators. -/
def crPartF : 𝓕.FieldOp → 𝓕.FieldOpFreeAlgebra := fun φ =>
  match φ with
  | FieldOp.inAsymp φ => ofCrAnOpF ⟨FieldOp.inAsymp φ, ()⟩
  | FieldOp.position φ => ofCrAnOpF ⟨FieldOp.position φ, CreateAnnihilate.create⟩
  | FieldOp.outAsymp _ => 0

@[simp]
lemma crPartF_negAsymp (φ : 𝓕.Fields × Lorentz.Contr 4) :
    crPartF (FieldOp.inAsymp φ) = ofCrAnOpF ⟨FieldOp.inAsymp φ, ()⟩ := by
  simp [crPartF]

@[simp]
lemma crPartF_position (φ : 𝓕.Fields × SpaceTime) :
    crPartF (FieldOp.position φ) =
    ofCrAnOpF ⟨FieldOp.position φ, CreateAnnihilate.create⟩ := by
  simp [crPartF]

@[simp]
lemma crPartF_posAsymp (φ : 𝓕.Fields × Lorentz.Contr 4) :
    crPartF (FieldOp.outAsymp φ) = 0 := by
  simp [crPartF]

/-- The algebra map taking an element of the free-state algbra to
  the part of it in the creation and annihilation free algebra
  spanned by annihilation operators. -/
def anPartF : 𝓕.FieldOp → 𝓕.FieldOpFreeAlgebra := fun φ =>
  match φ with
  | FieldOp.inAsymp _ => 0
  | FieldOp.position φ => ofCrAnOpF ⟨FieldOp.position φ, CreateAnnihilate.annihilate⟩
  | FieldOp.outAsymp φ => ofCrAnOpF ⟨FieldOp.outAsymp φ, ()⟩

@[simp]
lemma anPartF_negAsymp (φ : 𝓕.Fields × Lorentz.Contr 4) :
    anPartF (FieldOp.inAsymp φ) = 0 := by
  simp [anPartF]

@[simp]
lemma anPartF_position (φ : 𝓕.Fields × SpaceTime) :
    anPartF (FieldOp.position φ) =
    ofCrAnOpF ⟨FieldOp.position φ, CreateAnnihilate.annihilate⟩ := by
  simp [anPartF]

@[simp]
lemma anPartF_posAsymp (φ : 𝓕.Fields × Lorentz.Contr 4) :
    anPartF (FieldOp.outAsymp φ) = ofCrAnOpF ⟨FieldOp.outAsymp φ, ()⟩ := by
  simp [anPartF]

lemma ofFieldOpF_eq_crPartF_add_anPartF (φ : 𝓕.FieldOp) :
    ofFieldOpF φ = crPartF φ + anPartF φ := by
  rw [ofFieldOpF]
  cases φ with
  | inAsymp φ => simp [fieldOpToCrAnType]
  | position φ => simp [fieldOpToCrAnType, CreateAnnihilate.sum_eq]
  | outAsymp φ => simp [fieldOpToCrAnType]

/-!

## The basis of the creation and annihlation free-algebra.

-/

/-- The basis of the free creation and annihilation algebra formed by lists of CrAnFieldOp. -/
noncomputable def ofCrAnListFBasis : Basis (List 𝓕.CrAnFieldOp) ℂ (FieldOpFreeAlgebra 𝓕) where
  repr := FreeAlgebra.equivMonoidAlgebraFreeMonoid.toLinearEquiv

@[simp]
lemma ofListBasis_eq_ofList (φs : List 𝓕.CrAnFieldOp) :
    ofCrAnListFBasis φs = ofCrAnListF φs := by
  simp only [ofCrAnListFBasis, FreeAlgebra.equivMonoidAlgebraFreeMonoid, MonoidAlgebra.of_apply,
    Basis.coe_ofRepr, AlgEquiv.toLinearEquiv_symm, AlgEquiv.toLinearEquiv_apply,
    AlgEquiv.ofAlgHom_symm_apply, ofCrAnListF]
  erw [MonoidAlgebra.lift_apply]
  simp only [zero_smul, Finsupp.sum_single_index, one_smul]
  rw [@FreeMonoid.lift_apply]
  match φs with
  | [] => rfl
  | φ :: φs => erw [List.map_cons]

/-!

## Some useful multi-linear maps.

-/

/-- The bi-linear map associated with multiplication in `FieldOpFreeAlgebra`. -/
noncomputable def mulLinearMap : FieldOpFreeAlgebra 𝓕 →ₗ[ℂ] FieldOpFreeAlgebra 𝓕 →ₗ[ℂ]
    FieldOpFreeAlgebra 𝓕 where
  toFun a := {
    toFun := fun b => a * b,
    map_add' := fun c d => by simp [mul_add]
    map_smul' := by simp}
  map_add' := fun a b => by
    ext c
    simp [add_mul]
  map_smul' := by
    intros
    ext c
    simp [smul_mul']

lemma mulLinearMap_apply (a b : FieldOpFreeAlgebra 𝓕) :
    mulLinearMap a b = a * b := rfl

/-- The linear map associated with scalar-multiplication in `FieldOpFreeAlgebra`. -/
noncomputable def smulLinearMap (c : ℂ) : FieldOpFreeAlgebra 𝓕 →ₗ[ℂ] FieldOpFreeAlgebra 𝓕 where
  toFun a := c • a
  map_add' := by simp
  map_smul' m x := by simp [smul_smul, RingHom.id_apply, NonUnitalNormedCommRing.mul_comm]

end FieldOpFreeAlgebra

end FieldSpecification
