/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.SpaceTime.WeylFermion.Basic
import HepLean.SpaceTime.WeylFermion.Contraction
import Mathlib.LinearAlgebra.TensorProduct.Matrix
import HepLean.SpaceTime.WeylFermion.Two
/-!

# Units of Weyl fermions

We define the units for Weyl fermions, often denoted `δ` in the literature.

-/

namespace Fermion
noncomputable section

open Matrix
open MatrixGroups
open Complex
open TensorProduct
open CategoryTheory.MonoidalCategory

/-- The left-alt-left unit `δᵃₐ` as an element of `(leftHanded ⊗ altLeftHanded).V`. -/
def leftAltLeftUnitVal : (leftHanded ⊗ altLeftHanded).V :=
  leftAltLeftToMatrix.symm 1

/-- Expansion of `leftAltLeftUnitVal` into the basis. -/
lemma leftAltLeftUnitVal_expand_tmul : leftAltLeftUnitVal =
    leftBasis 0 ⊗ₜ[ℂ] altLeftBasis 0 + leftBasis 1 ⊗ₜ[ℂ] altLeftBasis 1 := by
  simp only [Action.instMonoidalCategory_tensorObj_V, leftAltLeftUnitVal, Fin.isValue]
  erw [leftAltLeftToMatrix_symm_expand_tmul]
  simp only [Fin.sum_univ_two, Fin.isValue, one_apply_eq, one_smul, ne_eq, zero_ne_one,
    not_false_eq_true, one_apply_ne, zero_smul, add_zero, one_ne_zero, zero_add]

/-- The left-alt-left unit `δᵃₐ` as a morphism `𝟙_ (Rep ℂ SL(2,ℂ)) ⟶ leftHanded ⊗ altLeftHanded `,
  manifesting the invariance under the `SL(2,ℂ)` action. -/
def leftAltLeftUnit : 𝟙_ (Rep ℂ SL(2,ℂ)) ⟶ leftHanded ⊗ altLeftHanded where
  hom := {
    toFun := fun a =>
      let a' : ℂ := a
      a' • leftAltLeftUnitVal,
    map_add' := fun x y => by
      simp only [add_smul]
    map_smul' := fun m x => by
      simp only [smul_smul]
      rfl}
  comm M := by
    ext x : 2
    simp only [Action.instMonoidalCategory_tensorObj_V, Action.instMonoidalCategory_tensorUnit_V,
      Action.tensorUnit_ρ', CategoryTheory.Category.id_comp, Action.tensor_ρ', ModuleCat.coe_comp,
      Function.comp_apply]
    let x' : ℂ := x
    change x' • leftAltLeftUnitVal =
      (TensorProduct.map (leftHanded.ρ M) (altLeftHanded.ρ M)) (x' • leftAltLeftUnitVal)
    simp only [Action.instMonoidalCategory_tensorObj_V, _root_.map_smul]
    apply congrArg
    simp only [Action.instMonoidalCategory_tensorObj_V, leftAltLeftUnitVal]
    erw [leftAltLeftToMatrix_ρ_symm]
    apply congrArg
    simp

lemma leftAltLeftUnit_apply_one : leftAltLeftUnit.hom (1 : ℂ) = leftAltLeftUnitVal := by
  change leftAltLeftUnit.hom.toFun (1 : ℂ) = leftAltLeftUnitVal
  simp only [Action.instMonoidalCategory_tensorObj_V, Action.instMonoidalCategory_tensorUnit_V,
    leftAltLeftUnit, AddHom.toFun_eq_coe, AddHom.coe_mk, one_smul]

/-- The alt-left-left unit `δₐᵃ` as an element of `(altLeftHanded ⊗ leftHanded).V`. -/
def altLeftLeftUnitVal : (altLeftHanded ⊗ leftHanded).V :=
  altLeftLeftToMatrix.symm 1

/-- Expansion of `altLeftLeftUnitVal` into the basis. -/
lemma altLeftLeftUnitVal_expand_tmul : altLeftLeftUnitVal =
    altLeftBasis 0 ⊗ₜ[ℂ] leftBasis 0 + altLeftBasis 1 ⊗ₜ[ℂ] leftBasis 1 := by
  simp only [Action.instMonoidalCategory_tensorObj_V, altLeftLeftUnitVal, Fin.isValue]
  erw [altLeftLeftToMatrix_symm_expand_tmul]
  simp only [Fin.sum_univ_two, Fin.isValue, one_apply_eq, one_smul, ne_eq, zero_ne_one,
    not_false_eq_true, one_apply_ne, zero_smul, add_zero, one_ne_zero, zero_add]

/-- The alt-left-left unit `δₐᵃ` as a morphism `𝟙_ (Rep ℂ SL(2,ℂ)) ⟶ altLeftHanded ⊗ leftHanded `,
  manifesting the invariance under the `SL(2,ℂ)` action. -/
def altLeftLeftUnit : 𝟙_ (Rep ℂ SL(2,ℂ)) ⟶ altLeftHanded ⊗ leftHanded where
  hom := {
    toFun := fun a =>
      let a' : ℂ := a
      a' • altLeftLeftUnitVal,
    map_add' := fun x y => by
      simp only [add_smul]
    map_smul' := fun m x => by
      simp only [smul_smul]
      rfl}
  comm M := by
    ext x : 2
    simp only [Action.instMonoidalCategory_tensorObj_V, Action.instMonoidalCategory_tensorUnit_V,
      Action.tensorUnit_ρ', CategoryTheory.Category.id_comp, Action.tensor_ρ', ModuleCat.coe_comp,
      Function.comp_apply]
    let x' : ℂ := x
    change x' • altLeftLeftUnitVal =
      (TensorProduct.map (altLeftHanded.ρ M) (leftHanded.ρ M)) (x' • altLeftLeftUnitVal)
    simp only [Action.instMonoidalCategory_tensorObj_V, _root_.map_smul]
    apply congrArg
    simp only [Action.instMonoidalCategory_tensorObj_V, altLeftLeftUnitVal]
    erw [altLeftLeftToMatrix_ρ_symm]
    apply congrArg
    simp only [mul_one, ← transpose_mul, SpecialLinearGroup.det_coe, isUnit_iff_ne_zero, ne_eq,
      one_ne_zero, not_false_eq_true, mul_nonsing_inv, transpose_one]

lemma altLeftLeftUnit_apply_one : altLeftLeftUnit.hom (1 : ℂ) = altLeftLeftUnitVal := by
  change altLeftLeftUnit.hom.toFun (1 : ℂ) = altLeftLeftUnitVal
  simp only [Action.instMonoidalCategory_tensorObj_V, Action.instMonoidalCategory_tensorUnit_V,
    altLeftLeftUnit, AddHom.toFun_eq_coe, AddHom.coe_mk, one_smul]

/-- The right-alt-right unit `δ^{dot a}_{dot a}` as an element of
  `(rightHanded ⊗ altRightHanded).V`. -/
def rightAltRightUnitVal : (rightHanded ⊗ altRightHanded).V :=
  rightAltRightToMatrix.symm 1

/-- Expansion of `rightAltRightUnitVal` into the basis. -/
lemma rightAltRightUnitVal_expand_tmul : rightAltRightUnitVal =
    rightBasis 0 ⊗ₜ[ℂ] altRightBasis 0 + rightBasis 1 ⊗ₜ[ℂ] altRightBasis 1 := by
  simp only [Action.instMonoidalCategory_tensorObj_V, rightAltRightUnitVal, Fin.isValue]
  erw [rightAltRightToMatrix_symm_expand_tmul]
  simp only [Fin.sum_univ_two, Fin.isValue, one_apply_eq, one_smul, ne_eq, zero_ne_one,
    not_false_eq_true, one_apply_ne, zero_smul, add_zero, one_ne_zero, zero_add]

/-- The right-alt-right unit `δ^{dot a}_{dot a}` as a morphism
  `𝟙_ (Rep ℂ SL(2,ℂ)) ⟶ rightHanded ⊗ altRightHanded`, manifesting
  the invariance under the `SL(2,ℂ)` action. -/
def rightAltRightUnit : 𝟙_ (Rep ℂ SL(2,ℂ)) ⟶ rightHanded ⊗ altRightHanded where
  hom := {
    toFun := fun a =>
      let a' : ℂ := a
      a' • rightAltRightUnitVal,
    map_add' := fun x y => by
      simp only [add_smul]
    map_smul' := fun m x => by
      simp only [smul_smul]
      rfl}
  comm M := by
    ext x : 2
    simp only [Action.instMonoidalCategory_tensorObj_V, Action.instMonoidalCategory_tensorUnit_V,
      Action.tensorUnit_ρ', CategoryTheory.Category.id_comp, Action.tensor_ρ', ModuleCat.coe_comp,
      Function.comp_apply]
    let x' : ℂ := x
    change x' • rightAltRightUnitVal =
      (TensorProduct.map (rightHanded.ρ M) (altRightHanded.ρ M)) (x' • rightAltRightUnitVal)
    simp only [Action.instMonoidalCategory_tensorObj_V, _root_.map_smul]
    apply congrArg
    simp only [Action.instMonoidalCategory_tensorObj_V, rightAltRightUnitVal]
    erw [rightAltRightToMatrix_ρ_symm]
    apply congrArg
    simp only [RCLike.star_def, mul_one]
    symm
    refine transpose_eq_one.mp ?h.h.h.a
    simp only [transpose_mul, transpose_transpose]
    change (M.1)⁻¹ᴴ * (M.1)ᴴ = 1
    rw [@conjTranspose_nonsing_inv]
    simp

lemma rightAltRightUnit_apply_one : rightAltRightUnit.hom (1 : ℂ) = rightAltRightUnitVal := by
  change rightAltRightUnit.hom.toFun (1 : ℂ) = rightAltRightUnitVal
  simp only [Action.instMonoidalCategory_tensorObj_V, Action.instMonoidalCategory_tensorUnit_V,
    rightAltRightUnit, AddHom.toFun_eq_coe, AddHom.coe_mk, one_smul]

/-- The alt-right-right unit `δ_{dot a}^{dot a}` as an element of
  `(rightHanded ⊗ altRightHanded).V`. -/
def altRightRightUnitVal : (altRightHanded ⊗ rightHanded).V :=
  altRightRightToMatrix.symm 1

/-- Expansion of `altRightRightUnitVal` into the basis. -/
lemma altRightRightUnitVal_expand_tmul : altRightRightUnitVal =
    altRightBasis 0 ⊗ₜ[ℂ] rightBasis 0 + altRightBasis 1 ⊗ₜ[ℂ] rightBasis 1 := by
  simp only [Action.instMonoidalCategory_tensorObj_V, altRightRightUnitVal, Fin.isValue]
  erw [altRightRightToMatrix_symm_expand_tmul]
  simp only [Fin.sum_univ_two, Fin.isValue, one_apply_eq, one_smul, ne_eq, zero_ne_one,
    not_false_eq_true, one_apply_ne, zero_smul, add_zero, one_ne_zero, zero_add]

/-- The alt-right-right unit `δ_{dot a}^{dot a}` as a morphism
  `𝟙_ (Rep ℂ SL(2,ℂ)) ⟶ altRightHanded ⊗ rightHanded`, manifesting
  the invariance under the `SL(2,ℂ)` action. -/
def altRightRightUnit : 𝟙_ (Rep ℂ SL(2,ℂ)) ⟶ altRightHanded ⊗ rightHanded where
  hom := {
    toFun := fun a =>
      let a' : ℂ := a
      a' • altRightRightUnitVal,
    map_add' := fun x y => by
      simp only [add_smul]
    map_smul' := fun m x => by
      simp only [smul_smul]
      rfl}
  comm M := by
    ext x : 2
    simp only [Action.instMonoidalCategory_tensorObj_V, Action.instMonoidalCategory_tensorUnit_V,
      Action.tensorUnit_ρ', CategoryTheory.Category.id_comp, Action.tensor_ρ', ModuleCat.coe_comp,
      Function.comp_apply]
    let x' : ℂ := x
    change x' • altRightRightUnitVal =
      (TensorProduct.map (altRightHanded.ρ M) (rightHanded.ρ M)) (x' • altRightRightUnitVal)
    simp only [Action.instMonoidalCategory_tensorObj_V, _root_.map_smul]
    apply congrArg
    simp only [Action.instMonoidalCategory_tensorObj_V, altRightRightUnitVal]
    erw [altRightRightToMatrix_ρ_symm]
    apply congrArg
    simp only [mul_one, RCLike.star_def]
    symm
    change (M.1)⁻¹ᴴ * (M.1)ᴴ = 1
    rw [@conjTranspose_nonsing_inv]
    simp

lemma altRightRightUnit_apply_one : altRightRightUnit.hom (1 : ℂ) = altRightRightUnitVal := by
  change altRightRightUnit.hom.toFun (1 : ℂ) = altRightRightUnitVal
  simp only [Action.instMonoidalCategory_tensorObj_V, Action.instMonoidalCategory_tensorUnit_V,
    altRightRightUnit, AddHom.toFun_eq_coe, AddHom.coe_mk, one_smul]

/-!

## Contraction of the units

-/

lemma contr_leftAltLeftUnitVal (x : leftHanded) :
    (λ_ leftHanded).hom.hom
    (((leftAltContraction) ▷ leftHanded).hom
    ((α_ _ _ leftHanded).inv.hom
    (x ⊗ₜ[ℂ] altLeftLeftUnit.hom (1 : ℂ)))) = x := by
  sorry
end
end Fermion
