/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.SpaceTime.LorentzVector.Complex.Two
import HepLean.SpaceTime.MinkowskiMetric
/-!

# Metric for complex Lorentz vectors

-/
noncomputable section

open Matrix
open MatrixGroups
open Complex
open TensorProduct
open SpaceTime
open CategoryTheory.MonoidalCategory
namespace Lorentz

/-- The metric `ηᵃᵃ` as an element of `(complexContr ⊗ complexContr).V`. -/
def contrMetricVal : (complexContr ⊗ complexContr).V :=
  contrContrToMatrix.symm ((@minkowskiMatrix 3).map ofReal)

/-- The metric `ηᵃᵃ` as a morphism `𝟙_ (Rep ℂ SL(2,ℂ)) ⟶ complexContr ⊗ complexContr`,
  making its invariance under the action of `SL(2,ℂ)`. -/
def contrMetric : 𝟙_ (Rep ℂ SL(2,ℂ)) ⟶ complexContr ⊗ complexContr where
  hom := {
    toFun := fun a =>
      let a' : ℂ := a
      a' • contrMetricVal,
    map_add' := fun x y => by
      simp only [add_smul],
    map_smul' := fun m x => by
      simp only [smul_smul]
      rfl}
  comm M := by
    ext x : 2
    simp only [Action.instMonoidalCategory_tensorObj_V, Action.instMonoidalCategory_tensorUnit_V,
      Action.tensorUnit_ρ', CategoryTheory.Category.id_comp, Action.tensor_ρ', ModuleCat.coe_comp,
      Function.comp_apply]
    let x' : ℂ := x
    change x' • contrMetricVal =
      (TensorProduct.map (complexContr.ρ M) (complexContr.ρ M)) (x' • contrMetricVal)
    simp only [Action.instMonoidalCategory_tensorObj_V, _root_.map_smul]
    apply congrArg
    simp only [Action.instMonoidalCategory_tensorObj_V, contrMetricVal]
    erw [contrContrToMatrix_ρ_symm]
    apply congrArg
    simp only [LorentzGroup.toComplex_mul_minkowskiMatrix_mul_transpose]

/-- The metric `ηᵢᵢ` as an element of `(complexCo ⊗ complexCo).V`. -/
def coMetricVal : (complexCo ⊗ complexCo).V :=
  coCoToMatrix.symm ((@minkowskiMatrix 3).map ofReal)

/-- The metric `ηᵢᵢ` as a morphism `𝟙_ (Rep ℂ SL(2,ℂ)) ⟶ complexCo ⊗ complexCo`,
  making its invariance under the action of `SL(2,ℂ)`. -/
def coMetric : 𝟙_ (Rep ℂ SL(2,ℂ)) ⟶ complexCo ⊗ complexCo where
  hom := {
    toFun := fun a =>
      let a' : ℂ := a
      a' • coMetricVal,
    map_add' := fun x y => by
      simp only [add_smul],
    map_smul' := fun m x => by
      simp only [smul_smul]
      rfl}
  comm M := by
    ext x : 2
    simp only [Action.instMonoidalCategory_tensorObj_V, Action.instMonoidalCategory_tensorUnit_V,
      Action.tensorUnit_ρ', CategoryTheory.Category.id_comp, Action.tensor_ρ', ModuleCat.coe_comp,
      Function.comp_apply]
    let x' : ℂ := x
    change x' • coMetricVal =
      (TensorProduct.map (complexCo.ρ M) (complexCo.ρ M)) (x' • coMetricVal)
    simp only [Action.instMonoidalCategory_tensorObj_V, _root_.map_smul]
    apply congrArg
    simp only [Action.instMonoidalCategory_tensorObj_V, coMetricVal]
    erw [coCoToMatrix_ρ_symm]
    apply congrArg
    rw [LorentzGroup.toComplex_inv]
    simp only [lorentzGroupIsGroup_inv, SL2C.toLorentzGroup_apply_coe,
      LorentzGroup.toComplex_transpose_mul_minkowskiMatrix_mul_self]

end Lorentz
end
