/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.SpaceTime.LorentzTensor.Basic
/-!

# Rising and Lowering of indices

We use the term `dualize` to describe the more general version of rising and lowering of indices.

In particular, rising and lowering indices corresponds taking the color of that index
to its dual.

-/

noncomputable section

open TensorProduct

variable {R : Type} [CommSemiring R]

namespace TensorStructure

variable (𝓣 : TensorStructure R)

variable {d : ℕ} {X Y Y' Z W C P : Type} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
  [Fintype Y'] [DecidableEq Y'] [Fintype Z] [DecidableEq Z] [Fintype W] [DecidableEq W]
  [Fintype C] [DecidableEq C] [Fintype P] [DecidableEq P]
  {cX cX2 : X → 𝓣.Color} {cY : Y → 𝓣.Color} {cZ : Z → 𝓣.Color}
  {cW : W → 𝓣.Color} {cY' : Y' → 𝓣.Color} {μ ν: 𝓣.Color}

/-!

## Properties of the unit

-/

/-! TODO: Move -/

lemma unit_lhs_eq (x : 𝓣.ColorModule μ) (y : 𝓣.ColorModule (𝓣.τ μ) ⊗[R] 𝓣.ColorModule μ) :
    contrLeftAux (𝓣.contrDual μ) (x ⊗ₜ[R] y) =
    (contrRightAux (𝓣.contrDual (𝓣.τ μ))) ((TensorProduct.comm R _ _) y
    ⊗ₜ[R] (𝓣.colorModuleCast (𝓣.τ_involutive μ).symm) x) := by
  refine TensorProduct.induction_on y (by simp) ?_ (fun z1 z2 h1 h2 => ?_)
  intro x1 x2
  simp only [contrRightAux, LinearEquiv.refl_toLinearMap, comm_tmul, colorModuleCast,
    Equiv.cast_symm, LinearEquiv.coe_mk, Equiv.cast_apply, LinearMap.coe_comp, LinearEquiv.coe_coe,
    Function.comp_apply, assoc_tmul, map_tmul, LinearMap.id_coe, id_eq, contrDual_symm', cast_cast,
    cast_eq, rid_tmul]
  rfl
  simp [LinearMap.map_add, add_tmul]
  rw [← h1, ← h2, tmul_add, LinearMap.map_add]

@[simp]
lemma unit_lid : (contrRightAux (𝓣.contrDual (𝓣.τ μ))) ((TensorProduct.comm R _ _) (𝓣.unit μ)
    ⊗ₜ[R] (𝓣.colorModuleCast (𝓣.τ_involutive μ).symm) x) = x := by
  have h1 := 𝓣.unit_rid μ x
  rw [← unit_lhs_eq]
  exact h1

/-!

## Properties of the metric

-/

@[simp]
lemma metric_cast (h : μ = ν) :
    (TensorProduct.congr (𝓣.colorModuleCast h) (𝓣.colorModuleCast h)) (𝓣.metric μ) =
    𝓣.metric ν := by
  subst h
  erw [congr_refl_refl]
  simp only [LinearEquiv.refl_apply]

@[simp]
lemma metric_contrRight_unit (μ : 𝓣.Color) (x : 𝓣.ColorModule μ) :
    (contrRightAux (𝓣.contrDual μ)) (𝓣.metric μ ⊗ₜ[R]
    ((contrRightAux (𝓣.contrDual (𝓣.τ μ)))
      (𝓣.metric (𝓣.τ μ) ⊗ₜ[R] (𝓣.colorModuleCast (𝓣.τ_involutive μ).symm x)))) = x := by
  change (contrRightAux (𝓣.contrDual μ) ∘ₗ TensorProduct.map (LinearMap.id)
      (contrRightAux (𝓣.contrDual (𝓣.τ μ)))) (𝓣.metric μ
      ⊗ₜ[R] 𝓣.metric (𝓣.τ μ) ⊗ₜ[R] (𝓣.colorModuleCast (𝓣.τ_involutive μ).symm x)) = _
  rw [contrRightAux_comp]
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply, assoc_symm_tmul,
    map_tmul, LinearMap.id_coe, id_eq]
  rw [𝓣.metric_dual]
  simp only [unit_lid]

/-!

## Dualizing

-/

/-- Takes a vector with index with dual color to a vector with index the underlying color.
  Obtained by contraction with the metric. -/
def dualizeSymm (μ : 𝓣.Color) : 𝓣.ColorModule (𝓣.τ μ) →ₗ[R] 𝓣.ColorModule μ :=
  contrRightAux (𝓣.contrDual μ) ∘ₗ
    TensorProduct.lTensorHomToHomLTensor R _ _ _ (𝓣.metric μ ⊗ₜ[R] LinearMap.id)

/-- Takes a vector to a vector with the dual color index.
  Obtained by contraction with the metric. -/
def dualizeFun (μ : 𝓣.Color) : 𝓣.ColorModule μ →ₗ[R] 𝓣.ColorModule (𝓣.τ μ) :=
  𝓣.dualizeSymm (𝓣.τ μ) ∘ₗ (𝓣.colorModuleCast (𝓣.τ_involutive μ).symm).toLinearMap

/-- Equivalence between the module with a color `μ` and the module with color
  `𝓣.τ μ` obtained by contraction with the metric. -/
def dualizeModule (μ : 𝓣.Color) : 𝓣.ColorModule μ ≃ₗ[R] 𝓣.ColorModule (𝓣.τ μ) := by
  refine LinearEquiv.ofLinear (𝓣.dualizeFun μ) (𝓣.dualizeSymm μ) ?_ ?_
  · apply LinearMap.ext
    intro x
    simp [dualizeFun, dualizeSymm, LinearMap.coe_comp, LinearEquiv.coe_coe,
      Function.comp_apply, lTensorHomToHomLTensor_apply, LinearMap.id_coe, id_eq,
      contrDual_symm_contrRightAux_apply_tmul, metric_cast]
  · apply LinearMap.ext
    intro x
    simp only [dualizeSymm, dualizeFun, LinearMap.coe_comp, LinearEquiv.coe_coe,
      Function.comp_apply, lTensorHomToHomLTensor_apply, LinearMap.id_coe, id_eq,
      metric_contrRight_unit]

/-- Dualizes the color of all indicies of a tensor by contraction with the metric. -/
def dualizeAll : 𝓣.Tensor cX ≃ₗ[R] 𝓣.Tensor (𝓣.τ ∘ cX) := by
  refine LinearEquiv.ofLinear
    (PiTensorProduct.map (fun x => (𝓣.dualizeModule (cX x)).toLinearMap))
    (PiTensorProduct.map (fun x => (𝓣.dualizeModule (cX x)).symm.toLinearMap)) ?_ ?_
  all_goals
    apply LinearMap.ext
    refine fun x ↦ PiTensorProduct.induction_on' x ?_ (by
      intro a b hx a
      simp [map_add, add_tmul, hx]
      simp_all only [Function.comp_apply, LinearMap.coe_comp, LinearMap.id_coe, id_eq])
    intro rx fx
    simp only [Function.comp_apply, PiTensorProduct.tprodCoeff_eq_smul_tprod,
      LinearMapClass.map_smul, LinearMap.coe_comp, LinearMap.id_coe, id_eq]
    apply congrArg
    change (PiTensorProduct.map _)
      ((PiTensorProduct.map _) ((PiTensorProduct.tprod R) fx)) = _
    rw [PiTensorProduct.map_tprod, PiTensorProduct.map_tprod]
    apply congrArg
    simp

lemma dualize_cond (e : C ⊕ P ≃ X) :
    cX = Sum.elim (cX ∘ e ∘ Sum.inl) (cX ∘ e ∘ Sum.inr) ∘ e.symm := by
  rw [Equiv.eq_comp_symm]
  funext x
  match x with
  | Sum.inl x => rfl
  | Sum.inr x => rfl

lemma dualize_cond' (e : C ⊕ P ≃ X) :
    Sum.elim (𝓣.τ ∘ cX ∘ ⇑e ∘ Sum.inl) (cX ∘ ⇑e ∘ Sum.inr) =
    (Sum.elim (𝓣.τ ∘ cX ∘ ⇑e ∘ Sum.inl) (cX ∘ ⇑e ∘ Sum.inr) ∘ ⇑e.symm) ∘ ⇑e := by
  funext x
  match x with
  | Sum.inl x => simp
  | Sum.inr x => simp

/-! TODO: Show that `dualize` is equivariant with respect to the group action. -/

/-- Given an equivalence `C ⊕ P ≃ X` dualizes those indices of a tensor which correspond to
  `C` whilst leaving the indices `P` invariant. -/
def dualize (e : C ⊕ P ≃ X) : 𝓣.Tensor cX ≃ₗ[R]
    𝓣.Tensor (Sum.elim (𝓣.τ ∘ cX ∘ e ∘ Sum.inl) (cX ∘ e ∘ Sum.inr) ∘ e.symm) :=
  𝓣.mapIso e.symm (𝓣.dualize_cond e) ≪≫ₗ
  (𝓣.tensoratorEquiv _ _).symm ≪≫ₗ
  TensorProduct.congr 𝓣.dualizeAll (LinearEquiv.refl _ _) ≪≫ₗ
  (𝓣.tensoratorEquiv _ _) ≪≫ₗ
  𝓣.mapIso e (𝓣.dualize_cond' e)

end TensorStructure

end
