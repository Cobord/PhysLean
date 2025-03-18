/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Joseph Tooby-Smith
-/
import PhysLean.Relativity.Lorentz.RealTensor.Metrics.Basic
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
/-!

## Metrics as real Lorentz tensors

-/
open IndexNotation
open CategoryTheory
open MonoidalCategory
open Matrix
open MatrixGroups
open Complex
open TensorProduct
open IndexNotation
open CategoryTheory
open TensorTree
open OverColor.Discrete
noncomputable section

namespace Lorentz
open realLorentzTensor

/-- Real contravariant Lorentz vector. -/
abbrev Vector (d : ℕ := 3) := ℝT[d, .up]

namespace Vector

/-- The equivalence between the type of indices of a Lorentz vector and
  `Fin 1 ⊕ Fin d`. -/
def indexEquiv {d : ℕ} :
    ((j : Fin (Nat.succ 0)) → Fin ((realLorentzTensor d).repDim (![Color.up] j)))
    ≃ Fin 1 ⊕ Fin d :=
  let e :((j : Fin (Nat.succ 0)) → Fin ((realLorentzTensor d).repDim (![Color.up] j)))
    ≃ Fin (1 + d) := {
    toFun := fun f => Fin.cast (by rfl) (f 0)
    invFun := fun x => (fun j => Fin.cast (by simp) x)
    left_inv := fun f => by
      ext j
      fin_cases j
      simp
    right_inv := fun x => by rfl}
  e.trans finSumFinEquiv.symm

/-- The coordinates of a Lorentz vector -/
def toCoord {d : ℕ} (p : Vector d) : Fin 1 ⊕ Fin d → ℝ :=
  Equiv.piCongrLeft' _ indexEquiv
  (Finsupp.equivFunOnFinite
  (((realLorentzTensor d).tensorBasis _).repr p))

lemma toCoord_injective {d : ℕ} : Function.Injective (@toCoord d) := by
  intros x y h
  simp [toCoord] at h
  erw [Equiv.apply_eq_iff_eq] at h
  simpa using h

/-- The coordinates of a Lorentz vector as a linear map. -/
def toCoordLinear {d : ℕ} : Vector d →ₗ[ℝ] (Fin 1 ⊕ Fin d → ℝ) where
  toFun := toCoord
  map_add' x y := by
    simp only [toCoord, Nat.succ_eq_add_one, Nat.reduceAdd, C_eq_color, map_add]
    rfl
  map_smul' x y := by
    simp only [toCoord, Nat.succ_eq_add_one, Nat.reduceAdd, C_eq_color, _root_.map_smul,
      RingHom.id_apply]
    rfl

@[simp]
lemma toCoordLinear_apply {d : ℕ} (p : Vector d) :
    toCoordLinear p = toCoord p := by rfl

lemma toCoordLinear_injective (d : ℕ) : Function.Injective (@toCoordLinear d) := by
  intros x y h
  simp at h
  exact toCoord_injective h

instance : CoeFun (Vector d) (fun _ => Fin 1 ⊕ Fin d → ℝ) := ⟨toCoord⟩

lemma tensorNode_repr_apply {d : ℕ} (p : Vector d)
    (b : (j : Fin (Nat.succ 0)) → Fin ((realLorentzTensor d).repDim (![Color.up] j))) :
    ((realLorentzTensor d).tensorBasis _).repr p b =
    p (finSumFinEquiv.symm (b 0)) := by
  simp [toCoord, indexEquiv]
  congr
  ext j
  fin_cases j
  simp

/-- The Minkowski product of Lorentz vectors in the +--- convention.. -/
def innerProduct {d : ℕ} (p q : Vector d) : ℝ :=
  {η' d | μ ν ⊗ p | μ ⊗ q | ν}ᵀ.field

@[inherit_doc innerProduct]
notation "⟪" p ", " q "⟫ₘ" => innerProduct p q

open TensorTree
lemma innerProduct_toCoord {d : ℕ} (p q : Vector d) :
    ⟪p, q⟫ₘ = p (Sum.inl 0) * q (Sum.inl 0) - ∑ i, p (Sum.inr i) * q (Sum.inr i) := by
  dsimp only [innerProduct, Nat.succ_eq_add_one, Nat.reduceAdd, C_eq_color, Fin.isValue]
  rw [TensorTree.field_eq_repr]
  rw [contr_tensorBasis_repr_apply_eq_fin]
  conv_lhs =>
    enter [2, x]
    rw [prod_tensorBasis_repr_apply]
    rw [contr_tensorBasis_repr_apply_eq_fin]
    rw [tensorNode_repr_apply]
    enter [1, 2, y]
    rw [prod_tensorBasis_repr_apply]
    rw [tensorNode_repr_apply]
    enter [1]
    erw [coMetric_repr_apply_eq_minkowskiMatrix]
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, C_eq_color, Fin.isValue, Fin.succAbove_zero,
    Function.comp_apply, Fin.zero_succAbove, Fin.succ_zero_eq_one, Fin.cast_eq_self,
    Fin.succ_one_eq_two, tensorNode_tensor]
  conv_lhs =>
    enter [2, x, 2, 2]
    simp only [Fin.isValue]
    change finSumFinEquiv.symm x
  conv_lhs =>
    enter [2, x, 1, 2, y, 2, 2]
    change finSumFinEquiv.symm y
  conv_lhs =>
    enter [2, x, 1, 2, y, 1]
    simp only [Fin.isValue]
    change minkowskiMatrix (finSumFinEquiv.symm y) (finSumFinEquiv.symm x)
  conv_lhs =>
    enter [2, x, 1]
    rw [← finSumFinEquiv.sum_comp]
  rw [← finSumFinEquiv.sum_comp]
  simp only [Equiv.symm_apply_apply, Fintype.sum_sum_type, Finset.univ_unique, Fin.default_eq_zero,
    Fin.isValue, Finset.sum_singleton, ne_eq, reduceCtorEq, not_false_eq_true,
    minkowskiMatrix.off_diag_zero, zero_mul, Finset.sum_const_zero, _root_.add_zero,
    _root_.zero_add]
  congr 1
  rw [minkowskiMatrix.inl_0_inl_0]
  simp only [Fin.isValue, one_mul]
  rw [← Finset.sum_neg_distrib]
  congr
  funext x
  rw [Finset.sum_eq_single x]
  · rw [minkowskiMatrix.inr_i_inr_i]
    simp
  · intro y _ hy
    rw [minkowskiMatrix.off_diag_zero (by simp [hy])]
    simp
  · simp

@[simp]
lemma innerProduct_zero_left {d : ℕ} (q : Vector d) :
    ⟪0, q⟫ₘ = 0 := by
  rw [innerProduct_toCoord]
  simp [toCoord]

@[simp]
lemma innerProduct_zero_right {d : ℕ} (p : Vector d) :
    ⟪p, 0⟫ₘ = 0 := by
  rw [innerProduct_toCoord]
  simp [toCoord]

@[simp]
lemma innerProduct_invariant {d : ℕ} (p q : Vector d) (Λ : LorentzGroup d) :
    ⟪((realLorentzTensor d).F.obj _).ρ Λ p, ((realLorentzTensor d).F.obj _).ρ Λ q⟫ₘ = ⟪p, q⟫ₘ := by
  rw [innerProduct]
  have h1 (q : Vector d) :
    (tensorNode ((((realLorentzTensor d).F.obj (OverColor.mk ![Color.up])).ρ Λ) q)).tensor
    = (action Λ (tensorNode q)).tensor := by simp [action_tensor]
  rw [field]
  rw [contr_tensor_eq <| prod_tensor_eq_snd <| h1 q]
  rw [contr_tensor_eq <| prod_tensor_eq_fst
    <| contr_tensor_eq <| prod_tensor_eq_snd <| h1 p]
  have h2 : (tensorNode (realLorentzTensor.coMetric d)).tensor
      = (action Λ (tensorNode (realLorentzTensor.coMetric d))).tensor := by
    rw [action_coMetric]
  rw [contr_tensor_eq <| prod_tensor_eq_fst
    <| contr_tensor_eq <| prod_tensor_eq_fst <| h2]
  rw [contr_tensor_eq <| prod_tensor_eq_fst <| contr_tensor_eq <|
    prod_action _ _ _]
  rw [contr_tensor_eq <| prod_tensor_eq_fst <| contr_action _ _]
  rw [contr_tensor_eq <| prod_action _ _ _]
  rw [contr_action _]
  rw [← field]
  simp
  rw [innerProduct]

/-!

## Smoothness

-/

section smoothness

instance isNormedAddCommGroup (d : ℕ) : NormedAddCommGroup (Vector d) :=
  NormedAddCommGroup.induced ↑(Vector d).V (Fin 1 ⊕ Fin d → ℝ)
  (@toCoordLinear d) (toCoordLinear_injective d)

instance isNormedSpace (d : ℕ) :
    haveI := isNormedAddCommGroup d
    NormedSpace ℝ (Vector d) :=
  NormedSpace.induced ℝ (Vector d) (Fin 1 ⊕ Fin d → ℝ) (@toCoordLinear d)

open Manifold
open Matrix
open Complex
open ComplexConjugate

/-- The structure of a smooth manifold on Vector . -/
def asSmoothManifold (d : ℕ) : ModelWithCorners ℝ (Vector d) (Vector d) := 𝓘(ℝ, Vector d)

/-- The instance of a `ChartedSpace` on `Vector d`. -/
instance : ChartedSpace (Vector d) (Vector d) := chartedSpaceSelf (Vector d)

end smoothness

end Vector

end Lorentz
