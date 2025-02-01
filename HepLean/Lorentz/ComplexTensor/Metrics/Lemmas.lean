/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.Lorentz.ComplexTensor.Metrics.Basis
import HepLean.Lorentz.ComplexTensor.Units.Basic
/-!

## Basic lemmas regarding metrics

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

namespace complexLorentzTensor

/-!

## Symmetry properties

-/

/-- The covariant metric is symmetric `{η' | μ ν = η' | ν μ}ᵀ`. -/
informal_lemma coMetric_symm where
  deps := [``coMetric]

/-- The contravariant metric is symmetric `{η | μ ν = η | ν μ}ᵀ`. -/
informal_lemma contrMetric_symm where
  deps := [``contrMetric]

/-- The left metric is antisymmetric `{εL | α α' = - εL | α' α}ᵀ`. -/
informal_lemma leftMetric_antisymm where
  deps := [``leftMetric]

/-- The right metric is antisymmetric `{εR | β β' = - εR | β' β}ᵀ`. -/
informal_lemma rightMetric_antisymm where
  deps := [``rightMetric]

/-- The alt-left metric is antisymmetric `{εL' | α α' = - εL' | α' α}ᵀ`. -/
informal_lemma altLeftMetric_antisymm where
  deps := [``altLeftMetric]

/-- The alt-right metric is antisymmetric `{εR' | β β' = - εR' | β' β}ᵀ`. -/
informal_lemma altRightMetric_antisymm where
  deps := [``altRightMetric]

/-!

## Contractions with each other

-/

/-- The contraction of the covariant metric with the contravariant metric is the unit
`{η' | μ ρ ⊗ η | ρ ν = δ' | μ ν}ᵀ`.
-/
informal_lemma coMetric_contr_contrMetric where
  deps := [``coMetric, ``contrMetric, ``coContrUnit]

/-- The contraction of the contravariant metric with the covariant metric is the unit
`{η | μ ρ ⊗ η' | ρ ν = δ | μ ν}ᵀ`.
-/
informal_lemma contrMetric_contr_coMetric where
  deps := [``contrMetric, ``coMetric, ``contrCoUnit]

/-- The contraction of the left metric with the alt-left metric is the unit
`{εL | α β ⊗ εL' | β γ = δL | α γ}ᵀ`.
-/
informal_lemma leftMetric_contr_altLeftMetric where
  deps := [``leftMetric, ``altLeftMetric, ``leftAltLeftUnit]

/-- The contraction of the right metric with the alt-right metric is the unit
`{εR | α β ⊗ εR' | β γ = δR | α γ}ᵀ`.
-/
informal_lemma rightMetric_contr_altRightMetric where
  deps := [``rightMetric, ``altRightMetric, ``rightAltRightUnit]

/-- The contraction of the alt-left metric with the left metric is the unit
`{εL' | α β ⊗ εL | β γ = δL' | α γ}ᵀ`.
-/
informal_lemma altLeftMetric_contr_leftMetric where
  deps := [``altLeftMetric, ``leftMetric, ``altLeftLeftUnit]

/-- The contraction of the alt-right metric with the right metric is the unit
`{εR' | α β ⊗ εR | β γ = δR' | α γ}ᵀ`.
-/
informal_lemma altRightMetric_contr_rightMetric where
  deps := [``altRightMetric, ``rightMetric, ``altRightRightUnit]

/-!

## Other relations

-/
/-- The map to color one gets when multiplying left and right metrics. -/
def leftMetricMulRightMap := (Sum.elim ![Color.upL, Color.upL] ![Color.upR, Color.upR]) ∘
  finSumFinEquiv.symm

/-- Expansion of the product of `εL` and `εR` in terms of a basis. -/
lemma leftMetric_prod_rightMetric : {εL | α α' ⊗ εR | β β'}ᵀ.tensor
    = basisVector leftMetricMulRightMap (fun | 0 => 0 | 1 => 1 | 2 => 0 | 3 => 1)
    - basisVector leftMetricMulRightMap (fun | 0 => 0 | 1 => 1 | 2 => 1 | 3 => 0)
    - basisVector leftMetricMulRightMap (fun | 0 => 1 | 1 => 0 | 2 => 0 | 3 => 1)
    + basisVector leftMetricMulRightMap (fun | 0 => 1 | 1 => 0 | 2 => 1 | 3 => 0) := by
  rw [prod_tensor_eq_fst (leftMetric_expand_tree)]
  rw [prod_tensor_eq_snd (rightMetric_expand_tree)]
  rw [prod_add_both]
  rw [add_tensor_eq_fst <| add_tensor_eq_fst <| smul_prod _ _ _]
  rw [add_tensor_eq_fst <| add_tensor_eq_fst <| smul_tensor_eq <| prod_smul _ _ _]
  rw [add_tensor_eq_fst <| add_tensor_eq_fst <| smul_smul _ _ _]
  rw [add_tensor_eq_fst <| add_tensor_eq_fst <| smul_eq_one _ _ (by simp)]
  rw [add_tensor_eq_fst <| add_tensor_eq_snd <| smul_prod _ _ _]
  rw [add_tensor_eq_snd <| add_tensor_eq_fst <| prod_smul _ _ _]
  rw [add_tensor_eq_fst <| add_tensor_eq_fst <| prod_basisVector_tree _ _]
  rw [add_tensor_eq_fst <| add_tensor_eq_snd <| smul_tensor_eq <| prod_basisVector_tree _ _]
  rw [add_tensor_eq_snd <| add_tensor_eq_fst <| smul_tensor_eq <| prod_basisVector_tree _ _]
  rw [add_tensor_eq_snd <| add_tensor_eq_snd <| prod_basisVector_tree _ _]
  rw [← add_assoc]
  simp only [add_tensor, smul_tensor, tensorNode_tensor]
  change _ = basisVector leftMetricMulRightMap (fun | 0 => 0 | 1 => 1 | 2 => 0 | 3 => 1)
    +- basisVector leftMetricMulRightMap (fun | 0 => 0 | 1 => 1 | 2 => 1 | 3 => 0)
    +- basisVector leftMetricMulRightMap (fun | 0 => 1 | 1 => 0 | 2 => 0 | 3 => 1)
    + basisVector leftMetricMulRightMap (fun | 0 => 1 | 1 => 0 | 2 => 1 | 3 => 0)
  congr 1
  congr 1
  congr 1
  all_goals
    congr
    funext x
    fin_cases x <;> rfl

/-- Expansion of the product of `εL` and `εR` in terms of a basis, as a tensor tree. -/
lemma leftMetric_prod_rightMetric_tree : {εL | α α' ⊗ εR | β β'}ᵀ.tensor
    = (TensorTree.add (tensorNode
        (basisVector leftMetricMulRightMap (fun | 0 => 0 | 1 => 1 | 2 => 0 | 3 => 1))) <|
      TensorTree.add (TensorTree.smul (-1 : ℂ) (tensorNode
        (basisVector leftMetricMulRightMap (fun | 0 => 0 | 1 => 1 | 2 => 1 | 3 => 0)))) <|
      TensorTree.add (TensorTree.smul (-1 : ℂ) (tensorNode
        (basisVector leftMetricMulRightMap (fun | 0 => 1 | 1 => 0 | 2 => 0 | 3 => 1)))) <|
      (tensorNode
        (basisVector leftMetricMulRightMap (fun | 0 => 1 | 1 => 0 | 2 => 1 | 3 => 0)))).tensor := by
  rw [leftMetric_prod_rightMetric]
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, add_tensor, tensorNode_tensor,
    smul_tensor, neg_smul, one_smul]
  rfl

end complexLorentzTensor
