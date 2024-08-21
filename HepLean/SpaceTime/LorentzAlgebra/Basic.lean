/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.SpaceTime.MinkowskiMetric
import Mathlib.Algebra.Lie.Classical
/-!
# The Lorentz Algebra

We define

- Define `lorentzAlgebra` via `LieAlgebra.Orthogonal.so'` as a subalgebra of
  `Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℝ`.
- In `mem_iff` prove that a matrix is in the Lorentz algebra if and only if it satisfies the
  condition `Aᵀ * η = - η * A`.

-/

namespace SpaceTime
open Matrix
open TensorProduct

/-- The Lorentz algebra as a subalgebra of `Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℝ`. -/
def lorentzAlgebra : LieSubalgebra ℝ (Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℝ) :=
  (LieAlgebra.Orthogonal.so' (Fin 1) (Fin 3) ℝ)

namespace lorentzAlgebra
open minkowskiMatrix

lemma transpose_eta (A : lorentzAlgebra) : A.1ᵀ * η = - η * A.1 := by
  have h1 := A.2
  erw [mem_skewAdjointMatricesLieSubalgebra] at h1
  simpa [LieAlgebra.Orthogonal.so', IsSkewAdjoint, IsAdjointPair] using h1

lemma mem_of_transpose_eta_eq_eta_mul_self {A : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℝ}
    (h : Aᵀ * η = - η * A) : A ∈ lorentzAlgebra := by
  erw [mem_skewAdjointMatricesLieSubalgebra]
  simpa [LieAlgebra.Orthogonal.so', IsSkewAdjoint, IsAdjointPair] using h

lemma mem_iff {A : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℝ} :
    A ∈ lorentzAlgebra ↔ Aᵀ * η = - η * A :=
  Iff.intro (fun h => transpose_eta ⟨A, h⟩) (fun h => mem_of_transpose_eta_eq_eta_mul_self h)

lemma mem_iff' (A : Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℝ) :
    A ∈ lorentzAlgebra ↔ A = - η * Aᵀ * η := by
  rw [mem_iff]
  refine Iff.intro (fun h => ?_) (fun h => ?_)
  · trans -η * (Aᵀ * η)
    · rw [h]
      trans (η * η) * A
      · rw [minkowskiMatrix.sq]
        noncomm_ring
      · noncomm_ring
    · noncomm_ring
  · nth_rewrite 2 [h]
    trans (η * η) * Aᵀ * η
    · rw [minkowskiMatrix.sq]
      noncomm_ring
    · noncomm_ring

lemma diag_comp (Λ : lorentzAlgebra) (μ : Fin 1 ⊕ Fin 3) : Λ.1 μ μ = 0 := by
  have h := congrArg (fun M ↦ M μ μ) $ mem_iff.mp Λ.2
  simp only [minkowskiMatrix, LieAlgebra.Orthogonal.indefiniteDiagonal, mul_diagonal,
    transpose_apply, diagonal_neg, diagonal_mul, neg_mul] at h
  rcases μ with μ | μ <;>
    simpa using h

lemma time_comps (Λ : lorentzAlgebra) (i : Fin 3) :
    Λ.1 (Sum.inr i) (Sum.inl 0) = Λ.1 (Sum.inl 0) (Sum.inr i) := by
  simpa only [Fin.isValue, minkowskiMatrix, LieAlgebra.Orthogonal.indefiniteDiagonal, mul_diagonal,
    transpose_apply, Sum.elim_inr, mul_neg, mul_one, diagonal_neg, diagonal_mul, Sum.elim_inl,
    neg_mul, one_mul, neg_inj] using congrArg (fun M ↦ M (Sum.inl 0) (Sum.inr i)) $ mem_iff.mp Λ.2

lemma space_comps (Λ : lorentzAlgebra) (i j : Fin 3) :
    Λ.1 (Sum.inr i) (Sum.inr j) = - Λ.1 (Sum.inr j) (Sum.inr i) := by
  simpa only [minkowskiMatrix, LieAlgebra.Orthogonal.indefiniteDiagonal, diagonal_neg, diagonal_mul,
    Sum.elim_inr, neg_neg, one_mul, mul_diagonal, transpose_apply, mul_neg, mul_one] using
    (congrArg (fun M ↦ M (Sum.inr i) (Sum.inr j)) $ mem_iff.mp Λ.2).symm

end lorentzAlgebra

@[simps!]
instance lorentzVectorAsLieRingModule : LieRingModule lorentzAlgebra (LorentzVector 3) where
  bracket Λ x := Λ.1.mulVec x
  add_lie Λ1 Λ2 x := by
    simp [add_mulVec]
  lie_add Λ x1 x2 := by
    simp only
    exact mulVec_add _ _ _
  leibniz_lie Λ1 Λ2 x := by
    simp [mulVec_add, Bracket.bracket, sub_mulVec]

@[simps!]
instance spaceTimeAsLieModule : LieModule ℝ lorentzAlgebra (LorentzVector 3) where
  smul_lie r Λ x := by
    simp [Bracket.bracket, smul_mulVec_assoc]
  lie_smul r Λ x := by
    simp [Bracket.bracket]
    rw [mulVec_smul]

end SpaceTime
