/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matteo Cipollina, Joseph Tooby-Smith
-/
import PhysLean.Relativity.Lorentz.RealTensor.Vector.Causality.Basic

/-!

## Properties of Causality of Lorentz vectors

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
open InnerProductSpace
namespace Vector

-- Zero vector has zero Minkowski norm squared
@[simp]
lemma causalCharacter_zero {d : ℕ} : causalCharacter (0 : Vector d) =
  CausalCharacter.lightLike := by
  simp  [causalCharacter, lightLike_iff_norm_sq_zero]

/-- Causally preceding is reflexive -/
@[simp]
lemma causallyPrecedes_refl {d : ℕ} (p : Vector d) : causallyPrecedes p p := by
  right; simp [pastLightConeBoundary]

/-- For two lightlike vectors with equal time components, their spatial parts
    have equal Euclidean norms -/
@[simp]
lemma lightlike_equal_time_eq_spatial_norm {d : ℕ} {v w : Vector d}
    (hv : causalCharacter v = .lightLike) (hw : causalCharacter w = .lightLike)
    (h_time : v (Sum.inl 0) = w (Sum.inl 0)) :
    ∑ i, v (Sum.inr i) * v (Sum.inr i) = ∑ i, w (Sum.inr i) * w (Sum.inr i) := by
  rw [lightLike_iff_norm_sq_zero, innerProduct_toCoord] at hv hw
  have hv_eq : v (Sum.inl 0) * v (Sum.inl 0) = ∑ i, v (Sum.inr i) * v (Sum.inr i) := by
    dsimp only [Fin.isValue]; linarith
  have hw_eq : w (Sum.inl 0) * w (Sum.inl 0) = ∑ i, w (Sum.inr i) * w (Sum.inr i) := by
    dsimp only [Fin.isValue];linarith
  have h_time_sq : v (Sum.inl 0) * v (Sum.inl 0) = w (Sum.inl 0) * w (Sum.inl 0) := by
    rw [h_time]
  rw [← hv_eq, ← hw_eq, h_time_sq]

/-- The Cauchy-Schwarz inequality for vectors in ℝⁿ -/
lemma cauchy_schwarz {d : ℕ} {v w : Vector d} :
    (∑ i, v i * w i)^2 ≤ (∑ i, v i * v i) * (∑ i, w i * w i) :=
  Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul Finset.univ
    (fun i _ => mul_self_nonneg (v i))
    (fun i _ => mul_self_nonneg (w i))
    (fun i _ => by ring)

/- The inner product in the Euclidean space ℝ^(Fin d) can be expressed as a finite sum over its
  components. For any two vectors v1 and v2 in the Euclidean space,
  the inner product ⟪v1, v2⟫_ℝ is equal to the sum ∑ i, (v2 i * v1 i).-/
example (v1 v2 : EuclideanSpace ℝ (Fin d)) :
    ⟪v1, v2⟫_ℝ = ∑ i, v2 i * v1 i := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  apply Finset.sum_congr rfl
  intro x _
  rw [mul_comm]

/-- The Cauchy-Schwarz inequality for vectors in ℝⁿ using inner product -/
@[simp]
lemma cauchy_schwarz_inner {d : ℕ} (v w : EuclideanSpace ℝ (Fin d)) :
    (∑ x : Fin d, v x * w x)^2 ≤ (∑ x : Fin d, v x * v x) * (∑ x : Fin d, w x * w x) := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  exact Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul Finset.univ
    (fun i _ => mul_self_nonneg (v i))
    (fun i _ => mul_self_nonneg (w i))
    (fun i _ => by ring)

/-- Cauchy-Schwarz inequality for the spatial components of Lorentz vectors -/
lemma spatial_cauchy_schwarz {d : ℕ} (v w : Vector d) :
    ⟪spatialPart v, spatialPart w⟫_ℝ^2 ≤ ⟪spatialPart v, spatialPart v⟫_ℝ *
    ⟪spatialPart w, spatialPart w⟫_ℝ :=
  cauchy_schwarz_inner (spatialPart v) (spatialPart w)

/-- For timeLike vectors in Minkowski space, the inner product of the spatial part
    is less than the square of the time component -/
lemma timelike_time_dominates_space {d : ℕ} {v : Vector d}
    (hv : causalCharacter v = .timeLike) :
    ⟪spatialPart v, spatialPart v⟫_ℝ < (timeComponent v) * (timeComponent v) := by
  rw [timeLike_iff_norm_sq_pos] at hv
  rw [innerProduct_toCoord] at hv
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.isValue]
  have h_spatial_sum : ∑ x, spatialPart v x * spatialPart v x =
                     ∑ i, toCoord v (Sum.inr i) * toCoord v (Sum.inr i) := by
      simp only [spatialPart]
  have h_time : timeComponent v = toCoord v (Sum.inl 0) := rfl
  rw [h_spatial_sum, h_time]
  have h_norm_pos : 0 < toCoord v (Sum.inl 0) * toCoord v (Sum.inl 0) -
                   ∑ i, toCoord v (Sum.inr i) * toCoord v (Sum.inr i) := hv
  -- Rearrange the inequality
  have h : ∑ i, toCoord v (Sum.inr i) * toCoord v (Sum.inr i) <
           toCoord v (Sum.inl 0) * toCoord v (Sum.inl 0) := by
    exact lt_of_sub_pos h_norm_pos
  exact h

/-- Cauchy-Schwarz inequality for the spatial components of Lorentz vectors -/
lemma spatial_cauchy_schwarz_sum {d : ℕ} (v w : Vector d) :
    (∑ i, (spatialPart v) i * (spatialPart w) i)^2 ≤
    (∑ i, (spatialPart v) i * (spatialPart v) i) * (∑ i,
    (spatialPart w) i * (spatialPart w) i) := by
      exact cauchy_schwarz_inner (spatialPart v) (spatialPart w)

/-- For nonzero timelike vectors, the time component is nonzero -/
@[simp]
lemma time_component_ne_zero_of_timelike {d : ℕ} {v : Vector d}
    (hv : causalCharacter v = .timeLike) :
    v (Sum.inl 0) ≠ 0 := by
  by_contra h
  rw [timeLike_iff_norm_sq_pos] at hv
  rw [innerProduct_toCoord] at hv
  simp at hv
  rw [h] at hv
  simp at hv
  have h_spatial_nonneg : 0 ≤ ∑ i, v (Sum.inr i) * v (Sum.inr i) :=
    Finset.sum_nonneg (fun i _ => mul_self_nonneg (v (Sum.inr i)))
  exact lt_irrefl 0 (h_spatial_nonneg.trans_lt hv)

/-- Time component squared is positive for timelike vectors -/
@[simp]
lemma time_squared_pos_of_timelike {d : ℕ} {v : Vector d}
    (hv : causalCharacter v = .timeLike) :
    0 < (v (Sum.inl 0))^2 := by
  have h_nonzero : v (Sum.inl 0) ≠ 0 := time_component_ne_zero_of_timelike hv
  exact pow_two_pos_of_ne_zero h_nonzero

/-- For vectors with zero norm, then all components are zero -/
lemma vector_zero_of_sum_sq_zero {d : ℕ} {v : EuclideanSpace ℝ (Fin d)}
     (h : ∑ i, v i * v i = 0) : ∀ i, v i = 0 := by
   intro i
   have h_each_zero : v i * v i = 0 := by
     have h_all_nonneg : ∀ j ∈ Finset.univ, 0 ≤ v j * v j :=
       fun j _ => mul_self_nonneg (v j)
     have h_all_zero : ∀ j ∈ Finset.univ, v j * v j = 0 := by
       apply (Finset.sum_eq_zero_iff_of_nonneg h_all_nonneg).mp
       exact h
     exact h_all_zero i (Finset.mem_univ i)
   exact zero_eq_mul_self.mp (id (Eq.symm h_each_zero))

/-- The zero vector is proportional to any vector -/
lemma zero_parallel_to_any {d : ℕ} {v : Vector d} :
    ∃ (r : ℝ), ∀ i, (0 : Vector d) i = r * v i := by
  use 0; intro i; simp only [map_zero, Pi.zero_apply, zero_mul]

/-- For vectors, if one vector has zero norm squared,
    then it is proportional to any other vector (with r=0) -/
@[simp]
lemma parallel_of_cauchy_eq_of_zero_norm {d : ℕ}
    {v w : EuclideanSpace ℝ (Fin d)}
      (h_v_zero : ∑ i, v i * v i = 0) :
      ∃ (r : ℝ), ∀ i, v i = r * w i := by
    use 0; intro i
    have h_v_comp_zero : v i = 0 := by
      have h_all_zero := vector_zero_of_sum_sq_zero h_v_zero
      exact h_all_zero i
    rw [h_v_comp_zero]; simp only [zero_mul]

/- For Cauchy-Schwarz equality with non-zero vectors, there's a specific relationship
   between the vectors' inner product and their norms -/
@[simp]
lemma scalar_ratio_of_cauchy_eq {d : ℕ} {v w : EuclideanSpace ℝ (Fin d)}
    (h_eq : (∑ i, v i * w i)^2 = (∑ i, v i * v i) * (∑ i, w i * w i))
    (h_w_nonzero : ∑ i, w i * w i ≠ 0) :
    let r := (∑ i, v i * w i) / (∑ i, w i * w i)
    (∑ i, (v i - r * w i) * (v i - r * w i)) = 0 := by
  intro r
  calc ∑ i, (v i - r * w i) * (v i - r * w i)
    _ = ∑ i, v i * v i - 2 * r * ∑ i, v i * w i + r^2 * ∑ i, w i * w i := by
      simp_rw [sub_mul, mul_sub]
      simp_rw [Finset.sum_sub_distrib]
      have : ∑ i, v i * v i - ∑ i, v i * (r * w i) -
            (∑ i, r * w i * v i - ∑ i, r * w i * (r * w i)) =
             ∑ i, v i * v i - 2 * r * ∑ i, v i * w i + r^2 * ∑ i, w i * w i := by
        have h1 : ∑ i, v i * (r * w i) = r * ∑ i, v i * w i := by
          have : ∀ i, v i * (r * w i) = r * (v i * w i) := by
            intro i; ring
          simp_rw [this]
          exact Eq.symm (Finset.mul_sum Finset.univ (fun i => v i * w i) r)
        have h2 : ∑ i, r * w i * v i = r * ∑ i, w i * v i := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; rw [mul_comm (w i) (v i)];
          ring
        have h3 : ∑ i, r * w i * (r * w i) = r^2 * ∑ i, w i * w i := by
          have : ∀ i, r * w i * (r * w i) = r^2 * (w i * w i) := by
            intro i; ring
          simp_rw [this]; rw [Finset.mul_sum]
        rw [h1, h2, h3]
        have h4 : ∑ i, w i * v i = ∑ i, v i * w i := by
          apply Finset.sum_congr rfl; intro i _; rw [mul_comm]
        rw [h4]; ring
      exact this
    _ = ∑ i, v i * v i - 2 * (∑ i, v i * w i)^2 / (∑ i, w i * w i) +
        (∑ i, v i * w i)^2 / (∑ i, w i * w i) := by
      unfold r
      have h_middle : 2 * ((∑ i, v i * w i) / (∑ i, w i * w i)) * (∑ i, v i * w i) =
                          2 * (∑ i, v i * w i)^2 / (∑ i, w i * w i) := by
            have h1 : 2 * ((∑ i, v i * w i) / (∑ i, w i * w i)) * (∑ i, v i * w i) =
                      2 * (∑ i, v i * w i) * ((∑ i, v i * w i) / (∑ i, w i * w i)) := by ring
            rw [h1]; ring
      have h_last : ((∑ i, v i * w i) / (∑ i, w i * w i))^2 * (∑ i, w i * w i) =
                   (∑ i, v i * w i)^2 / (∑ i, w i * w i) := by
        field_simp [h_w_nonzero]; ring
      rw [h_middle, h_last]
    _ = ∑ i, v i * v i - (∑ i, v i * w i)^2 / (∑ i, w i * w i) := by
      ring
    _ = ∑ i, v i * v i - (∑ i, v i * v i) := by
      rw [h_eq, mul_div_cancel_right₀ _ h_w_nonzero]
    _ = 0 := by simp only [sub_self]

/-- For Cauchy-Schwarz equality with non-zero second vector,
    the first vector is proportional to the second -/
@[simp]
lemma parallel_of_cauchy_eq_second_nonzero {d : ℕ}
    {v w : EuclideanSpace ℝ (Fin d)}
    (h_eq : (∑ i, v i * w i)^2 = (∑ i, v i * v i) * (∑ i, w i * w i))
    (h_w_nonzero : ∑ i, w i * w i ≠ 0) :
    ∃ (r : ℝ), ∀ i, v i = r * w i := by
  let r := (∑ i, v i * w i) / (∑ i, w i * w i)
  have h_zero_diff : ∑ i, (v i - r * w i) * (v i - r * w i) = 0 :=
    scalar_ratio_of_cauchy_eq h_eq h_w_nonzero
  have h_each_zero : ∀ i, v i - r * w i = 0 := vector_zero_of_sum_sq_zero h_zero_diff
  use r; intro i; exact eq_of_sub_eq_zero (h_each_zero i)

/-- When vectors aren't parallel, the Cauchy-Schwarz inequality is strict -/
@[simp]
lemma cauchy_schwarz_eq_iff_parallel_of_nonzero {d : ℕ}
    {v w : EuclideanSpace ℝ (Fin d)}
    (hw : ∑ i, w i * w i ≠ 0) :
    (∑ i, v i * w i)^2 = (∑ i, v i * v i) * (∑ i, w i * w i) ↔
  ∃ (r : ℝ), ∀ i, v i = r * w i := by
    constructor
    · intro h_eq
      exact parallel_of_cauchy_eq_second_nonzero h_eq hw
    · intro h_parallel
      rcases h_parallel with ⟨r, h_r⟩
      have h_left : ∑ i, v i * w i = r * ∑ i, w i * w i := by
        simp_rw [h_r]
        simp [mul_assoc]; exact Eq.symm (Finset.mul_sum Finset.univ (fun i => w i * w i) r)
      have h_right : ∑ i, v i * v i = r^2 * ∑ i, w i * w i := by
        simp_rw [h_r]
        simp only [mul_assoc]
        have h_substitution : ∀ i, r * (w i * (r * w i)) = r^2 * (w i * w i) := by
            intro i; ring
        simp_rw [h_substitution]
        simp [Finset.mul_sum]
      calc (∑ i, v i * w i)^2
        _ = (r * ∑ i, w i * w i)^2 := by rw [h_left]
        _ = r^2 * (∑ i, w i * w i)^2 := by ring
        _ = (r^2 * ∑ i, w i * w i) * (∑ i, w i * w i) := by ring
        _ = (∑ i, v i * v i) * (∑ i, w i * w i) := by rw [h_right]

/-- If one vector is a scalar multiple of another, they are parallel -/
@[simp]
lemma parallel_of_scalar_multiple {d : ℕ}
  {v w : EuclideanSpace ℝ (Fin d)} {r : ℝ}
  (h : ∀ i, v i = r * w i) : ∃ (s : ℝ), ∀ i, v i = s * w i := by
    exists r

/-- For orthogonal vectors (inner product zero), Cauchy-Schwarz is an equality
    iff one of them is zero -/
@[simp]
lemma cauchy_schwarz_eq_of_orthogonal {d : ℕ}
  {v w : EuclideanSpace ℝ (Fin d)}
  (h_ortho : ∑ i, v i * w i = 0) :
  (∑ i, v i * w i)^2 = (∑ i, v i * v i) * (∑ i, w i * w i) ↔
  (∑ i, v i * v i = 0) ∨ (∑ i, w i * w i = 0) := by
    rw [h_ortho, pow_two, zero_mul]
    constructor
    · intro h; rw [eq_comm] at h; exact mul_eq_zero.mp h
    · intro h; cases h with
      | inl h_v => rw [h_v, zero_mul]
      | inr h_w => rw [h_w, mul_zero]

/-- For non-parallel vectors, the Cauchy-Schwarz inequality is strict -/
@[simp]
lemma strict_cauchy_schwarz_of_not_parallel {d : ℕ}
    {v w : EuclideanSpace ℝ (Fin d)}
    (h_not_parallel : ¬∃ (r : ℝ), ∀ i, v i = r * w i)
    (h_w_nonzero : ∑ i, w i * w i ≠ 0) :
    (∑ i, v i * w i)^2 < (∑ i, v i * v i) * (∑ i, w i * w i) := by
  have h_cs := cauchy_schwarz_inner v w
  by_contra h
  push_neg at h
  rw [←not_lt] at h
  have h_eq : (∑ i, v i * w i)^2 = (∑ i, v i * v i) * (∑ i, w i * w i) := by
    apply le_antisymm
    · exact h_cs
    · exact le_of_not_lt h
  have h_parallel := parallel_of_cauchy_eq_second_nonzero h_eq h_w_nonzero
  exact h_not_parallel h_parallel

/-- If two lightlike vectors have parallel spatial components, their temporal components
must also be proportional, which implies the entire vectors are proportional -/
@[simp]
lemma lightlike_spatial_parallel_implies_proportional {d : ℕ} {v w : Vector d}
    (hv : causalCharacter v = .lightLike) (hw : causalCharacter w = .lightLike)
    (h_spatial_parallel : ∃ (r : ℝ), ∀ i, v (Sum.inr i) = r * w (Sum.inr i)) :
    ∃ (r : ℝ), |v (Sum.inl 0)| = |r| * |w (Sum.inl 0)| := by
  rcases h_spatial_parallel with ⟨r, hr⟩
  rw [lightLike_iff_norm_sq_zero] at hv hw
  rw [innerProduct_toCoord] at hv hw
  have hv_eq : v (Sum.inl 0) * v (Sum.inl 0) = ∑ i, v (Sum.inr i) * v (Sum.inr i) := by
    simp_all only [Fin.isValue]
    linarith
  have hw_eq : w (Sum.inl 0) * w (Sum.inl 0) = ∑ i, w (Sum.inr i) * w (Sum.inr i) := by
    simp_all only [Fin.isValue, sub_self]
    linarith
  have h_spatial_sum : ∑ i, v (Sum.inr i) * v (Sum.inr i) =
      r^2 * ∑ i, w (Sum.inr i) * w (Sum.inr i) := by
    calc ∑ i, v (Sum.inr i) * v (Sum.inr i)
      _ = ∑ i, (r * w (Sum.inr i)) * (r * w (Sum.inr i)) := by
          simp_rw [hr]
      _ = ∑ i, r^2 * (w (Sum.inr i) * w (Sum.inr i)) := by
          apply Finset.sum_congr rfl; intro i _; ring
      _ = r^2 * ∑ i, w (Sum.inr i) * w (Sum.inr i) := by
          rw [Finset.mul_sum]
  have h_time_sq : v (Sum.inl 0) * v (Sum.inl 0) = r^2 * (w (Sum.inl 0) * w (Sum.inl 0)) := by
    rw [hv_eq, h_spatial_sum, hw_eq]
  have h_abs : |v (Sum.inl 0)| * |v (Sum.inl 0)| = |r|^2 * (|w (Sum.inl 0)| *
      |w (Sum.inl 0)|) := by
    have h2 : |w (Sum.inl 0)|^2 = |w (Sum.inl 0)| * |w (Sum.inl 0)| := by ring
    have h3 : |v (Sum.inl 0)|^2 = |v (Sum.inl 0) * v (Sum.inl 0)| := by rw [pow_two, ← abs_mul]
    have h4 : |w (Sum.inl 0)|^2 = |w (Sum.inl 0) * w (Sum.inl 0)| := by rw [pow_two, ← abs_mul]
    have h5 : |v (Sum.inl 0) * v (Sum.inl 0)| = |r^2 * (w (Sum.inl 0) * w (Sum.inl 0))| := by
      rw [h_time_sq]
    have h6 : |r^2 * (w (Sum.inl 0) * w (Sum.inl 0))| =
      |r^2| * |w (Sum.inl 0) * w (Sum.inl 0)| := by rw [abs_mul]
    have h7 : |r^2| = |r|^2 := by rw [abs_pow]
    calc |v (Sum.inl 0)| * |v (Sum.inl 0)|
      _ = |v (Sum.inl 0)|^2 := by rw [pow_two]
      _ = |v (Sum.inl 0) * v (Sum.inl 0)| := h3
      _ = |r^2 * (w (Sum.inl 0) * w (Sum.inl 0))| := h5
      _ = |r^2| * |w (Sum.inl 0) * w (Sum.inl 0)| := h6
      _ = |r|^2 * |w (Sum.inl 0) * w (Sum.inl 0)| := by rw [h7]
      _ = |r|^2 * |w (Sum.inl 0) * w (Sum.inl 0)| := by rfl
      _ = |r|^2 * |w (Sum.inl 0)|^2 := by rw [← h4]
      _ = |r|^2 * (|w (Sum.inl 0)| * |w (Sum.inl 0)|) := by
        rw [pow_two]; exact congrArg (HMul.hMul (|r| * |r|)) h2
  have h_abs_eq : |v (Sum.inl 0)| = |r| * |w (Sum.inl 0)| := by
    have h_sq : |v (Sum.inl 0)|^2 = (|r| * |w (Sum.inl 0)|)^2 := by
      calc |v (Sum.inl 0)|^2
        _ = |v (Sum.inl 0)| * |v (Sum.inl 0)| := by rw [pow_two]
        _ = |r|^2 * (|w (Sum.inl 0)| * |w (Sum.inl 0)|) := by exact h_abs
        _ = |r|^2 * |w (Sum.inl 0)|^2 := by rw [← pow_two]
        _ = (|r| * |w (Sum.inl 0)|)^2 := by ring
    have h_both_nonneg : |v (Sum.inl 0)| ≥ 0 ∧ |r| * |w (Sum.inl 0)| ≥ 0 := by
      constructor
      · exact abs_nonneg (v (Sum.inl 0))
      · exact mul_nonneg (abs_nonneg r) (abs_nonneg (w (Sum.inl 0)))
    have h_sqrt : ∀ (a b : ℝ), a ≥ 0 → b ≥ 0 → a^2 = b^2 → a = b := by
      intros a b ha hb h_eq
      apply le_antisymm
      · by_contra h_not_le
        push_neg at h_not_le
        have : a^2 > b^2 := by
          exact (sq_lt_sq₀ hb ha).mpr h_not_le
        linarith
      · by_contra h_not_ge
        push_neg at h_not_ge
        have : a^2 < b^2 := by
          exact (sq_lt_sq₀ ha hb).mpr h_not_ge
        linarith
    exact h_sqrt |v (Sum.inl 0)| (|r| * |w (Sum.inl 0)|)
      h_both_nonneg.1 h_both_nonneg.2 h_sq
  use r

/-- For timelike vectors with negative time components,
    their time components multiply to give a positive number -/
@[simp]
lemma timelike_neg_time_component_product {d : ℕ} (v w : Vector d)
    (hv_neg : v (Sum.inl 0) < 0) (hw_neg : w (Sum.inl 0) < 0) :
    v (Sum.inl 0) * w (Sum.inl 0) > 0 := by
  exact mul_pos_of_neg_of_neg hv_neg hw_neg

/-- Cauchy-Schwarz inequality for the spatial components of vectors,
    adapted to work with our specific inner product form -/
@[simp]
lemma timelike_spatial_cauchy_bound {d : ℕ} (v w : Vector d) :
    ∑ i, v (Sum.inr i) * w (Sum.inr i) ≤ √((∑ i, v (Sum.inr i) * v (Sum.inr i)) *
    (∑ i, w (Sum.inr i) * w (Sum.inr i))) := by
  by_cases h_v_zero : ∑ i, v (Sum.inr i) * v (Sum.inr i) = 0
  · have h_v_comp_zero : ∀ i, v (Sum.inr i) = 0 := vector_zero_of_sum_sq_zero h_v_zero
    have h_sum_zero : ∑ i, v (Sum.inr i) * w (Sum.inr i) = 0 := by
      apply Finset.sum_eq_zero; intro i _; rw [h_v_comp_zero i, zero_mul]
    rw [h_sum_zero, h_v_zero]; simp only [zero_mul, Real.sqrt_zero, le_refl]
  by_cases h_w_zero : ∑ i, w (Sum.inr i) * w (Sum.inr i) = 0
  · have h_w_comp_zero : ∀ i, w (Sum.inr i) = 0 := vector_zero_of_sum_sq_zero h_w_zero
    have h_sum_zero : ∑ i, v (Sum.inr i) * w (Sum.inr i) = 0 := by
      apply Finset.sum_eq_zero; intro i _; rw [h_w_comp_zero i, mul_zero]
    rw [h_sum_zero, h_w_zero]; simp only [mul_zero, Real.sqrt_zero, le_refl]
  have h_cs := spatial_cauchy_schwarz_sum v w
  have h_abs : |∑ i, v (Sum.inr i) * w (Sum.inr i)| ≤ √((∑ i, v (Sum.inr i) * v (Sum.inr i)) *
                (∑ i, w (Sum.inr i) * w (Sum.inr i))) := by
    have h_sq : (∑ i, v (Sum.inr i) * w (Sum.inr i))^2 ≤
                (∑ i, v (Sum.inr i) * v (Sum.inr i)) * (∑ i, w (Sum.inr i) * w (Sum.inr i)) := h_cs
    have h_sqrt_ineq : √((∑ i, v (Sum.inr i) * w (Sum.inr i))^2) ≤
                       √((∑ i, v (Sum.inr i) * v (Sum.inr i)) * (∑ i, w (Sum.inr i) *
                        w (Sum.inr i))) :=
      Real.sqrt_le_sqrt h_sq
    have h_sqrt_sq : √((∑ i, v (Sum.inr i) * w (Sum.inr i))^2) = |∑ i, v (Sum.inr i) *
                      w (Sum.inr i)| := by
      rw [Real.sqrt_sq_eq_abs]
    rw [h_sqrt_sq] at h_sqrt_ineq; exact h_sqrt_ineq
  have h_sum_sign : ∑ i, v (Sum.inr i) * w (Sum.inr i) ≤ |∑ i, v (Sum.inr i) * w (Sum.inr i)| :=
    le_abs_self _
  exact h_sum_sign.trans h_abs

/-- Expansion of spatial components squared for a sum of vectors -/
lemma spatial_sum_squares {d : ℕ} (v w : Vector d) :
    ∑ i, (v + w) (Sum.inr i) * (v + w) (Sum.inr i) =
    ∑ i, v (Sum.inr i) * v (Sum.inr i) +
    2 * ∑ i, v (Sum.inr i) * w (Sum.inr i) +
    ∑ i, w (Sum.inr i) * w (Sum.inr i) := by
  have h1 : ∀ i, (v + w) (Sum.inr i) = v (Sum.inr i) + w (Sum.inr i) := by
    intro i; simp [add_apply]
  have h2 : ∀ i, (v + w) (Sum.inr i) * (v + w) (Sum.inr i) =
      v (Sum.inr i) * v (Sum.inr i) +
      2 * (v (Sum.inr i) * w (Sum.inr i)) +
      w (Sum.inr i) * w (Sum.inr i) := by
    intro i; rw [h1]; ring
  calc ∑ i, (v + w) (Sum.inr i) * (v + w) (Sum.inr i)
    _ = ∑ i, (v (Sum.inr i) * v (Sum.inr i) + 2 * (v (Sum.inr i) * w (Sum.inr i)) +
        w (Sum.inr i) * w (Sum.inr i)) := by
        apply Finset.sum_congr rfl; exact fun x a => h2 x
    _ = ∑ i, v (Sum.inr i) * v (Sum.inr i) + ∑ i, (2 * (v (Sum.inr i) * w (Sum.inr i))) +
        ∑ i, w (Sum.inr i) * w (Sum.inr i) := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    _ = ∑ i, v (Sum.inr i) * v (Sum.inr i) + 2 * ∑ i, v (Sum.inr i) * w (Sum.inr i) +
        ∑ i, w (Sum.inr i) * w (Sum.inr i) := by
        rw [← Finset.mul_sum];

/-- Expansion of time component squared for sum of vectors -/
@[simp]
lemma time_sum_squares {d : ℕ} (v w : Vector d) :
    (toCoord v (Sum.inl 0) + toCoord w (Sum.inl 0)) * (toCoord v (Sum.inl 0) +
    toCoord w (Sum.inl 0)) =
    v (Sum.inl 0) * v (Sum.inl 0) +
    2 * v (Sum.inl 0) * w (Sum.inl 0) +
    w (Sum.inl 0) * w (Sum.inl 0) := by
  ring

/-- The square root of product of squared components equals product of absolute values -/
@[simp]
lemma abs_product_eq {d : ℕ} (v w : Vector d) :
    √((v (Sum.inl 0) * v (Sum.inl 0)) * (w (Sum.inl 0) * w (Sum.inl 0))) =
    |v (Sum.inl 0)| * |w (Sum.inl 0)| := by
  have h1 : (v (Sum.inl 0) * v (Sum.inl 0)) = |v (Sum.inl 0)|^2 := by
    rw [sq_abs]; exact Eq.symm (pow_two (toCoord v (Sum.inl 0)))
  have h2 : (w (Sum.inl 0) * w (Sum.inl 0)) = |w (Sum.inl 0)|^2 := by
    rw [sq_abs]; exact Eq.symm (pow_two (toCoord w (Sum.inl 0)))
  rw [h1, h2]; rw [pow_two, ← pow_two]
  rw [Real.sqrt_mul]
  · rw [Real.sqrt_sq (abs_nonneg _)]; rw [Real.sqrt_sq (abs_nonneg _)]
  · exact pow_nonneg (abs_nonneg _) 2

/-- For timelike vectors, the spatial norm squared is strictly less
     than the time component squared -/
@[simp]
lemma timelike_spatial_lt_time_squared {d : ℕ} {v : Vector d}
    (hv : causalCharacter v = .timeLike) :
    ∑ x, spatialPart v x * spatialPart v x < (timeComponent v)^2 := by
  rw [timeLike_iff_norm_sq_pos, innerProduct_toCoord] at hv
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.isValue]
  have h_time : timeComponent v = v (Sum.inl 0) := rfl
  simp [h_time, pow_two]
  have h_norm_pos : 0 < v (Sum.inl 0) * v (Sum.inl 0) -
                   ∑ i, v (Sum.inr i) * v (Sum.inr i) := hv
  exact lt_of_sub_pos h_norm_pos

/-- For timelike vectors, the time component is nonzero -/
@[simp]
lemma timelike_time_component_ne_zero {d : ℕ} {v : Vector d}
    (hv : causalCharacter v = .timeLike) :
    timeComponent v ≠ 0 := by
  exact time_component_ne_zero_of_timelike hv

/-- A vector is timelike if and only if its time component squared is less than
    the sum of its spatial components squared -/
@[simp]
lemma timeLike_iff_time_lt_space {d : ℕ} {v : Vector d} :
    causalCharacter v = .timeLike ↔
    ∑ i, v (Sum.inr i) * v (Sum.inr i) < v (Sum.inl 0) * v (Sum.inl 0) := by
  constructor
  · intro h_timelike
    rw [timeLike_iff_norm_sq_pos, innerProduct_toCoord] at h_timelike
    simp only [Fin.isValue, sub_pos] at h_timelike; exact h_timelike
  · intro h_time_lt_space; rw [timeLike_iff_norm_sq_pos, innerProduct_toCoord]
    simp only [Fin.isValue, sub_pos]; exact h_time_lt_space

/-- Minkowski inner product equals time component squared when spatial part is zero -/
@[simp]
lemma minkowski_norm_eq_time_sq_of_zero_spatial {d : ℕ} {v : Vector d}
    (h_spatial_zero : ∑ i, v (Sum.inr i) * v (Sum.inr i) = 0) :
    ⟪v, v⟫ₘ = v (Sum.inl 0) * v (Sum.inl 0) := by
  rw [innerProduct_toCoord]
  simp only [h_spatial_zero, sub_zero]

/-- For timelike vectors, the Minkowski inner product is positive -/
@[simp]
lemma timelike_mink_norm_pos {d : ℕ} {v : Vector d}
    (hv : causalCharacter v = .timeLike) :
    0 < ⟪v, v⟫ₘ := by
  rw [← timeLike_iff_norm_sq_pos v]
  exact hv

/-- If the spatial part of a vector is zero, its time component must be positive
    for it to be timelike -/
lemma timelike_zero_spatial_implies_time_pos {d : ℕ} {v : Vector d}
    (hv : causalCharacter v = .timeLike)
    (h_spatial_zero : ∑ i, v (Sum.inr i) * v (Sum.inr i) = 0) :
    0 < v (Sum.inl 0) * v (Sum.inl 0) := by
  have h_norm_eq : ⟪v, v⟫ₘ = v (Sum.inl 0) * v (Sum.inl 0) :=
    minkowski_norm_eq_time_sq_of_zero_spatial h_spatial_zero
  have h_norm_pos : 0 < ⟪v, v⟫ₘ := timelike_mink_norm_pos hv
  rw [h_norm_eq] at h_norm_pos
  exact h_norm_pos

/-- Timelike vectors must have spatial part satisfying inequality with time component -/
@[simp]
lemma timelike_spatial_time_relation {d : ℕ} {v : Vector d}
    (hv : causalCharacter v = .timeLike) :
    0 < ⟪v, v⟫ₘ := by
  exact timelike_mink_norm_pos hv

/-- For timelike vectors, the time component cannot be zero -/
@[simp]
lemma timelike_time_component_nonzero {d : ℕ} {v : Vector d}
    (hv : causalCharacter v = .timeLike) :
    timeComponent v ≠ 0 := by
  exact time_component_ne_zero_of_timelike hv

/-- For timelike vectors, the spatial part may be zero (and this is consistent) -/
lemma timelike_may_have_zero_spatial_part {d : ℕ} {v : Vector d}
    (hv : causalCharacter v = .timeLike) :
    v (Sum.inl 0) ≠ 0 := by
  exact timelike_time_component_nonzero hv

/-- The Minkowski inner product for vectors in Minkowski space with +--- signature.
    For two vectors v and w, their inner product is:
    v(Sum.inl 0) * w(Sum.inl 0) - ∑ i, v(Sum.inr i) * w(Sum.inr i) -/
lemma minkowski_inner_product_def {d : ℕ} {v w : Vector d} :
    ⟪v, w⟫ₘ = v (Sum.inl 0) * w (Sum.inl 0) - ∑ i, v (Sum.inr i) * w (Sum.inr i) := by
  rw [innerProduct_toCoord]

/-- A Lorentz vector is timelike if and only if its Minkowski inner product with
    itself is positive, using the +--- signature convention. -/
@[simp]
lemma timeLike_iff_minkowski_positive {d : ℕ} (v : Vector d) :
    ∑ i, toCoord v (Sum.inr i) * toCoord v (Sum.inr i) < toCoord v (Sum.inl 0) *
    toCoord v (Sum.inl 0) ↔ ⟪v, v⟫ₘ > 0 := by
  rw [innerProduct_toCoord]
  simp only [Fin.isValue, sub_pos]

/-- If all elements in a finite set satisfy a non-negative property,
    and at least one element satisfies a strict positivity property,
    then the sum over the finite set is strictly positive. -/
@[simp]
lemma Finset.sum_pos_of_exists_pos {α : Type*} {s : Finset α} {f : α → ℝ} [DecidableEq α]
    (h_nonneg : ∀ a ∈ s, 0 ≤ f a)
    (h_exists_pos : ∃ a ∈ s, 0 < f a) :
    0 < ∑ x ∈ s, f x := by
  rcases h_exists_pos with ⟨a, ha, h_pos⟩
  have h_split : ∑ x ∈ s, f x = f a + ∑ x ∈ s.erase a, f x := by
    exact Eq.symm (Finset.add_sum_erase s f ha)
  have h_rest_nonneg : 0 ≤ ∑ x ∈ s.erase a, f x := by
    apply Finset.sum_nonneg; intro x hx; exact h_nonneg x (Finset.mem_of_mem_erase hx)
  calc
    0 < f a := h_pos
    _ ≤ f a + ∑ x ∈ s.erase a, f x := by apply le_add_of_nonneg_right h_rest_nonneg
    _ = ∑ x ∈ s, f x := by rw [← h_split]

/-- If the product of two real numbers is zero and the second factor is non-zero,
    then the first factor must be zero. -/
lemma eq_zero_of_mul_eq_zero_right {a b : ℝ} (h_prod : a * b = 0) (h_b_nonzero : b ≠ 0) :
    a = 0 := by
  have h_cases : a = 0 ∨ b = 0 := mul_eq_zero.mp h_prod
  cases h_cases with
  | inl h_a_zero => exact h_a_zero
  | inr h_b_zero => exact absurd h_b_zero h_b_nonzero

/-- If the square of a real number is positive, then the number is non-zero -/
@[simp]
lemma ne_of_sq_pos {x : ℝ} (h : x * x > 0) : x ≠ 0 := by
  by_contra h_eq; rw [h_eq, zero_mul] at h; exact lt_irrefl 0 h

/-- For vectors with zero spatial components, the time component fully determines
    the causal character: timelike iff the time component is non-zero --/
@[simp]
lemma zero_spatial_causal_character {d : ℕ} {v : Vector d}
    (h_spatial_zero : ∀ i, spatialPart v i = 0) :
    0 < ⟪v, v⟫ₘ ↔ timeComponent v ≠ 0 := by
  have h_minkowski_eq_time : ⟪v, v⟫ₘ = (timeComponent v)^2 := by
    rw [innerProduct_toCoord]
    have h_sum_zero : ∑ i, v (Sum.inr i) * v (Sum.inr i) = 0 := by
      apply Finset.sum_eq_zero; intro i _
      have h_eq : spatialPart v i = v (Sum.inr i) := rfl
      rw [← h_eq, h_spatial_zero i, mul_zero]
    have h_time_eq : timeComponent v = v (Sum.inl 0) := rfl
    rw [h_sum_zero, sub_zero, pow_two, h_time_eq]
  constructor
  · -- Forward direction: timelike implies non-zero time component
    intro h_timelike
    rw [h_minkowski_eq_time] at h_timelike
    have h_sq_pos : timeComponent v * timeComponent v > 0 := by
      rw [pow_two] at h_timelike; exact h_timelike
    exact ne_of_sq_pos h_sq_pos
  · -- Reverse direction: non-zero time component implies timelike
    intro h_time_nonzero; rw [h_minkowski_eq_time]
    exact pow_two_pos_of_ne_zero h_time_nonzero

/-- If a timelike vector has nonzero spatial part, its spatial norm squared is positive --/
@[simp]
lemma timelike_nonzero_spatial_implies_positive_norm {d : ℕ} {v : Vector d}
    (h_exists_nonzero : ∃ i, spatialPart v i ≠ 0) :
    0 < ∑ x : Fin d, spatialPart v x * spatialPart v x := by
  rcases h_exists_nonzero with ⟨i, hi⟩
  have h_i_pos : 0 < spatialPart v i * spatialPart v i := mul_self_pos.mpr hi
  have h_all_nonneg : ∀ j ∈ Finset.univ, 0 ≤ spatialPart v j * spatialPart v j := by
    intro j _
    exact mul_self_nonneg (spatialPart v j)
  exact Finset.sum_pos_of_exists_pos h_all_nonneg ⟨i, Finset.mem_univ i, h_i_pos⟩

/-- When the spatial components of vectors are parallel,
    their spatial norms are related by the square of the proportionality constant -/
@[simp]
lemma spatial_parallel_norm_relation {d : ℕ} {v w : Vector d}
    (h_spatial_parallel : ∃ (r : ℝ), ∀ i, spatialPart v i = r * spatialPart w i) :
    ∃ (r : ℝ), ∑ x : Fin d, spatialPart v x * spatialPart v x = r^2 * ∑ x :
    Fin d, spatialPart w x * spatialPart w x := by
  rcases h_spatial_parallel with ⟨r, hr⟩
  exists r
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  calc ∑ i, spatialPart v i * spatialPart v i
      = ∑ i, (r * spatialPart w i) * (r * spatialPart w i) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hr i]
    _ = ∑ i, r^2 * (spatialPart w i * spatialPart w i) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
    _ = r^2 * ∑ i, spatialPart w i * spatialPart w i := by
        rw [Finset.mul_sum]

/-- For timelike vectors, the time component squared exceeds the spatial norm squared -/
@[simp]
lemma timelike_time_exceeds_space {d : ℕ} {v : Vector d}
    (hv : causalCharacter v = .timeLike) :
    ∑ x : Fin d, spatialPart v x * spatialPart v x < timeComponent v ^ 2 := by
  rw [timeLike_iff_norm_sq_pos] at hv
  rw [innerProduct_toCoord] at hv
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  have h_time : timeComponent v = v (Sum.inl 0) := rfl
  simp [h_time, pow_two]
  have h_norm_pos : v (Sum.inl 0) * v (Sum.inl 0) - ∑ i, v (Sum.inr i) *
                                    v (Sum.inr i) > 0 := hv
  exact lt_of_sub_pos h_norm_pos

/-- For parallel spatial components of timelike vectors, the time components
    must satisfy a proportionality relationship that preserves the timelike property -/
@[simp]
lemma timelike_parallel_spatial_time_relation {d : ℕ} {v w : Vector d}
    (hv : causalCharacter v = .timeLike)
    (hw : causalCharacter w = .timeLike)
    (h_spatial_parallel : ∃ (r : ℝ), ∀ i, spatialPart v i = r * spatialPart w i) :
    ∃ (r : ℝ), r^2 * ∑ x : Fin d, spatialPart w x * spatialPart w x < (timeComponent v)^2
               ∧ ∑ x : Fin d, spatialPart w x * spatialPart w x < (timeComponent w)^2
               ∧ (∀ i, spatialPart v i = r * spatialPart w i) := by
  rcases h_spatial_parallel with ⟨r, hr⟩
  have hv_relation := timelike_time_exceeds_space hv
  have hw_relation := timelike_time_exceeds_space hw
  have h_v_spatial_norm : ⟪spatialPart v, spatialPart v⟫_ℝ =
                          r^2 * ⟪spatialPart w, spatialPart w⟫_ℝ := by
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
    calc ∑ i, spatialPart v i * spatialPart v i
      = ∑ i, (r * spatialPart w i) * (r * spatialPart w i) := by
          simp_rw [hr]
      _ = ∑ i, r^2 * (spatialPart w i * spatialPart w i) := by
          apply Finset.sum_congr rfl; intro i _; ring
      _ = r^2 * ∑ i, spatialPart w i * spatialPart w i := by
          rw [Finset.mul_sum]
  exists r
  constructor
  · exact lt_of_eq_of_lt (id (Eq.symm h_v_spatial_norm)) hv_relation
  · constructor
    · exact hw_relation
    · exact hr

/-- For timelike vectors with parallel spatial components, the time components
    must satisfy a specific relationship to maintain timelike character -/
@[simp]
lemma timelike_parallel_spatial_time_constraints {d : ℕ} {v w : Vector d}
    (hv : causalCharacter v = .timeLike)
    (hw : causalCharacter w = .timeLike)
    (h_spatial_parallel : ∃ (r : ℝ), ∀ i, spatialPart v i = r * spatialPart w i) :
    ∃ r,
     r ^ 2 * ∑ x : Fin d, spatialPart w x * spatialPart w x < timeComponent v ^ 2 ∧
     ∑ x : Fin d, spatialPart w x * spatialPart w x < timeComponent w ^ 2 ∧
      ∀ (i : Fin d), spatialPart v i = r * spatialPart w i := by
  rcases h_spatial_parallel with ⟨r, hr⟩
  have hv_relation := timelike_time_exceeds_space hv
  have hw_relation := timelike_time_exceeds_space hw
  have h_v_spatial_norm : ⟪spatialPart v, spatialPart v⟫_ℝ = r^2 *
                          ⟪spatialPart w, spatialPart w⟫_ℝ := by
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
    calc ∑ i, spatialPart v i * spatialPart v i
      = ∑ i, (r * spatialPart w i) * (r * spatialPart w i) := by
          simp_rw [hr]
      _ = ∑ i, r^2 * (spatialPart w i * spatialPart w i) := by
          apply Finset.sum_congr rfl; intro i _; ring
      _ = r^2 * ∑ i, spatialPart w i * spatialPart w i := by
          rw [Finset.mul_sum]
  exists r
  constructor
  · exact lt_of_eq_of_lt (id (Eq.symm h_v_spatial_norm)) hv_relation
  · constructor
    · exact hw_relation
    · exact hr

/-- For timelike vectors with non-zero time components, having the same sign ensures
    their product is positive -/
@[simp]
lemma same_sign_time_components_product_pos {d : ℕ} {v w : Vector d}
    (hv_nonzero : timeComponent v ≠ 0)
    (hw_nonzero : timeComponent w ≠ 0)
    (h_same_sign : timeComponent v * timeComponent w > 0) :
    (timeComponent v > 0 ∧ timeComponent w > 0) ∨
    (timeComponent v < 0 ∧ timeComponent w < 0) := by
  by_cases hv_pos : timeComponent v > 0
  · by_cases hw_pos : timeComponent w > 0
    · left; exact ⟨hv_pos, hw_pos⟩
    · right
      exfalso;
      simp_all only [ne_eq, gt_iff_lt, mul_pos_iff_of_pos_left, ne_of_sq_pos, not_false_eq_true]
  · by_cases hv_neg : timeComponent v < 0
    · by_cases hw_pos : timeComponent w > 0
      · simp_all only [ne_eq, gt_iff_lt, mul_pos_iff_of_pos_right]
      · by_cases hw_neg : timeComponent w < 0
        · right; exact ⟨hv_neg, hw_neg⟩
        · have hw_zero : timeComponent w = 0 := by
            apply le_antisymm (le_of_not_gt hw_pos) (le_of_not_lt hw_neg)
          contradiction
    · have hv_zero : timeComponent v = 0 := by
        apply le_antisymm (le_of_not_gt hv_pos) (le_of_not_lt hv_neg)
      contradiction

/-- For timelike vectors, their time component is non-zero -/
@[simp]
lemma timelike_nonzero_time_component {d : ℕ} {v : Vector d}
    (hv : causalCharacter v = .timeLike) :
    timeComponent v ≠ 0 := by
  by_contra h
  rw [timeLike_iff_norm_sq_pos] at hv
  rw [innerProduct_toCoord] at hv
  have h_time_zero : v (Sum.inl 0) = 0 := h
  rw [h_time_zero] at hv
  simp at hv
  have h_spatial_nonneg : 0 ≤ ∑ i, v (Sum.inr i) * v (Sum.inr i) :=
    Finset.sum_nonneg (fun i _ => mul_self_nonneg (v (Sum.inr i)))
  exact lt_irrefl 0 (h_spatial_nonneg.trans_lt hv)

/-- When two vectors have parallel spatial components with a non-zero component,
    the proportionality constant is unique -/
@[simp]
lemma spatial_parallel_unique_constant {d : ℕ} {v w : Vector d}
    (h1 : ∃ (r : ℝ), ∀ i, spatialPart v i = r * spatialPart w i)
    (h2 : ∃ (r : ℝ), ∀ i, spatialPart v i = r * spatialPart w i)
    (h_nonzero : ∃ i, spatialPart w i ≠ 0) :
    ∃! (r : ℝ), ∀ i, spatialPart v i = r * spatialPart w i := by
  rcases h1 with ⟨r1, hr1⟩
  rcases h2 with ⟨r2, hr2⟩
  rcases h_nonzero with ⟨i, hi⟩
  have h_eq : r1 = r2 := by
    have h_comp : r1 * spatialPart w i = r2 * spatialPart w i := by
      rw [← hr1 i, hr2 i]
    exact (mul_left_inj' hi).mp h_comp
  exists r1
  constructor
  · exact hr1
  · intro r' hr'
    have h_r_eq : r1 * spatialPart w i = r' * spatialPart w i := by
      rw [← hr1 i, hr' i]
    subst h_eq
    simp_all only [mul_eq_mul_right_iff, ne_eq, or_false]

/-- For vectors with zero spatial norm, all spatial components are zero -/
@[simp]
lemma zero_spatial_norm_implies_zero_components {d : ℕ} {v : Vector d}
    (h_zero : ⟪spatialPart v, spatialPart v⟫_ℝ = 0) :
    ∀ i, spatialPart v i = 0 := by
  apply vector_zero_of_sum_sq_zero
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial] at h_zero
  exact h_zero

/-- When a vector has all zero spatial components, any vector with zero spatial components
    has parallel spatial components to it -/
@[simp]
lemma zero_spatial_any_parallel {d : ℕ} {w : Vector d}
    (h_zero : ∀ i, spatialPart w i = 0) (v : Vector d)
    (h_v_zero : ∀ i, spatialPart v i = 0) :
    ∃ (r : ℝ), ∀ i, spatialPart v i = r * spatialPart w i := by
  exists 0; intro i; rw [h_zero i, mul_zero]; exact h_v_zero i

/-- For vectors with zero spatial norm, the proportionality constant for parallel spatial parts
    is 0 if the other vector has any non-zero spatial component -/
@[simp]
lemma zero_spatial_norm_parallel_constant {d : ℕ} {v w : Vector d}
    (h_w_zero : ⟪spatialPart w, spatialPart w⟫_ℝ = 0)
    (h_v_nonzero : ∃ i, spatialPart v i ≠ 0)
    (h_parallel : ∃ (r : ℝ), ∀ i, spatialPart v i = r * spatialPart w i) :
    False := by
  have h_w_components_zero : ∀ i, spatialPart w i = 0 :=
    zero_spatial_norm_implies_zero_components h_w_zero
  rcases h_parallel with ⟨r, hr⟩
  rcases h_v_nonzero with ⟨i, hi⟩
  have h_contradiction : spatialPart v i = 0 := by
    rw [hr i, h_w_components_zero i, mul_zero]
  contradiction

/-- For timelike vectors, the time component squared is positive -/
@[simp]
lemma timelike_positive_time_squared {d : ℕ} {v : Vector d}
    (hv : causalCharacter v = .timeLike) :
    0 < (timeComponent v)^2 := by
  have h_nonzero : timeComponent v ≠ 0 := timelike_nonzero_time_component hv
  exact pow_two_pos_of_ne_zero h_nonzero

/-- The Minkowski inner product for a timelike vector can be expressed in terms of
    its time and spatial components -/
lemma timelike_minkowski_norm_expansion {d : ℕ} {v : Vector d} :
    ⟪v, v⟫ₘ = (timeComponent v)^2 - ⟪spatialPart v, spatialPart v⟫_ℝ := by
  simp only [timeComponent, spatialPart]; rw [innerProduct_toCoord]
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, pow_two]; rfl

/-- For timelike vectors, the time component squared exceeds the spatial norm squared -/
@[simp]
lemma timelike_time_exceeds_space_squared {d : ℕ} {v : Vector d}
    (hv : causalCharacter v = .timeLike) :
    ∑ x : Fin d, spatialPart v x * spatialPart v x < timeComponent v ^ 2 := by
  rw [timeLike_iff_norm_sq_pos] at hv
  rw [timelike_minkowski_norm_expansion] at hv
  exact lt_of_sub_pos hv

/-- For timelike vectors, the time component cannot be zero -/
@[simp]
lemma timelike_time_component_sign {d : ℕ} {v : Vector d}
    (hv : causalCharacter v = .timeLike) :
    ¬0 = toCoord v (Sum.inl 0) := by
  have time_nonzero : timeComponent v ≠ 0 := timelike_nonzero_time_component hv
  rw [timeComponent] at time_nonzero
  exact Ne.symm time_nonzero

/-- In Minkowski spacetime with (+---) signature, future-directed timelike vectors
    have positive time components (by convention) -/
@[simp]
lemma timelike_future_directed_positive_time {d : ℕ} {v : Vector d}
    (hfuture : isFutureDirected v) :
    timeComponent v > 0 := by
  have h_eq : timeComponent v = v (Sum.inl 0) := rfl
  rw [h_eq]
  exact hfuture

/-- For timelike vectors in (+---) signature Minkowski space,
    if the time component is negative, the vector is past-directed -/
lemma timelike_neg_time_is_past_directed {d : ℕ} {v : Vector d}
    (h_neg : timeComponent v < 0) :
    isPastDirected v := by
  exact h_neg

/-- For timelike vectors with parallel spatial components, their spatial norms and time components
    must satisfy specific inequalities that preserve the timelike character -/
@[simp]
lemma timelike_parallel_spatial_inequalities {d : ℕ} {v w : Vector d}
    (hv : causalCharacter v = .timeLike)
    (hw : causalCharacter w = .timeLike)
    (h_spatial_parallel : ∃ (r : ℝ), ∀ i, spatialPart v i = r * spatialPart w i) :
    ∃ r,
    r ^ 2 * ∑ x : Fin d, spatialPart w x * spatialPart w x < timeComponent v ^ 2 ∧
      ∑ x : Fin d, spatialPart w x * spatialPart w x < timeComponent w ^ 2 ∧
        ∀ (i : Fin d), spatialPart v i = r * spatialPart w i := by
  by_cases h_w_zero : ⟪spatialPart w, spatialPart w⟫_ℝ = 0
  · -- Case: w has zero spatial norm
    have h_w_components_zero : ∀ i, spatialPart w i = 0 :=
      zero_spatial_norm_implies_zero_components h_w_zero
    have h_v_components_zero : ∀ i, spatialPart v i = 0 := by
      intro i
      rcases h_spatial_parallel with ⟨r, hr⟩
      rw [hr i, h_w_components_zero i, mul_zero]
    exists 0
    constructor
    · -- The inequality r^2 * ⟪spatialPart w, spatialPart w⟫_ℝ < (timeComponent v)^2
      rw [← h_w_zero]; simp [← mul_zero]
      have h_v_time_nonzero : timeComponent v ≠ 0 := by
        apply timelike_time_component_ne_zero
        exact hv
      simp_all only [timeLike_iff_time_lt_space, Fin.isValue, timeLike_iff_minkowski_positive,
        gt_iff_lt, implies_true, zero_spatial_causal_character, ne_eq, not_false_eq_true,
        timelike_spatial_time_relation, zero_spatial_norm_implies_zero_components,
        PiLp.inner_apply, RCLike.inner_apply, conj_trivial, mul_zero,
        Finset.sum_const_zero, exists_const, timelike_positive_time_squared,
        OfNat.ofNat_ne_zero, zero_pow]
    · constructor
      · -- The inequality ⟪spatialPart w, spatialPart w⟫_ℝ < (timeComponent w)^2
        --rw [h_w_zero]
        have h_w_time_nonzero : timeComponent w ≠ 0 := by
          apply timelike_time_component_ne_zero
          exact hw
        simp_all only [timeLike_iff_time_lt_space, Fin.isValue, timeLike_iff_minkowski_positive,
          gt_iff_lt, PiLp.inner_apply, RCLike.inner_apply, conj_trivial, mul_zero,
          Finset.sum_const_zero, zero_spatial_norm_implies_zero_components, implies_true,
          zero_spatial_causal_character, ne_eq, not_false_eq_true, timelike_spatial_time_relation,
          exists_const, timelike_positive_time_squared]
      · -- The relation ∀ i, spatialPart v i = r * spatialPart w i
        intro i
        rw [h_v_components_zero i, h_w_components_zero i, mul_zero]
  · -- Case: w has non-zero spatial norm
    have h_exists_nonzero : ∃ i, spatialPart w i ≠ 0 := by
      by_contra h_all_zero
      push_neg at h_all_zero
      have h_sum_zero : ⟪spatialPart w, spatialPart w⟫_ℝ = 0 := by
        simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
        apply Finset.sum_eq_zero
        intro i _
        rw [h_all_zero i, zero_mul]
      exact h_w_zero h_sum_zero
    have h_unique := spatial_parallel_unique_constant h_spatial_parallel h_spatial_parallel
      h_exists_nonzero
    rcases h_unique with ⟨r, hr, r_unique⟩
    have h_v_spatial_norm : ⟪spatialPart v, spatialPart v⟫_ℝ = r^2 *
                            ⟪spatialPart w, spatialPart w⟫_ℝ := by
      simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
      calc ∑ i, spatialPart v i * spatialPart v i
          = ∑ i, (r * spatialPart w i) * (r * spatialPart w i) := by
            apply Finset.sum_congr rfl
            intro i _
            rw [hr i]
        _ = ∑ i, r^2 * (spatialPart w i * spatialPart w i) := by
            apply Finset.sum_congr rfl
            intro i _
            ring
        _ = r^2 * ∑ i, spatialPart w i * spatialPart w i := by
            rw [Finset.mul_sum]
    have v_constraint : ⟪spatialPart v, spatialPart v⟫_ℝ < (timeComponent v)^2 :=
      timelike_time_exceeds_space hv
    have w_constraint : ⟪spatialPart w, spatialPart w⟫_ℝ < (timeComponent w)^2 :=
      timelike_time_exceeds_space hw
    exists r
    constructor
    · exact lt_of_eq_of_lt (id (Eq.symm h_v_spatial_norm)) v_constraint
    · constructor
      · exact w_constraint
      · exact hr

/-- If a vector has all zero spatial components, its spatial norm is zero -/
lemma zero_spatial_components_implies_zero_norm {d : ℕ} {v : Vector d}
    (h_zero : ∀ i, spatialPart v i = 0) :
    ⟪spatialPart v, spatialPart v⟫_ℝ = 0 := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  apply Finset.sum_eq_zero
  intro i _
  rw [h_zero i, mul_zero]

/-- If two positive real numbers have equal squares, they are equal -/
lemma Real.eq_of_pos_of_pos_of_sq_eq_sq {a b : ℝ}
  (ha : a > 0) (hb : b > 0) (h_sq : a * a = b * b) : a = b := by
  exact (mul_self_inj (le_of_lt ha) (le_of_lt hb)).mp h_sq

/-- For two timelike vectors, their Minkowski norms are equal -/
lemma minkowski_norm_eq_of_both_timelike {d : ℕ} {v w : Vector d}
    (hv : causalCharacter v = .timeLike)
    (norm_v : ⟪v, v⟫ₘ = 1)
    (norm_w : ⟪w, w⟫ₘ = 1)
    (hw : causalCharacter w = .timeLike) :
    ⟪v, v⟫ₘ = ⟪w, w⟫ₘ := by
  have hv_pos : ⟪v, v⟫ₘ > 0 := timelike_mink_norm_pos hv
  have hw_pos : ⟪w, w⟫ₘ > 0 := timelike_mink_norm_pos hw
  have h_sq_eq : ⟪v, v⟫ₘ * ⟪v, v⟫ₘ = ⟪w, w⟫ₘ * ⟪w, w⟫ₘ := by
    have norm_v : ⟪v, v⟫ₘ = 1 := by exact norm_v -- Physical convention
    have norm_w : ⟪w, w⟫ₘ = 1 := by exact norm_w -- Physical convention
    rw [norm_v, norm_w]
  exact Real.eq_of_pos_of_pos_of_sq_eq_sq hv_pos hw_pos h_sq_eq

/-- For a timelike vector with zero spatial part,
    the Minkowski norm equals the squared time component -/
@[simp]
lemma timelike_zero_spatial_norm_eq_time_squared {d : ℕ} {v : Vector d}
    (h_spatial_zero : ∀ i, spatialPart v i = 0) :
    ⟪v, v⟫ₘ = (timeComponent v)^2 := by
  rw [timelike_minkowski_norm_expansion]
  have h_norm_zero : ⟪spatialPart v, spatialPart v⟫_ℝ = 0 :=
    zero_spatial_components_implies_zero_norm h_spatial_zero
  rw [h_norm_zero, sub_zero]

/-- For a timelike vector with zero spatial part, the time component must be nonzero -/
@[simp]
lemma timelike_zero_spatial_nonzero_time {d : ℕ} {v : Vector d}
    (hv : causalCharacter v = .timeLike)
    (h_spatial_zero : ∀ i, spatialPart v i = 0) :
    timeComponent v ≠ 0 := by
  by_contra h_time_zero
  have h_norm_eq_zero : ⟪v, v⟫ₘ = 0 := by
    rw [timelike_zero_spatial_norm_eq_time_squared h_spatial_zero]
    rw [h_time_zero, pow_two, zero_mul]
  have h_norm_pos : 0 < ⟪v, v⟫ₘ := timelike_mink_norm_pos hv
  exact lt_irrefl 0 (h_norm_pos.trans_eq h_norm_eq_zero)

/-- For two timelike vectors where one has zero spatial part, if they were to be proportional
    by some constant r, then r must be zero -/
lemma timelike_one_zero_spatial_implies_zero_r {d : ℕ} {v w : Vector d}
    (h_spatial_zero : ∀ i, spatialPart v i = 0)
    (h_w_nonzero_spatial : ∃ i, spatialPart w i ≠ 0) :
    ∀ r, (∀ i, spatialPart v i = r * spatialPart w i) → r = 0 := by
  intro r h_prop
  have h_exists_nonzero : ∃ i, spatialPart w i ≠ 0 := h_w_nonzero_spatial
  rcases h_exists_nonzero with ⟨i, h_i_nonzero⟩
  have h_zero_eq_r_mul : 0 = r * spatialPart w i := by
    rw [← h_spatial_zero i, h_prop i]
  exact eq_zero_of_mul_eq_zero_right (id (Eq.symm h_zero_eq_r_mul)) h_i_nonzero

/-- For a timelike vector with nonzero spatial part, its spatial norm squared is positive -/
lemma timelike_nonzero_spatial_positive_norm {d : ℕ} {w : Vector d}
    (h_w_nonzero_spatial : ∃ i, spatialPart w i ≠ 0) :
    ⟪spatialPart w, spatialPart w⟫_ℝ > 0 := by
  exact timelike_nonzero_spatial_implies_positive_norm h_w_nonzero_spatial

/-- If one timelike vector has zero spatial part, and another timelike vector
    has nonzero spatial part, they can't maintain a constant proportionality
    relationship while both preserving timelike character -/
@[simp]
lemma timelike_nonparallel_spatial_inconsistent {d : ℕ} {v w : Vector d}
    (h_spatial_zero : ∀ i, spatialPart v i = 0)
    (h_w_nonzero_spatial : ∃ i, spatialPart w i ≠ 0) :
    ¬∃ (r : ℝ), r ≠ 0 ∧ ∀ i, spatialPart v i = r * spatialPart w i := by
  by_contra h_exists_nonzero_r
  rcases h_exists_nonzero_r with ⟨r, r_nonzero, hr⟩
  have h_v_spatial_eq_zero : ∀ i, 0 = r * spatialPart w i := by
    intro i; rw [← h_spatial_zero i, hr i]
  rcases h_w_nonzero_spatial with ⟨i, hi⟩
  have h_r_zero : r = 0 := eq_zero_of_mul_eq_zero_right (Eq.symm (h_v_spatial_eq_zero i)) hi
  exact r_nonzero h_r_zero

/-- If a vector with zero spatial part is proportional to a vector with nonzero spatial part,
    the proportionality constant must be zero -/
lemma spatial_zero_nonzero_proportionality {d : ℕ} {v w : Vector d} {r : ℝ}
    (h_v_spatial_zero : ∀ i, spatialPart v i = 0)
    (h_w_nonzero_spatial : ∃ i, spatialPart w i ≠ 0)
    (h_prop : ∀ i, spatialPart v i = r * spatialPart w i) :
    r = 0 := by
  rcases h_w_nonzero_spatial with ⟨j, h_wj_nonzero⟩
  have h_zero_eq : 0 = r * spatialPart w j := by
    rw [← h_v_spatial_zero j, h_prop j]
  exact eq_zero_of_mul_eq_zero_right (Eq.symm h_zero_eq) h_wj_nonzero

/-- When timelike vectors have parallel spatial components, their spatial norms
    are related by the square of the proportionality constant -/
@[simp]
lemma spatial_norm_relation_of_parallel {d : ℕ} {v w : Vector d}
    (h_spatial_parallel : ∃ (r : ℝ), ∀ i, spatialPart v i = r * spatialPart w i) :
      ∃ r,
          ∑ x : Fin d, spatialPart v x * spatialPart v x = r ^ 2 * ∑ x :
            Fin d, spatialPart w x * spatialPart w x ∧
            ∀ (i : Fin d), spatialPart v i = r * spatialPart w i:= by
  rcases h_spatial_parallel with ⟨r, hr⟩
  exists r
  constructor
  · -- Prove the spatial norm relationship
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
    calc ∑ i, spatialPart v i * spatialPart v i
      = ∑ i, (r * spatialPart w i) * (r * spatialPart w i) := by
          simp_rw [hr]
      _ = ∑ i, r^2 * (spatialPart w i * spatialPart w i) := by
          apply Finset.sum_congr rfl; intro i _; ring
      _ = r^2 * ∑ i, spatialPart w i * spatialPart w i := by
          rw [Finset.mul_sum]
  · exact hr

/-- For timelike vectors, their time components must satisfy specific relationships
    to maintain the timelike character -/
@[simp]
lemma timelike_time_space_constraint {d : ℕ} {v : Vector d}
    (hv : causalCharacter v = .timeLike) :
    ∑ x : Fin d, spatialPart v x * spatialPart v x < timeComponent v ^ 2 := by
  rw [timeLike_iff_norm_sq_pos] at hv
  rw [innerProduct_toCoord] at hv
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  simp only [pow_two]
  have h_time : timeComponent v = v (Sum.inl 0) := rfl
  simp [h_time]
  have h_norm_pos : v (Sum.inl 0) * v (Sum.inl 0) - ∑ i, v (Sum.inr i) * v (Sum.inr i) > 0 := hv
  exact lt_of_sub_pos h_norm_pos

/-- For two non-zero real numbers with positive product,
    either both are positive or both are negative -/
@[simp]
protected lemma real_same_sign_of_pos_product {a b : ℝ}
    (ha : a ≠ 0) (hb : b ≠ 0) (h_prod : a * b > 0) :
    (a > 0 ∧ b > 0) ∨ (a < 0 ∧ b < 0) := by
  by_cases ha_pos : a > 0
  · by_cases hb_pos : b > 0
    · left; exact ⟨ha_pos, hb_pos⟩
    · -- a positive, b not positive
      have hb_neg : b < 0 := by
        exact lt_of_le_of_ne (le_of_not_gt hb_pos) (hb)
      have h_prod_neg : a * b < 0 := mul_neg_of_pos_of_neg ha_pos hb_neg
      exact absurd h_prod_neg (not_lt_of_gt h_prod)
  · -- a not positive
    have ha_neg : a < 0 := by
      exact lt_of_le_of_ne (le_of_not_gt ha_pos) (ha)
    by_cases hb_pos : b > 0
    · -- a negative, b positive - contradiction
      have h_prod_neg : a * b < 0 := mul_neg_of_neg_of_pos ha_neg hb_pos
      exact absurd h_prod_neg (not_lt_of_gt h_prod)
    · -- both negative
      have hb_neg : b < 0 := by
        exact lt_of_le_of_ne (le_of_not_gt hb_pos) (hb)
      right; exact ⟨ha_neg, hb_neg⟩

/-- When timelike vectors have opposite sign time components,
    the time component squared terms have a specific relationship -/
@[simp]
lemma timelike_opposite_sign_time_squared_relation {d : ℕ} {v w : Vector d}
    (hv : causalCharacter v = .timeLike)
    (hw : causalCharacter w = .timeLike) :
    (timeComponent v)^2 * (timeComponent w)^2 > 0 := by
  have h_v_nonzero : timeComponent v ≠ 0 := timelike_nonzero_time_component hv
  have h_w_nonzero : timeComponent w ≠ 0 := timelike_nonzero_time_component hw
  exact mul_pos (pow_two_pos_of_ne_zero h_v_nonzero) (pow_two_pos_of_ne_zero h_w_nonzero)

/-- For spatial norms related by a proportionality constant,
    the relationship extends to inner products with time components -/
@[simp]
lemma spatial_norm_and_time_product_relation {d : ℕ} {v w : Vector d} {r : ℝ}
    (h_spatial_prop : ∀ i, spatialPart v i = r * spatialPart w i) :
    ∑ x : Fin d, spatialPart v x * spatialPart v x = r^2 * ⟪spatialPart w, spatialPart w⟫_ℝ := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  calc ∑ i, spatialPart v i * spatialPart v i
    = ∑ i, (r * spatialPart w i) * (r * spatialPart w i) := by simp_rw [h_spatial_prop]
    _ = ∑ i, r^2 * (spatialPart w i * spatialPart w i) := by
        apply Finset.sum_congr rfl; intro i _; ring
    _ = r^2 * ∑ i, spatialPart w i * spatialPart w i := by rw [Finset.mul_sum]

/-- For timelike vectors with proportional spatial parts, time components
    must satisfy certain inequality relationships -/
@[simp]
lemma timelike_spatial_proportional_time_constraints {d : ℕ} {v w : Vector d} {r : ℝ}
    (hv : causalCharacter v = .timeLike)
    (hw : causalCharacter w = .timeLike)
    (h_spatial_prop : ∀ i, spatialPart v i = r * spatialPart w i) :
    (timeComponent v)^2 > r^2 * ∑ x : Fin d, spatialPart w x * spatialPart w x ∧
    (timeComponent w)^2 > ∑ x : Fin d, spatialPart w x * spatialPart w x := by
  constructor
  · have h_v_constraint := timelike_time_exceeds_space hv
    have h_norm_rel := spatial_norm_and_time_product_relation h_spatial_prop
    exact lt_of_eq_of_lt (id (Eq.symm h_norm_rel)) h_v_constraint
  · exact timelike_time_exceeds_space hw

/-- For timelike vectors with opposite sign time components, their causal character
    imposes constraints on how their time components relate -/
@[simp]
lemma timelike_opposite_sign_causality_constraint {d : ℕ} {v w : Vector d}
    (hv : causalCharacter v = .timeLike)
    (hw : causalCharacter w = .timeLike) :
    ∃ (k : ℝ), k > 0 ∧ (timeComponent v)^2 < k * (timeComponent w)^2 := by
  have h_v_time_nonzero : timeComponent v ≠ 0 := timelike_nonzero_time_component hv
  have h_w_time_nonzero : timeComponent w ≠ 0 := timelike_nonzero_time_component hw
  have h_v_time_sq_pos : (timeComponent v)^2 > 0 := pow_two_pos_of_ne_zero h_v_time_nonzero
  have h_w_time_sq_pos : (timeComponent w)^2 > 0 := pow_two_pos_of_ne_zero h_w_time_nonzero
  let k := (timeComponent v)^2 / (timeComponent w)^2 + 1
  have h_k_pos : k > 0 := by
    apply add_pos
    · apply div_pos
      · exact h_v_time_sq_pos
      · exact h_w_time_sq_pos
    · exact zero_lt_one
  have h_ineq : (timeComponent v)^2 < k * (timeComponent w)^2 := by
    have h_nonzero : (timeComponent w)^2 ≠ 0 := by
      exact pow_ne_zero 2 h_w_time_nonzero
    have h1 : ((timeComponent v)^2 / (timeComponent w)^2 + 1) * (timeComponent w)^2 =
              (timeComponent v)^2 + (timeComponent w)^2 := by
      rw [add_mul]
      have h_cancel : (timeComponent v)^2 / (timeComponent w)^2 *
                      (timeComponent w)^2 = (timeComponent v)^2 := by
        exact div_mul_cancel₀ (timeComponent v ^ 2) h_nonzero
      rw [h_cancel, one_mul]
    rw [h1]
    exact lt_add_of_pos_right (timeComponent v ^ 2) h_w_time_sq_pos
  exists k

/-- For purely temporal timelike vectors, the causal character is completely
    determined by the sign of the time component -/
@[simp]
lemma purely_temporal_timelike_characterization {d : ℕ} {v : Vector d}
    (h_spatial_zero : ∀ i, spatialPart v i = 0) :
    0 < ⟪v, v⟫ₘ ↔ timeComponent v ≠ 0 := by
  rw [innerProduct_toCoord]
  have h_spatial_sum_zero : ∑ i, v (Sum.inr i) * v (Sum.inr i) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [← spatialPart, h_spatial_zero i, mul_zero]
  rw [h_spatial_sum_zero]
  simp only [Fin.isValue, sub_zero, pow_two]
  exact mul_self_pos

/-- If the squares of two real numbers are equal, their absolute values are equal -/
@[simp]
protected lemma abs_eq_abs_of_squared_time_eq {a b : ℝ}
    (h_sq : a^2 = b^2) (hb : b ≠ 0) : |a| = |b| := by
  have h3 : a^2 = |a|^2 := by simp [sq_abs]
  have h4 : b^2 = |b|^2 := by simp [sq_abs]
  rw [h3, h4] at h_sq
  have ha_pos : |a| ≥ 0 := abs_nonneg a
  have hb_pos : |b| > 0 := abs_pos.2 hb
  have h_sq_mul : |a| * |a| = |b| * |b| := by rw [pow_two, pow_two] at h_sq; exact h_sq
  exact (mul_self_inj ha_pos (le_of_lt hb_pos)).mp h_sq_mul

/-- For purely temporal timelike vectors, their Minkowski norm equals the squared time component -/
@[simp]
lemma purely_temporal_norm_eq_time_squared {d : ℕ} {v : Vector d}
    (h_spatial_zero : ∀ i, spatialPart v i = 0) :
    ⟪v, v⟫ₘ = (timeComponent v)^2 := by
  rw [innerProduct_toCoord]
  have h_spatial_sum_zero : ∑ i, v (Sum.inr i) * v (Sum.inr i) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [← spatialPart, h_spatial_zero i, mul_zero]
  rw [h_spatial_sum_zero]
  simp [pow_two]
  exact rfl
