/-
Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import PhysLean.Mathematics.SpecialFunctions.PhyscisistsHermite
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import PhysLean.Mathematics.SpecialFunctions.PhyscisistsHermite
import Mathlib.Analysis.Convolution
/-!

# Hilbert space for one dimension quantum mechanics

-/

namespace QuantumMechanics

namespace OneDimension
noncomputable section
/-- The Hilbert space in 1d corresponding to square integbrable (equivalence classes)
  of functions. -/
noncomputable abbrev HilbertSpace := MeasureTheory.Lp (α := ℝ) ℂ 2

namespace HilbertSpace

lemma mem_iff {f : ℝ →ₘ[MeasureTheory.volume] ℂ} : f ∈ HilbertSpace
    ↔ MeasureTheory.Integrable (fun x => ‖f x‖ ^ 2) := by
  rw [HilbertSpace]
  rw [MeasureTheory.Lp.mem_Lp_iff_memℒp]
  simp [MeasureTheory.Memℒp]
  have h1 : MeasureTheory.AEStronglyMeasurable (↑f) MeasureTheory.volume := by
    exact MeasureTheory.AEEqFun.aestronglyMeasurable f
  simp [h1]
  rw [MeasureTheory.eLpNorm_lt_top_iff_lintegral_rpow_nnnorm_lt_top]
  simp [MeasureTheory.Integrable]
  have h0 : MeasureTheory.AEStronglyMeasurable
    (fun x => Complex.abs (f x) ^ 2) MeasureTheory.volume := by
    apply MeasureTheory.AEStronglyMeasurable.pow
    refine Continuous.comp_aestronglyMeasurable ?_ h1
    exact Complex.continuous_abs
  simp [h0]
  simp [MeasureTheory.HasFiniteIntegral]
  simp [enorm, nnnorm]
  exact Ne.symm (NeZero.ne' 2)
  exact ENNReal.ofNat_ne_top

open MeasureTheory

lemma aeEqFun_mk_mem_iff (f : ℝ → ℂ) (hf : AEStronglyMeasurable f volume) :
     AEEqFun.mk f hf ∈ HilbertSpace ↔ MeasureTheory.Memℒp f 2 volume := by
  rw [mem_iff, ← MeasureTheory.memℒp_two_iff_integrable_sq_norm]
  apply MeasureTheory.memℒp_congr_ae
  exact AEEqFun.coeFn_mk f hf
  exact AEEqFun.aestronglyMeasurable (AEEqFun.mk f hf)


lemma mem_iff' {f : ℝ → ℂ} (hf : MeasureTheory.AEStronglyMeasurable f MeasureTheory.volume) :
    MeasureTheory.AEEqFun.mk f hf ∈ HilbertSpace
    ↔ MeasureTheory.Integrable (fun x => ‖f x‖ ^ 2) := by
  rw [HilbertSpace]
  rw [MeasureTheory.Lp.mem_Lp_iff_memℒp]
  simp [MeasureTheory.Memℒp]
  have h1 : MeasureTheory.AEStronglyMeasurable
    (MeasureTheory.AEEqFun.mk f hf) MeasureTheory.volume := by
    apply MeasureTheory.AEEqFun.aestronglyMeasurable
  simp [h1]
  rw [MeasureTheory.eLpNorm_lt_top_iff_lintegral_rpow_nnnorm_lt_top]
  simp [MeasureTheory.Integrable]
  have h0 : MeasureTheory.AEStronglyMeasurable
    (fun x => Complex.abs (f x) ^ 2) MeasureTheory.volume := by
    apply MeasureTheory.AEStronglyMeasurable.pow
    refine Continuous.comp_aestronglyMeasurable ?_ hf
    exact Complex.continuous_abs
  simp [h0]
  simp [MeasureTheory.HasFiniteIntegral]
  simp [enorm, nnnorm]
  exact Ne.symm (NeZero.ne' 2)
  exact ENNReal.ofNat_ne_top

/-!

## Gaussians

-/
open MeasureTheory

lemma gaussian_integrable {b  : ℝ} (c : ℝ) (hb : 0 < b) :
    MeasureTheory.Integrable (fun x => (Real.exp (- b * (x - c)^ 2) : ℂ)) := by
  apply MeasureTheory.Integrable.ofReal
  have hf : (fun x => (Real.exp (-b * (x - c) ^ 2))) =
    fun y => (fun x => (Real.exp (-b * x ^ 2))) (y - c) := by
    exact rfl
  erw [hf]
  apply Integrable.comp_sub_right (f :=  (fun x => Real.exp (- b * x ^ 2)))
  exact integrable_exp_neg_mul_sq hb

lemma gaussian_aestronglyMeasurable {b : ℝ} (c : ℝ) (hb : 0 < b) :
    AEStronglyMeasurable (fun x  =>  (Real.exp (- b * (x - c) ^2) : ℂ)) volume := by
  apply MeasureTheory.Integrable.aestronglyMeasurable
  exact gaussian_integrable c hb

lemma guassian_mem_hilbertSpace  {b : ℝ} (c : ℝ) (hb : 0 < b) :
    AEEqFun.mk (fun x  => (Real.exp (- b * (x - c) ^2) : ℂ)) (gaussian_aestronglyMeasurable c hb)
    ∈ HilbertSpace := by
  rw [mem_iff']
  simp [Complex.abs_exp]
  have h1 : (fun (x : ℝ) => Real.exp (-(b * ((x - c : ℂ) ^ 2).re)) ^ 2) =
    fun y => (fun x => Real.exp (- (2 * b) * x ^ 2)) (y - c) := by
    ext x
    simp
    trans Real.exp (-(b * ((x - c: ℂ) ^ 2).re)) ^ (2 : ℝ)
    · simp
    rw [← Real.exp_mul]
    simp
    rw [← Complex.ofReal_sub, ← Complex.ofReal_pow, Complex.ofReal_re]
    ring
  rw [h1]
  apply Integrable.comp_sub_right (f := fun x => Real.exp (- (2 * b) * x ^ 2))
  apply integrable_exp_neg_mul_sq
  linarith

lemma exp_mul_gaussian_integrable  (b c : ℝ) (hb : 0 < b) :
    MeasureTheory.Integrable (fun x => Real.exp (c *  x) * Real.exp (- b * x ^ 2))  := by
  have h1 :  (fun x =>  Real.exp (c *  x) * Real.exp (- b * x ^ 2))
      = (fun x => Real.exp (c^2 /(4 * b)) * Real.exp (- b * (x - c/(2 * b)) ^ 2)) := by
    funext x
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    field_simp
    ring
  rw [h1]
  apply MeasureTheory.Integrable.const_mul
  have h1 :(fun x => Real.exp (- b * (x - c/(2 * b)) ^ 2))
      = fun y => (fun x => Real.exp (- b * x ^ 2)) (y -  c/(2 * b)) := by
    funext x
    rw [sub_sq]
    ring_nf
  rw [h1]
  apply Integrable.comp_sub_right (f :=  (fun x => Real.exp (- b * x ^ 2)))
  exact integrable_exp_neg_mul_sq hb

lemma exp_abs_mul_gaussian_integrable  (b c : ℝ) (hb : 0 < b) :
    MeasureTheory.Integrable (fun x => Real.exp (|c *  x|) * Real.exp (- b * x ^ 2))  := by
  rw [← MeasureTheory.integrableOn_univ]
  have h1 : Set.univ (α := ℝ) = (Set.Iic 0) ∪ Set.Ici 0  := by
    exact Eq.symm Set.Iic_union_Ici
  rw [h1]
  apply MeasureTheory.IntegrableOn.union
  · let g := fun x => Real.exp ((- |c|) * x) * Real.exp (- b * x ^ 2)
    rw [integrableOn_congr_fun (g := g) _ measurableSet_Iic]
    · apply MeasureTheory.IntegrableOn.left_of_union (t := Set.Ici 0 )
      rw [← h1, MeasureTheory.integrableOn_univ]
      exact exp_mul_gaussian_integrable b (- |c|) hb
    · intro x hx
      simp at hx
      simp [g]
      rw [abs_mul]
      rw [abs_of_nonpos hx]
      ring
  · let g := fun x => Real.exp (|c| * x) * Real.exp (- b * x ^ 2)
    rw [integrableOn_congr_fun (g := g) _ measurableSet_Ici]
    · apply MeasureTheory.IntegrableOn.right_of_union (s := Set.Iic 0 )
      rw [← h1, MeasureTheory.integrableOn_univ]
      exact exp_mul_gaussian_integrable b (|c|) hb
    · intro x hx
      simp at hx
      simp [g]
      rw [abs_mul]
      rw [abs_of_nonneg hx]

lemma mul_gaussian_mem_Lp_one  (f : ℝ → ℂ) (hf : AEStronglyMeasurable f volume)
    (hmem : AEEqFun.mk f hf ∈ HilbertSpace) (b c : ℝ) (hb : 0 < b) :
    MeasureTheory.Memℒp (fun x => f x * Real.exp (- b * (x - c) ^ 2)) 1 volume := by
  refine memℒp_one_iff_integrable.mpr ?_
  let g : HilbertSpace := ⟨AEEqFun.mk (fun x  => (Real.exp (- b * (x - c)^2) : ℂ))
    (gaussian_aestronglyMeasurable c hb), guassian_mem_hilbertSpace c hb⟩
  have h1 := MeasureTheory.L2.integrable_inner (𝕜 := ℂ) g ⟨(AEEqFun.mk f hf), hmem⟩
  refine (integrable_congr   ?_).mp h1
  simp
  conv_lhs =>
    enter [x]
    rw [mul_comm]
  apply Filter.EventuallyEq.mul
  · exact AEEqFun.coeFn_mk f hf
  trans (fun x => (starRingEnd ℂ) (Real.exp (- b * (x - c) ^2)))
  · apply Filter.EventuallyEq.fun_comp
    simp [g]
    exact AEEqFun.coeFn_mk _ _
  · apply Filter.EventuallyEq.of_eq
    funext x
    rw [Complex.conj_ofReal]
    simp

lemma mul_gaussian_mem_Lp_two  (f : ℝ → ℂ) (hf : AEStronglyMeasurable f volume)
    (hmem : AEEqFun.mk f hf ∈ HilbertSpace) (b c : ℝ) (hb : 0 < b) :
    MeasureTheory.Memℒp (fun x => f x * Real.exp (- b * (x - c) ^ 2)) 2 volume := by
  apply MeasureTheory.Memℒp.mul_of_top_left (p := 2)
  · apply MeasureTheory.memℒp_top_of_bound (C := Real.exp (0))
    · exact gaussian_aestronglyMeasurable c hb
    · apply Filter.Eventually.of_forall
      intro x
      simp only [neg_mul, Complex.norm_eq_abs, zero_sub, even_two, Even.neg_pow]
      rw [Complex.abs_ofReal]
      rw [abs_of_nonneg]
      · simp [Real.exp_le_exp_of_le]
        apply mul_nonneg
        · exact le_of_lt hb
        · exact sq_nonneg (x - c)
      · exact Real.exp_nonneg (-(b * (x - c) ^ 2))
  · rw [aeEqFun_mk_mem_iff] at hmem
    exact hmem

lemma abs_mul_gaussian_integrable (f : ℝ → ℂ) (hf : AEStronglyMeasurable f volume)
    (hmem : AEEqFun.mk f hf ∈ HilbertSpace) (b c : ℝ) (hb : 0 < b) :
    MeasureTheory.Integrable (fun x =>  Complex.abs (f x) * Real.exp (- b * (x - c)^2)) := by
  have h1 : (fun x => Complex.abs (f x) * Real.exp (- b * (x - c)^2)) =
      (fun x => Complex.abs (f x * Real.exp (- b *(x - c)^2))) := by
    funext x
    simp [Complex.abs_exp]
    left
    left
    rw [← Complex.ofReal_sub, ← Complex.ofReal_pow]
    rw [Complex.ofReal_re]
  rw [h1]
  have h2 : MeasureTheory.Memℒp (fun x => f x * Real.exp (- b * (x- c)^2)) 1 volume := by
    exact mul_gaussian_mem_Lp_one f hf hmem b c hb
  simpa using MeasureTheory.Memℒp.integrable_norm_rpow h2 (by simp) (by simp)

lemma exp_mul_abs_mul_gaussian_integrable  (f : ℝ → ℂ) (hf : AEStronglyMeasurable f volume)
    (hmem : AEEqFun.mk f hf ∈ HilbertSpace)
    (b c : ℝ) (hb : 0 < b) :
    MeasureTheory.Integrable (fun x => Real.exp (c *  x) * Complex.abs (f x) * Real.exp (- b * x ^ 2))  := by
  have h1 :  (fun x =>  Real.exp (c *  x) * Complex.abs (f x) * Real.exp (- b * x ^ 2))
      = (fun x => Real.exp (c^2 /(4 * b)) * (Complex.abs (f x) * Real.exp (- b * (x - c/(2 * b)) ^ 2))) := by
    funext x
    rw [mul_comm,← mul_assoc]
    trans (Real.exp (c ^ 2 / (4 * b)) * Real.exp (-b * (x - c / (2 * b)) ^ 2)) * Complex.abs (f x)
    swap
    · ring
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    field_simp
    ring
  rw [h1]
  apply MeasureTheory.Integrable.const_mul
  exact abs_mul_gaussian_integrable f hf hmem b (c / (2 * b)) hb

lemma exp_abs_mul_abs_mul_gaussian_integrable (f : ℝ → ℂ) (hf : AEStronglyMeasurable f volume)
    (hmem : AEEqFun.mk f hf ∈ HilbertSpace) (b c : ℝ) (hb : 0 < b) :
    MeasureTheory.Integrable (fun x => Real.exp (|c * x|) * Complex.abs (f x) * Real.exp (- b * x ^ 2)) := by
  rw [← MeasureTheory.integrableOn_univ]
  have h1 : Set.univ (α := ℝ) = (Set.Iic 0) ∪ Set.Ici 0  := by
    exact Eq.symm Set.Iic_union_Ici
  rw [h1]
  apply MeasureTheory.IntegrableOn.union
  · let g := fun x => Real.exp ((- |c|) * x) * Complex.abs (f x) * Real.exp (- b * x ^ 2)
    rw [integrableOn_congr_fun (g := g) _ measurableSet_Iic]
    · apply MeasureTheory.IntegrableOn.left_of_union (t := Set.Ici 0 )
      rw [← h1, MeasureTheory.integrableOn_univ]
      exact exp_mul_abs_mul_gaussian_integrable f hf hmem b (-|c|) hb
    · intro x hx
      simp at hx
      simp [g]
      left
      rw [abs_mul]
      rw [abs_of_nonpos hx]
      ring
  · let g := fun x => Real.exp (|c| * x)  * Complex.abs (f x) * Real.exp (- b * x ^ 2)
    rw [integrableOn_congr_fun (g := g) _ measurableSet_Ici]
    · apply MeasureTheory.IntegrableOn.right_of_union (s := Set.Iic 0 )
      rw [← h1, MeasureTheory.integrableOn_univ]
      exact exp_mul_abs_mul_gaussian_integrable f hf hmem b |c| hb
    · intro x hx
      simp at hx
      simp [g]
      left
      rw [abs_mul]
      rw [abs_of_nonneg hx]


end HilbertSpace
