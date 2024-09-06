/-
Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Tooby-Smith
-/
import HepLean.StandardModel.HiggsBoson.Potential
/-!

# The Two Higgs Doublet Model

The two Higgs doublet model is the standard model plus an additional Higgs doublet.

Currently this file contains the definition of the 2HDM potential.

-/

namespace TwoHDM

open StandardModel
open ComplexConjugate
open HiggsField

noncomputable section

/-! TODO: Make the potential a structure. -/
/-- The potential of the two Higgs doublet model. -/
def potential (m₁₁2 m₂₂2 𝓵₁ 𝓵₂ 𝓵₃ 𝓵₄ : ℝ)
    (m₁₂2 𝓵₅ 𝓵₆ 𝓵₇ : ℂ) (Φ1 Φ2 : HiggsField) (x : SpaceTime) : ℝ :=
  m₁₁2 * ‖Φ1‖_H ^ 2 x + m₂₂2 * ‖Φ2‖_H ^ 2 x - (m₁₂2 * ⟪Φ1, Φ2⟫_H x + conj m₁₂2 * ⟪Φ2, Φ1⟫_H x).re
  + 1/2 * 𝓵₁ * ‖Φ1‖_H ^ 2 x * ‖Φ1‖_H ^ 2 x + 1/2 * 𝓵₂ * ‖Φ2‖_H ^ 2 x * ‖Φ2‖_H ^ 2 x
  + 𝓵₃ * ‖Φ1‖_H ^ 2 x * ‖Φ2‖_H ^ 2 x
  + 𝓵₄ * ‖⟪Φ1, Φ2⟫_H x‖ ^ 2 + (1/2 * 𝓵₅ * ⟪Φ1, Φ2⟫_H x ^ 2 + 1/2 * conj 𝓵₅ * ⟪Φ2, Φ1⟫_H x ^ 2).re
  + (𝓵₆ * ‖Φ1‖_H ^ 2 x * ⟪Φ1, Φ2⟫_H x + conj 𝓵₆ * ‖Φ1‖_H ^ 2 x * ⟪Φ2, Φ1⟫_H x).re
  + (𝓵₇ * ‖Φ2‖_H ^ 2 x * ⟪Φ1, Φ2⟫_H x + conj 𝓵₇ * ‖Φ2‖_H ^ 2 x * ⟪Φ2, Φ1⟫_H x).re

namespace potential

variable (Φ1 Φ2 : HiggsField)
variable (m₁₁2 m₂₂2 𝓵₁ 𝓵₂ 𝓵₃ 𝓵₄ : ℝ)
variable (m₁₂2 𝓵₅ 𝓵₆ 𝓵₇ : ℂ)
/-!

## Simple properties of the potential

-/

/-- Swapping `Φ1` with `Φ2`, and a number of the parameters (with possible conjugation) leads
  to an identical potential. -/
lemma swap_fields :
    potential m₁₁2 m₂₂2 𝓵₁ 𝓵₂ 𝓵₃ 𝓵₄ m₁₂2 𝓵₅ 𝓵₆ 𝓵₇ Φ1 Φ2
    = potential m₂₂2 m₁₁2 𝓵₂ 𝓵₁ 𝓵₃ 𝓵₄ (conj m₁₂2) (conj 𝓵₅) (conj 𝓵₇) (conj 𝓵₆) Φ2 Φ1 := by
  funext x
  simp only [potential, HiggsField.normSq, Complex.add_re, Complex.mul_re, Complex.conj_re,
    Complex.conj_im, neg_mul, sub_neg_eq_add, one_div, Complex.norm_eq_abs, Complex.inv_re,
    Complex.re_ofNat, Complex.normSq_ofNat, div_self_mul_self', Complex.inv_im, Complex.im_ofNat,
    neg_zero, zero_div, zero_mul, sub_zero, Complex.mul_im, add_zero, mul_neg, Complex.ofReal_pow,
    RingHomCompTriple.comp_apply, RingHom.id_apply]
  ring_nf
  simp only [one_div, add_left_inj, add_right_inj, mul_eq_mul_left_iff]
  apply Or.inl
  rw [HiggsField.innerProd, HiggsField.innerProd, ← InnerProductSpace.conj_symm, Complex.abs_conj]

/-- If `Φ₂` is zero the potential reduces to the Higgs potential on `Φ₁`. -/
lemma right_zero : potential m₁₁2 m₂₂2 𝓵₁ 𝓵₂ 𝓵₃ 𝓵₄ m₁₂2 𝓵₅ 𝓵₆ 𝓵₇ Φ1 0 =
    StandardModel.HiggsField.potential (- m₁₁2) (𝓵₁/2) Φ1 := by
  funext x
  simp only [potential, normSq, ContMDiffSection.coe_zero, Pi.zero_apply, norm_zero, ne_eq,
    OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero, innerProd_right_zero,
    innerProd_left_zero, Complex.zero_re, sub_zero, one_div, Complex.ofReal_pow,
    Complex.ofReal_zero, HiggsField.potential, neg_neg, add_right_inj, mul_eq_mul_right_iff,
    pow_eq_zero_iff, norm_eq_zero, or_self_right]
  ring_nf
  simp only [true_or]

/-- If `Φ₁` is zero the potential reduces to the Higgs potential on `Φ₂`. -/
lemma left_zero : potential m₁₁2 m₂₂2 𝓵₁ 𝓵₂ 𝓵₃ 𝓵₄ m₁₂2 𝓵₅ 𝓵₆ 𝓵₇ 0 Φ2 =
    StandardModel.HiggsField.potential (- m₂₂2) (𝓵₂/2) Φ2 := by
  rw [swap_fields, right_zero]

/-- Negating `Φ₁` is equivalent to negating `m₁₂2`, `𝓵₆` and `𝓵₇`. -/
lemma neg_left : potential m₁₁2 m₂₂2 𝓵₁ 𝓵₂ 𝓵₃ 𝓵₄ m₁₂2 𝓵₅ 𝓵₆ 𝓵₇ (- Φ1) Φ2
    = potential m₁₁2 m₂₂2 𝓵₁ 𝓵₂ 𝓵₃ 𝓵₄ (- m₁₂2) 𝓵₅ (- 𝓵₆) (- 𝓵₇) Φ1 Φ2 := by
  funext x
  simp only [potential, normSq, ContMDiffSection.coe_neg, Pi.neg_apply, norm_neg,
    innerProd_neg_left, mul_neg, innerProd_neg_right, Complex.add_re, Complex.neg_re,
    Complex.mul_re, neg_sub, Complex.conj_re, Complex.conj_im, neg_mul, sub_neg_eq_add, neg_add_rev,
    one_div, Complex.norm_eq_abs, even_two, Even.neg_pow, Complex.inv_re, Complex.re_ofNat,
    Complex.normSq_ofNat, div_self_mul_self', Complex.inv_im, Complex.im_ofNat, neg_zero, zero_div,
    zero_mul, sub_zero, Complex.mul_im, add_zero, Complex.ofReal_pow, map_neg]

/-- Negating `Φ₁` is equivalent to negating `m₁₂2`, `𝓵₆` and `𝓵₇`. -/
lemma neg_right : potential m₁₁2 m₂₂2 𝓵₁ 𝓵₂ 𝓵₃ 𝓵₄ m₁₂2 𝓵₅ 𝓵₆ 𝓵₇ Φ1 (- Φ2)
    = potential m₁₁2 m₂₂2 𝓵₁ 𝓵₂ 𝓵₃ 𝓵₄ (- m₁₂2) 𝓵₅ (- 𝓵₆) (- 𝓵₇) Φ1 Φ2 := by
  rw [swap_fields, neg_left, swap_fields]
  simp only [map_neg, RingHomCompTriple.comp_apply, RingHom.id_apply]

lemma left_eq_right : potential m₁₁2 m₂₂2 𝓵₁ 𝓵₂ 𝓵₃ 𝓵₄ m₁₂2 𝓵₅ 𝓵₆ 𝓵₇ Φ1 Φ1 =
    StandardModel.HiggsField.potential (- m₁₁2 - m₂₂2 + 2 * m₁₂2.re)
    (𝓵₁/2 + 𝓵₂/2 + 𝓵₃ + 𝓵₄ + 𝓵₅.re + 2 * 𝓵₆.re + 2 * 𝓵₇.re) Φ1 := by
  funext x
  simp only [potential, normSq, innerProd_self_eq_normSq, Complex.ofReal_pow, Complex.add_re,
    Complex.mul_re, normSq_apply_re_self, normSq_apply_im_zero, mul_zero, sub_zero, Complex.conj_re,
    Complex.conj_im, one_div, norm_pow, Complex.norm_real, norm_norm, Complex.inv_re,
    Complex.re_ofNat, Complex.normSq_ofNat, div_self_mul_self', Complex.inv_im, Complex.im_ofNat,
    neg_zero, zero_div, zero_mul, Complex.mul_im, add_zero, mul_neg, neg_mul, sub_neg_eq_add,
    sub_add_add_cancel, zero_add, HiggsField.potential, neg_add_rev, neg_sub]
  ring_nf
  erw [show ((Complex.ofReal ‖Φ1 x‖) ^ 4).re = ‖Φ1 x‖ ^ 4 by
    erw [← Complex.ofReal_pow]; rfl]
  ring

lemma left_eq_neg_right : potential m₁₁2 m₂₂2 𝓵₁ 𝓵₂ 𝓵₃ 𝓵₄ m₁₂2 𝓵₅ 𝓵₆ 𝓵₇ Φ1 (- Φ1) =
    StandardModel.HiggsField.potential (- m₁₁2 - m₂₂2 - 2 * m₁₂2.re)
    (𝓵₁/2 + 𝓵₂/2 + 𝓵₃ + 𝓵₄ + 𝓵₅.re - 2 * 𝓵₆.re - 2 * 𝓵₇.re) Φ1 := by
  rw [neg_right, left_eq_right]
  simp_all only [Complex.neg_re, mul_neg]
  rfl

/-!

## Potential bounded from below

-/

/-! TODO: Prove bounded properties of the 2HDM potential.
  See e.g. https://inspirehep.net/literature/201299. -/

/-- The proposition on the coefficents for a potential to be bounded. -/
def IsBounded (m₁₁2 m₂₂2 𝓵₁ 𝓵₂ 𝓵₃ 𝓵₄ : ℝ) (m₁₂2 𝓵₅ 𝓵₆ 𝓵₇ : ℂ) : Prop :=
  ∃ c, ∀ Φ1 Φ2 x, c ≤ potential m₁₁2 m₂₂2 𝓵₁ 𝓵₂ 𝓵₃ 𝓵₄ m₁₂2 𝓵₅ 𝓵₆ 𝓵₇ Φ1 Φ2 x

lemma isBounded_right_zero {m₁₁2 m₂₂2 𝓵₁ 𝓵₂ 𝓵₃ 𝓵₄ : ℝ} {m₁₂2 𝓵₅ 𝓵₆ 𝓵₇ : ℂ}
    (h : IsBounded m₁₁2 m₂₂2 𝓵₁ 𝓵₂ 𝓵₃ 𝓵₄ m₁₂2 𝓵₅ 𝓵₆ 𝓵₇) :
    StandardModel.HiggsField.potential.IsBounded (- m₁₁2) (𝓵₁/2) := by
  obtain ⟨c, hc⟩ := h
  use c
  intro Φ x
  have hc1 := hc Φ 0 x
  rw [right_zero] at hc1
  exact hc1

lemma isBounded_left_zero {m₁₁2 m₂₂2 𝓵₁ 𝓵₂ 𝓵₃ 𝓵₄ : ℝ} {m₁₂2 𝓵₅ 𝓵₆ 𝓵₇ : ℂ}
    (h : IsBounded m₁₁2 m₂₂2 𝓵₁ 𝓵₂ 𝓵₃ 𝓵₄ m₁₂2 𝓵₅ 𝓵₆ 𝓵₇) :
    StandardModel.HiggsField.potential.IsBounded (- m₂₂2) (𝓵₂/2) := by
  obtain ⟨c, hc⟩ := h
  use c
  intro Φ x
  have hc1 := hc 0 Φ x
  rw [left_zero] at hc1
  exact hc1

lemma isBounded_𝓵₁_nonneg {m₁₁2 m₂₂2 𝓵₁ 𝓵₂ 𝓵₃ 𝓵₄ : ℝ} {m₁₂2 𝓵₅ 𝓵₆ 𝓵₇ : ℂ}
    (h : IsBounded m₁₁2 m₂₂2 𝓵₁ 𝓵₂ 𝓵₃ 𝓵₄ m₁₂2 𝓵₅ 𝓵₆ 𝓵₇) :
    0 ≤ 𝓵₁ := by
  have h1 := isBounded_right_zero h
  have h2 := StandardModel.HiggsField.potential.isBounded_𝓵_nonneg h1
  linarith

lemma isBounded_𝓵₂_nonneg {m₁₁2 m₂₂2 𝓵₁ 𝓵₂ 𝓵₃ 𝓵₄ : ℝ} {m₁₂2 𝓵₅ 𝓵₆ 𝓵₇ : ℂ}
    (h : IsBounded m₁₁2 m₂₂2 𝓵₁ 𝓵₂ 𝓵₃ 𝓵₄ m₁₂2 𝓵₅ 𝓵₆ 𝓵₇) :
    0 ≤ 𝓵₂ := by
  have h1 := isBounded_left_zero h
  have h2 := StandardModel.HiggsField.potential.isBounded_𝓵_nonneg h1
  linarith

lemma isBounded_of_left_eq_right {m₁₁2 m₂₂2 𝓵₁ 𝓵₂ 𝓵₃ 𝓵₄ : ℝ} {m₁₂2 𝓵₅ 𝓵₆ 𝓵₇ : ℂ}
    (h : IsBounded m₁₁2 m₂₂2 𝓵₁ 𝓵₂ 𝓵₃ 𝓵₄ m₁₂2 𝓵₅ 𝓵₆ 𝓵₇) :
    0 ≤ 𝓵₁/2 + 𝓵₂/2 + 𝓵₃ + 𝓵₄ + 𝓵₅.re + 2 * 𝓵₆.re + 2 * 𝓵₇.re := by
  obtain ⟨c, hc⟩ := h
  have h1 : StandardModel.HiggsField.potential.IsBounded (- m₁₁2 - m₂₂2 + 2 * m₁₂2.re)
    (𝓵₁/2 + 𝓵₂/2 + 𝓵₃ + 𝓵₄ + 𝓵₅.re + 2 * 𝓵₆.re + 2 * 𝓵₇.re) := by
    use c
    intro Φ x
    have hc1 := hc Φ Φ x
    rw [left_eq_right] at hc1
    exact hc1
  exact StandardModel.HiggsField.potential.isBounded_𝓵_nonneg h1

lemma isBounded_of_left_eq_neg_right {m₁₁2 m₂₂2 𝓵₁ 𝓵₂ 𝓵₃ 𝓵₄ : ℝ} {m₁₂2 𝓵₅ 𝓵₆ 𝓵₇ : ℂ}
    (h : IsBounded m₁₁2 m₂₂2 𝓵₁ 𝓵₂ 𝓵₃ 𝓵₄ m₁₂2 𝓵₅ 𝓵₆ 𝓵₇) :
    0 ≤ 𝓵₁/2 + 𝓵₂/2 + 𝓵₃ + 𝓵₄ + 𝓵₅.re - 2 * 𝓵₆.re - 2 * 𝓵₇.re := by
  obtain ⟨c, hc⟩ := h
  have h1 : StandardModel.HiggsField.potential.IsBounded (- m₁₁2 - m₂₂2 - 2 * m₁₂2.re)
    (𝓵₁/2 + 𝓵₂/2 + 𝓵₃ + 𝓵₄ + 𝓵₅.re - 2 * 𝓵₆.re - 2 * 𝓵₇.re) := by
    use c
    intro Φ x
    have hc1 := hc Φ (- Φ) x
    rw [left_eq_neg_right] at hc1
    exact hc1
  exact StandardModel.HiggsField.potential.isBounded_𝓵_nonneg h1

/-! TODO: Show that if the potential is bounded then `0 ≤ 𝓵₁` and `0 ≤ 𝓵₂`. -/
/-!

## Smoothness of the potential

-/

/-! TODO: Prove smoothness properties of the 2HDM potential. -/

/-!

## Invariance of the potential under gauge transformations

-/

/-! TODO: Prove invariance properties of the 2HDM potential. -/

end potential

end
end TwoHDM
