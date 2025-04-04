/-
Copyright (c) 2025 Ammar Husain. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ammar Husain
-/
import PhysLean.QuantumMechanics.OneDimension.GeneralPotential.Basic
/-!

# The 1d SQM system with general super-potential

-/

open QuantumMechanics
open OneDimension
open GeneralPotential

namespace SUSYQM

/-- The two partner potentials associated to a given superpotential `W`. -/
noncomputable def Superpotential_to_Potential (ℏ : ℝ) (m : ℝ) (_hm : m > 0)
  (W : ℝ → ℝ) (_hW_x: Differentiable ℝ W) : (ℝ → ℝ) × (ℝ -> ℝ) :=
  ((fun x => ((W x)^2 + ℏ/(Real.sqrt (2*m)) * deriv W x))
  ,
  (fun x => (W x)^2 - ℏ/(Real.sqrt (2*m)) * deriv W x))

/-- A supersymmetric quantum mechanical system in 1D is specified by a three
  real parameters: the mass of the particle `m`, a value of Planck's constant `ℏ`, and
  a superpotential function `W` -/
structure GeneralSuperPotential where
  /-- The mass of the particle. -/
  m : ℝ
  /-- Reduced Planck's constant. -/
  ℏ : ℝ
  /-- The potential. -/
  W : ℝ → ℝ
  hW_x: Differentiable ℝ W
  hℏ : 0 < ℏ
  hm : 0 < m

variable (SQM : GeneralSuperPotential)

noncomputable def Q_operator (ψ : ℝ → ℂ) : ℝ → ℂ :=
  fun x => SQM.ℏ/(Real.sqrt (2*SQM.m)) * deriv ψ x + (SQM.W x)*(ψ x)
noncomputable def Q_dag_operator (ψ : ℝ → ℂ) : ℝ → ℂ :=
  fun x => -SQM.ℏ/(Real.sqrt (2*SQM.m)) * deriv ψ x + (SQM.W x)*(ψ x)

noncomputable def schroedinger1 : ((ℝ → ℂ) -> (ℝ → ℂ)) :=
  fun ψ => Q_operator SQM (Q_dag_operator SQM ψ)
noncomputable def schroedinger2 : ((ℝ → ℂ) -> (ℝ → ℂ)) :=
  fun ψ => Q_dag_operator SQM (Q_operator SQM ψ)

noncomputable def SQM_to_QM (which : Bool): GeneralPotential :=
  {
    m := SQM.m,
    ℏ := SQM.ℏ,
    V := (if which then Prod.fst else Prod.snd) (Superpotential_to_Potential SQM.ℏ SQM.m SQM.hm SQM.W SQM.hW_x),
    hℏ := SQM.hℏ,
    hm := SQM.hm
  }

TODO "Implement proof that QQ^† is the factorization of schroedinger operator with + sign potential"
theorem schroedingerFactorized1 :
  forall ψ, forall x, (schrodingerOperator (SQM_to_QM SQM True) ψ) x == (schroedinger1 SQM ψ) x:= by
  intros ψ x
  sorry

TODO "Implement proof that Q^†Q is the factorization of schroedinger operator with - sign potential"
theorem schroedingerFactorized2 :
  forall ψ, forall x, (schrodingerOperator (SQM_to_QM SQM False) ψ) x == (schroedinger2 SQM ψ) x:= by
  intros ψ x
  sorry

end SUSYQM
