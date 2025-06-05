import Mathlib.Analysis.InnerProductSpace.Basic

import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Star.Basic

import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.CStarAlgebra.CStarMatrix

import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Basic
namespace StarAlgHomClass

variable {F A₁ A₂ : Type*} [CStarAlgebra A₁] [CStarAlgebra A₂]
  [PartialOrder A₁] [PartialOrder A₂] [StarOrderedRing A₁] [StarOrderedRing A₂]
  [FunLike F A₁ A₂] [AlgHomClass F ℂ A₁ A₂] [StarHomClass F A₁ A₂]

open CStarMatrix

class CompletelyPositiveMapClass (F : Type*) (A₁ : Type*) (A₂ : Type*)
    [CStarAlgebra A₁] [CStarAlgebra A₂] [PartialOrder A₁]
    [PartialOrder A₂] [StarOrderedRing A₁] [StarOrderedRing A₂] [FunLike F A₁ A₂] where
  map_cstarMatrix_nonneg' (φ : F) (k : ℕ) (M : CStarMatrix (Fin k) (Fin k) A₁) (hM : 0 ≤ M) :
    0 ≤ M.map φ

def IsCommutativeCStarAlgebra (A : Type*) [CStarAlgebra A] : Prop :=
  ∀ (a b : A), a * b = b * a

variable {A : Type*} [CStarAlgebra A]

lemma ex (a : A) (b : A) (h : IsCommutativeCStarAlgebra A) : a * b = b * a := by
  apply h


structure State (A : Type*) [Ring A] [StarRing A] [Algebra ℂ A] :=
  (E : A → ℂ)
  (linear : IsLinearMap ℂ E)
  (positive : ∀ a : A, 0 ≤ Complex.re (E (star a * a)))
  (normalized : E 1 = 1)

structure AlgebraicProbabilitySpace (A : Type*) [Ring A] [StarRing A] [Algebra ℂ A] :=
  (state : State A)

structure StarHom (B U : Type*) [Ring B] [Ring U] [StarRing B] [StarRing U] [Algebra ℂ B] [Algebra ℂ U] :=
  (toFun : B → U)
  (map_add : ∀ x y, toFun (x + y) = toFun x + toFun y)
  (map_mul : ∀ x y, toFun (x * y) = toFun x * toFun y)
  (map_star : ∀ x, toFun (star x) = star (toFun x))
  (map_smul : ∀ (c : ℂ) (x : B), toFun (c • x) = c • toFun x)

variable {A B : Type*} [Ring A] [Ring B] [StarRing A] [StarRing B] [Algebra ℂ A] [Algebra ℂ B]

instance : FunLike (StarHom B A) B A where
  coe := StarHom.toFun
  coe_injective' := by
    intros f g h
    cases f; cases g
    simp only at h
    congr

namespace StarHom

variable {B U : Type*} [Ring B] [Ring U] [StarRing B] [StarRing U] [Algebra ℂ B] [Algebra ℂ U]
variable (φ : StarHom B U)

@[simp]
theorem map_add_apply (x y : B) : φ (x + y) = φ x + φ y :=
  φ.map_add x y

@[simp]
theorem map_mul_apply (x y : B) : φ (x * y) = φ x * φ y :=
  φ.map_mul x y

@[simp]
theorem map_star_apply (x : B) : φ (star x) = star (φ x) :=
  φ.map_star x

@[simp]
theorem map_smul_apply (c : ℂ) (x : B) : φ (c • x) = c • φ x :=
  φ.map_smul c x

@[simp]
theorem map_zero : φ 0 = 0 := by
  rw [← (zero_smul ℂ (0 : B)), map_smul_apply, zero_smul]

@[simp]
theorem map_neg (x : B) : φ (-x) = -φ x := by
  rw [← neg_one_smul ℂ x, map_smul_apply, neg_one_smul]

@[simp]
theorem map_sub (x y : B) : φ (x - y) = φ x - φ y := by
  rw [sub_eq_add_neg, map_add_apply, map_neg, sub_eq_add_neg]

end StarHom
