import Mathlib.Order.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Tactic
import Mathlib.Algebra.Order.Module.Pointwise


/-- A function f : α → ℝ is submodular if f(a ⊔ b) + f(a ⊓ b) ≤ f(a) + f(b). -/
def IsSubmodular {α : Type*} [Lattice α] (f : α → ℝ) : Prop :=
  ∀ a b : α, f (a ⊔ b) + f (a ⊓ b) ≤ f a + f b

structure SubmodularFunction (α : Type*) where
  (toFun : Set α → ℝ)
  (submodular : IsSubmodular toFun)
  (map_empty : toFun ∅ = 0)

variable {E : Type*} [Fintype E] [DecidableEq E]

instance : CoeFun (SubmodularFunction E) (λ _ => Set E → ℝ) :=
  ⟨λ f => f.toFun⟩

variable {α : Type*} [Lattice α]

/-- If f and g are submodular, so is f + g -/
lemma IsSubmodular.add {f g : α → ℝ} (hf : IsSubmodular f) (hg : IsSubmodular g) :
    IsSubmodular (f + g) := by
  intro a b
  simp only [Pi.add_apply]
  linarith [hf a b, hg a b]

/-- if f is submodular and c ∈ ℝ≥0, then c ⬝ f is also submodular -/
lemma IsSubmodular.smul {f : α → ℝ} (hf : IsSubmodular f) {c : ℝ} (hc : 0 ≤ c) :
    IsSubmodular (c • f) := by
  intro a b
  simp only [Pi.smul_apply, smul_eq_mul]
  have h := hf a b
  nlinarith

lemma IsSubmodular.compl {f : Finset E → ℝ} (hf : IsSubmodular f) :
    IsSubmodular (λ A => f (Finset.univ \ A)) := by
  intro A B
  simp only
  rw [← Finset.compl_eq_univ_sdiff, ← Finset.compl_eq_univ_sdiff, ← Finset.compl_eq_univ_sdiff, ← Finset.compl_eq_univ_sdiff]
  rw [compl_sup, compl_inf, add_comm]
  exact hf (Aᶜ) (Bᶜ)

lemma isSubmodular_additive (w : E → ℝ) :
    IsSubmodular (λ A : Finset E => ∑ a ∈ A, w a) := by
  intro A B
  simp only
  rw [Finset.sup_eq_union, Finset.inf_eq_inter, Finset.sum_union_inter]

lemma IsSubmodular.restriction (A : α) (hf : IsSubmodular f) :
    IsSubmodular (λ (S : Set.Iic A) => f S.val) := by
    intro S T; simp; exact hf S T


def IsMonotone (f : Set E → ℝ) : Prop := ∀ ⦃A B⦄, A ⊆ B → f A ≤ f B

structure Polymatroid (E : Type*) where
  f : Set E → ℝ
  submod : IsSubmodular f
  monotone : IsMonotone f
  normalized : f ∅ = 0

/-- The marginal gain of adding element `i` to set `A`. -/
def marginalGain (f : Finset E → ℝ) (i : E) (A : Finset E) : ℝ :=
  f (insert i A) - f A

open Pointwise

lemma insert_i_A_inter_B_eq_B_if_i_nin_B  (A B : Finset E) (hAB : A ⊆ B) (hi : i ∉ B) :
  insert i A ∩ B = B := by
    ext x

lemma diminishing_imp_submodular (f : Finset E → ℝ)
    (h_dim : ∀ A B : Finset E, A ⊆ B → ∀ i : E, i ∉ B →
      f (insert i A) - f A ≥ f (insert i B) - f B) :
    IsSubmodular f := by
  intro A B
  rw [Finset.sup_eq_union, Finset.inf_eq_inter]
  suffices f (B ∪ A) - f B ≤ f A - f (B ∩ A) by
    rw [Finset.union_comm] at this; simp; sorry

  let D := A \ B
  have hD : D = A \ B := by rfl
  have h_union : B ∪ A = B ∪ D := by
    rw [← Finset.union_sdiff_self_eq_union, hD]
  have h_inter : B ∩ A = A \ D := by
    ext x; simp [D]; tauto

  rw [h_union, h_inter]
  clear h_union h_inter

  induction D using Finset.induction_on with
  | empty =>
      simp
  | insert hi hs =>
      
      -- Rewrite current goal using the inductive step
      -- f(B ∪ (s ∪ {i})) - f(B) ≤ f((A\s\i) ∪ (s ∪ {i})) - f(A\s\i)
      -- This part usually requires telescope summation or
      -- applying h_dim to the "top" element i.
      rename_i _ _ i s 
      have h1 : f (insert i (B ∪ s)) - f (B ∪ s) ≤ f (insert i (B ∩ A ∪ s)) - f (B ∩ A ∪ s) := by
        apply h_dim
        · -- B ∩ A ∪ s ⊆ B ∪ s
          intro x; simp; tauto
        · -- i ∉ B ∪ s
          simp at hi; simp [hi]; intro hb;
          -- i is from A \ B, so i cannot be in B
          have : i ∈ A \ B := by sorry -- follows from D definition
          simp at this; tauto
      simp
      


lemma isSubmodular_iff_diminishing (f : Finset E → ℝ):
  IsSubmodular f ↔ ∀ A B : Finset E, A ⊆ B → ∀ i : E, i ∉ B → marginalGain f i A ≥ marginalGain f i B := by
  constructor
  .
    intro h A B hAB i hiB
    specialize h (insert i A) B
    have h_inf : (insert i A) ⊓ B = A := by
      rw [Finset.inf_eq_inter]
      ext x
      simp only [Finset.mem_inter, Finset.mem_insert]
      constructor
      . rintro ⟨(rfl|hxA),hxB⟩
        . contradiction
        . exact hxA
      . intro hxA
        exact ⟨Or.inr hxA, hAB hxA⟩
    have h_sup : (insert i A) ⊔ B = insert i B := by
      rw [Finset.sup_eq_union]
      ext x
      simp only [Finset.mem_union, Finset.mem_insert]
      tauto
    unfold marginalGain
    rw [h_inf, h_sup] at h
    linarith
  . intro h_dim A B
