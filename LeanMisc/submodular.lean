import Mathlib.Order.Lattice
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Convex.Basic
import Mathlib.Tactic


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
