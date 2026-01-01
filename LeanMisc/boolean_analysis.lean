import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Set.SymmDiff
import Mathlib.Tactic.Ring
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.CStarAlgebra.Basic
open BigOperators Finset
open scoped symmDiff

variable {n : ℕ}

abbrev Cube (n : ℕ) : Type := (Fin n -> ZMod 2)

def HammingCube (n : ℕ) := {x : Fin n → ℝ // ∀ i, x i = 1 ∨ x i = -1}

abbrev BooleanFunc (n : ℕ) : Type := Cube n → ℝ

variable {f : BooleanFunc n}


-- TODO: rename
/-- The encoding χ(b) = (-1)^b -/
def χ (b : ZMod 2) : ℝ := if b = 0 then 1 else -1

def chi_base_alt (b : ZMod 2) : ℝ := (-1)^(b.val)

lemma chi_repr (b : ZMod 2) :
  χ b = chi_base_alt b := by
  unfold χ chi_base_alt
  simp [ZMod.val]
  fin_cases b
  . simp
  . simp

lemma χ_sq (b : ZMod 2) : (χ b) * (χ b) = 1 := by
  fin_cases b <;> simp [χ]

-- Definition 1.2
def chi (S : Finset (Fin n) ) : BooleanFunc n :=
  fun x => ∏ i ∈ S, χ (x i)

def χₛ (S : Finset (Fin n)) : BooleanFunc n :=
  fun x => ∏ i ∈ S, χ (x i)

noncomputable def chi_alt (S : Finset (Fin n)) : BooleanFunc n :=
  fun x => (-1)^(∑ i ∈ S, (x i).val)

lemma chi_prod_eq_pow_chi_sum (S : Finset (Fin n)) :
  chi S = chi_alt S := by
  unfold chi chi_alt
  funext x
  simp [chi_repr]
  unfold chi_base_alt
  rw [Finset.prod_pow_eq_pow_sum]


-- lemma 1.5
lemma chi_add (S : Finset (Fin n)) (x y : Fin n → ZMod 2) :
    chi S (x + y) = chi S x * chi S y := by
  simp [chi, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  generalize ha : x i = a
  generalize hb : y i = b
  fin_cases a <;> fin_cases b <;> simp [χ]
  have h_true : (1 : ZMod 2) + 1 = 0 := by rfl
  intro h_true
  contradiction


-- definition 1.3
noncomputable
def inner_product (f g : BooleanFunc n) : ℝ :=
  (∑ x : Cube n, (f x * g x)) / 2^n

noncomputable
def expectation (f : BooleanFunc n) : ℝ :=
  (∑ x, f x) / 2^n

lemma inpr_eq_expectation (f g : BooleanFunc n) :
  inner_product f g = expectation (fun x => f x * g x) := by
  unfold inner_product
  unfold expectation
  simp

notation "⟨" f "," g "⟩" => inner_product f g

noncomputable instance : InnerProductSpace.Core ℝ (BooleanFunc n) where
  inner := fun f g => ⟨f,g⟩
  conj_symm := by
    simp
    unfold inner_product
    simp [mul_comm]
  nonneg_re := by
    intro x
    rw [RCLike.re_to_real]
    unfold inner_product
    apply mul_nonneg
    . apply sum_nonneg; intros y _; apply mul_self_nonneg
    . simp
  add_left := by sorry
  smul_left := by sorry
  definite := by sorry

noncomputable instance : NormedAddCommGroup (BooleanFunc n) :=
  instCoreRealBooleanFunc.toNormedAddCommGroup


noncomputable instance : SeminormedAddCommGroup (BooleanFunc n) :=
  instNormedAddCommGroupBooleanFunc.toSeminormedAddCommGroup


noncomputable instance : InnerProductSpace ℝ (BooleanFunc n) :=
  InnerProductSpace.ofCore instCoreRealBooleanFunc

notation "𝐄" => expectation

lemma expectation_chi_prod (S : Finset (Fin n)) :
    expectation (chi S) = ∏ i in S, expectation (fun x ↦ χ (x i)) := by
  unfold expectation chi
  let g : Fin n → ZMod 2 → ℝ := fun i b ↦ if i ∈ S then χ b else 1
  -- have h_distrib := Finset.sum_univ_pi (fun i ↦ (Finset.univ : Finset (ZMod 2))) g


-- Fact 1.7
lemma expectation_chi_eq_zero {S : Finset (Fin n)} (hS : S.Nonempty) :
    expectation (chi S) = 0 := by
  obtain ⟨i, hi⟩ := hS
  unfold expectation
  rw [div_eq_zero_iff]
  left
  unfold chi
  rw [← Finset.prod_univ_sum  ]


lemma expectation_chi_empty :
  expectation (chi (∅ : Finset (Fin n))) = 1 := by
  unfold chi
  simp
  unfold expectation
  simp

-- fact 1.6
theorem chi_mul_chi (S T : Finset (Fin n)) (x : Fin n → ZMod 2) :
    chi S x * chi T x = chi (S ∆ T) x := by
  unfold chi
  nth_rewrite 1 [← Finset.sdiff_union_inter S T]
  nth_rewrite 3 [← Finset.sdiff_union_inter T S]
  repeat rw [prod_union (disjoint_sdiff_inter _ _)]
  rw [mul_assoc]
  nth_rewrite 2 [← mul_assoc, mul_comm, ← mul_assoc, mul_comm]
  rw [← mul_assoc, symmDiff_def S T, inter_comm, ←Finset.prod_mul_distrib]
  rw [Finset.prod_congr rfl (fun i _ => χ_sq (x i))]
  simp
  rw [prod_union]
  apply disjoint_sdiff_sdiff

theorem chi_orthonormal : Orthonormal ℝ (fun S : Finset (Fin n) => chi S) := by
  rw [orthonormal_iff_ite]
  intro S T
  have h_inner : inner (chi S) (chi T) = inner_product (chi S) (chi T) := by
    rfl
  rw [h_inner, inner_product]
  rw [Finset.sum_congr rfl (fun i _ => chi_mul_chi S T _)]
  split_ifs with h
  . subst h; simp [symmDiff_self]; rw [← expectation, expectation_chi_empty]
  . apply expectation_chi_eq_zero
    rwa [symmDiff_nonempty]


-- Prop 1.8 part 1
noncomputable
def fourier_coeff (f : BooleanFunc n) (S : Finset (Fin n)) : ℝ :=
  ⟨f,χₛ S⟩

theorem fourier_expansion (f : BooleanFunc n) :
  f = ∑ S, fourier_coeff f S • chi S := by
  sorry

/-- The Fourier Transform for Boolean Functions -/
noncomputable def ℱ (f : Cube n → ℝ) : Finset (Fin n) → ℝ :=
  fun S ↦ ⟨χₛ S, f⟩



@[simp] lemma ft_add (f g : BooleanFunc n) : ℱ (f + g) = ℱ f + ℱ g := by
  ext; unfold ℱ; simp; sorry

theorem parseval (f : BooleanFunc n) :
  ⟨f,f⟩ = ∑ S : Finset (Fin n), (fourier_coeff f S) ^ 2 := by
  unfold inner_product; sorry
