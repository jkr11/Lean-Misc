import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Set.SymmDiff
import Mathlib.Tactic.Ring
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Adjoint

open BigOperators Finset
open scoped symmDiff
open RealInnerProductSpace
open InnerProductSpace
open LinearMap

variable {n : ℕ}

/-!
# Chapter 1: Fourier Analysis of Boolean Functions (O'Donnell)

This file is arranged to mirror the order of definitions and results
in Ryan O'Donnell's *Analysis of Boolean Functions*.
-/

abbrev Cube (n : ℕ) : Type := (Fin n -> ZMod 2)

def HammingCube (n : ℕ) := {x : Fin n → ℝ // ∀ i, x i = 1 ∨ x i = -1}

abbrev BooleanFunc (n : ℕ) : Type := Cube n → ℝ

instance : Pow (BooleanFunc n) ℕ := Pi.instPow

variable {f : BooleanFunc n}


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

lemma chi_add_one (b : ZMod 2) :
  χ (b + 1) = - χ (b) := by
  match h : b with
  | 0 => simp [chi_repr]; unfold chi_base_alt; simp [ZMod.val]
  | 1 =>
    have h_true : (1 : ZMod 2) + 1 = 0 := by rfl
    rw [h_true]
    unfold χ
    simp

lemma χ_sq (b : ZMod 2) : (χ b) * (χ b) = 1 := by
  fin_cases b <;> simp [χ]

-- Definition 1.2
def chi (S : Finset (Fin n) ) : BooleanFunc n :=
  fun x => ∏ i ∈ S, χ (x i)

abbrev χₛ (S : Finset (Fin n)) : BooleanFunc n :=
  chi S

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

lemma chi_add' (S : Finset (Fin n)) (x y : Cube n) :
  χₛ S (x + y) = χₛ S x * χₛ S y := by
  unfold χₛ
  simp [chi_add]


-- definition 1.3
noncomputable
def inner_product (f g : BooleanFunc n) : ℝ :=
  (∑ x : Cube n, (f x * g x)) / 2^n

noncomputable
def expectation : BooleanFunc n →ₗ[ℝ] ℝ where
  toFun f := (∑ x, f x) / 2^n
  map_add' f g := by
    simp [Finset.sum_add_distrib]
    ring
  map_smul' c f := by
    field_simp
    rw [Finset.mul_sum]

lemma inpr_eq_expectation (f g : BooleanFunc n) :
  inner_product f g = expectation (fun x => f x * g x) := by
  unfold inner_product
  unfold expectation
  simp

lemma char_split (x : Cube n) (S : Finset (Fin n)) (i : Fin n) (hi : i ∈ S) :
  χₛ S x = χ (x i) * χₛ (S.erase i) x := by
  unfold χₛ chi
  rw [mul_comm, ← Finset.prod_erase_mul]
  exact hi

noncomputable instance : InnerProductSpace.Core ℝ (BooleanFunc n) where
  inner := fun f g => inner_product f g
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
  add_left := by
    unfold inner_product
    field_simp
    simp_rw [add_mul, Finset.sum_add_distrib]
    simp
  smul_left := by
    unfold inner_product
    simp_rw [starRingEnd_apply, star_trivial]
    field_simp
    simp_rw [Finset.mul_sum]
    ring
    simp
  definite := by
    unfold inner_product
    field_simp
    simp_rw [← sq]
    intro x
    sorry -- because of nonneg but cant find theorem rn

noncomputable instance : NormedAddCommGroup (BooleanFunc n) :=
  instCoreRealBooleanFunc.toNormedAddCommGroup


noncomputable instance : SeminormedAddCommGroup (BooleanFunc n) :=
  instNormedAddCommGroupBooleanFunc.toSeminormedAddCommGroup


noncomputable instance : InnerProductSpace ℝ (BooleanFunc n) :=
  InnerProductSpace.ofCore instCoreRealBooleanFunc

noncomputable
instance : Norm (BooleanFunc n) := InnerProductSpace.Core.toNorm (𝕜 := ℝ) (F := BooleanFunc n)

notation "𝐄" => expectation

lemma expectation_chi_empty :
  𝐄 (chi (∅ : Finset (Fin n))) = 1 := by
  unfold chi expectation
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
  rw [← mul_assoc, symmDiff_def S T, inter_comm, ←Finset.prod_mul_distrib, Finset.prod_congr rfl (fun i _ => χ_sq (x i))]
  simp
  rw [prod_union]
  apply disjoint_sdiff_sdiff

lemma expectation_chi_eq_zero {S : Finset (Fin n)} (hS : S.Nonempty) :
    expectation (χₛ S) = 0 := by
  unfold expectation
  simp
  obtain ⟨j, hj⟩ := hS

  let f : Cube n ≃ Cube n := Equiv.addLeft (Pi.single j 1)

  have h_neg : ∀ x, χₛ S (f x) = - χₛ S x := by
    intro x
    unfold χₛ f
    simp [f, Pi.single_apply, ← Finset.prod_erase_mul S _ hj, chi]
    rw [add_comm, chi_add_one, mul_neg]
    have h_prod_eq : (∏ i in S.erase j, χ ((if i = j then 1 else 0) + x i)) = ∏ i in S.erase j, χ (x i) := by
      apply Finset.prod_congr rfl
      intro i hi
      have hij : i ≠ j := Finset.ne_of_mem_erase hi
      rw [if_neg hij, zero_add]
    rw [h_prod_eq]
  have h_sum := f.sum_comp (λ x => χₛ S x)
  simp [h_neg] at h_sum
  linarith [h_neg]

lemma expectation_apply (f : BooleanFunc n) :
    𝐄 f = (∑ x, f x) / 2^n := rfl

theorem chi_orthonormal : Orthonormal ℝ (fun S : Finset (Fin n) => chi S) := by
  rw [orthonormal_iff_ite]
  intro S T
  have h_inner : inner (chi S) (chi T) = inner_product (chi S) (chi T) := by
    rfl
  rw [h_inner, inner_product]
  rw [Finset.sum_congr rfl (fun i _ => chi_mul_chi S T _)]
  split_ifs with h
  . subst h; simp [symmDiff_self]; rw [← expectation_apply]; simp_rw [expectation_chi_empty]
  . apply expectation_chi_eq_zero
    rwa [symmDiff_nonempty]


-- Prop 1.8 part 1
noncomputable
def fourier_coeff' (f : BooleanFunc n) (S : Finset (Fin n)) : ℝ :=
  ⟪f,χₛ S⟫

noncomputable
def fourier_coeff (S : Finset (Fin n)) : BooleanFunc n →ₗ[ℝ] ℝ where
  toFun f := ⟪f, χₛ S⟫
  map_add' f g := by
    rw [inner_add_left]
  map_smul' c f := by
    rw [inner_smul_left]
    simp

theorem fourier_expansion (f : BooleanFunc n) :
  f = ∑ S, fourier_coeff S f • chi S := by
  sorry

noncomputable
def fourier_transform' (f : BooleanFunc n) : BooleanFunc n :=
  ∑ S, fourier_coeff S f • χₛ S

noncomputable
def fourier_transform : BooleanFunc n →ₗ[ℝ] BooleanFunc n where
  toFun f := fourier_transform' f
  map_add' := by sorry
  map_smul' := by sorry

lemma inner_eq_expect (f g : BooleanFunc n) :
   ⟪f, g⟫ = 𝐄 (f * g) := rfl


theorem plancherel (f g : BooleanFunc n) :
  ⟪f, g⟫ = ∑ S, fourier_coeff S f * fourier_coeff S g := by
  conv_lhs =>
    rw [fourier_expansion f, fourier_expansion g]
  simp_rw [inner_sum, sum_inner, inner_smul_left, inner_smul_right]
  simp only [starRingEnd_apply, star_trivial]
  simp_rw [orthonormal_iff_ite.mp chi_orthonormal]
  simp [ite_mul]

theorem plancherel' (f g : BooleanFunc n) :
    𝐄 (f * g) = ∑ S, fourier_coeff S f * fourier_coeff S g := by
    rw [← inner_eq_expect]
    simp [plancherel]


theorem parseval (f : BooleanFunc n) :
  ⟪f, f⟫ = ∑ S, (fourier_coeff S f)^2 := by
  simp [plancherel]
  simp_rw [← sq]

theorem parseval' (f : BooleanFunc n) :
  𝐄 (f ^ 2) = ∑ S, (fourier_coeff S f)^2 := by
  rw [pow_two]
  simp [plancherel']
  simp_rw [← sq]

-- most basic probability notion, maybe this is bad because we need instances?
noncomputable def Prob (P : Cube n → Prop) [DecidablePred P] : ℝ :=
  (Finset.univ.filter P).card / (Fintype.card (Cube n) : ℝ)

-- def 1.10
noncomputable
def hamming_dist (f g : Cube n → ZMod 2) :=
  Prob (fun x => f x ≠ g x)


-- fact 1.12
lemma expectation_f_eq_fourier_coeff_emptyset (f : BooleanFunc n) : 𝐄 f = fourier_coeff ∅ f := by
  rw [← mul_one f];
  rw [← inner_eq_expect]
  rw [fourier_coeff]
  unfold χₛ
  simp -- make chi empty lemma
  rfl

lemma inner_eq_expect_left (f : BooleanFunc n) :
  ⟪f, 1⟫ = 𝐄 f := by
  conv_rhs =>
    rw [← mul_one f]
  rw [← inner_eq_expect]

lemma inner_eq_expect_right (f : BooleanFunc n) :
  ⟪1, f⟫ = 𝐄 f := by
  rw [← inner_conj_symm]
  simp only [starRingEnd_apply, star_trivial]
  simp [inner_eq_expect_left]

instance : Sub (BooleanFunc n) := Pi.instSub

noncomputable
abbrev Var (f : BooleanFunc n) : ℝ :=
  𝐄 ((f - fun _ => 𝐄 f) ^ 2)

noncomputable
abbrev Var' (f : BooleanFunc n) : ℝ :=
  ⟪f- λ _ => 𝐄 f,f - λ _ => 𝐄 f⟫


noncomputable
abbrev Cov (f g : BooleanFunc n) : ℝ :=
  𝐄 (f * g) - 𝐄 f * 𝐄 g

noncomputable
abbrev Var'' (f : BooleanFunc n) : ℝ :=
  Cov f f -- TODO figure out a system for this

lemma var_eq_var' (f : BooleanFunc n) :
  Var f =  Var' f := by
  unfold Var Var'
  rw [inner_eq_expect, ← sq]

lemma expectation_const (c : ℝ) : 𝐄 ((fun _ ↦ c) : BooleanFunc n) = c := by
  unfold expectation
  simp

lemma cov_eq_nonempty_fourier_sum (f g : BooleanFunc n) :
  Cov f g = ∑ S ∈ univ \ {∅}, (fourier_coeff S f) * (fourier_coeff S g) := by
  simp
  unfold Cov
  rw [plancherel']; simp
  simp_rw [expectation_f_eq_fourier_coeff_emptyset]

lemma variance_eq_expect_sq_sub_sq_expect (f : BooleanFunc n) :
    Var f = 𝐄 (f^2) - (𝐄 f)^2 := by
  unfold Var
  rw [← inner_eq_expect_left, inner_eq_expect, mul_one]
  simp_rw [sub_sq]
  simp
  rw [mul_assoc]
  have h : (2 * (f * λ x ↦ 𝐄 f)) = (2 * 𝐄 f) • f := by -- TODO mae this nicer
    ext x
    simp [mul_assoc]
    ring
  rw [h, map_smul 𝐄]
  conv_lhs =>
    enter [2]
    rw [sq]
  simp_rw [Pi.mul_def]
  rw [expectation_const]
  rw [← sq]
  rw [smul_eq_mul]
  ring

lemma variance_eq_nonempty_fourier_sum (f : BooleanFunc n) :
  Var f = ∑ S ∈ univ \ {∅}, (fourier_coeff S f) ^ 2 := by
  rw [variance_eq_expect_sq_sub_sq_expect]
  simp
  rw [parseval', expectation_f_eq_fourier_coeff_emptyset]

noncomputable def weight (f : BooleanFunc n) (k : ℕ) : ℝ :=
  ∑ S : Finset (Fin n), if S.card = k then (fourier_coeff S f) ^ 2 else 0

notation "𝐖" k "[" f "]" => weight f k

noncomputable def degree_part (f : BooleanFunc n) (k : ℕ) : BooleanFunc n :=
  ∑ S : Finset (Fin n), if S.card = k then (fourier_coeff S f) • (chi S) else 0

lemma weight_eq_degree_part_norm (f : BooleanFunc n) (k : ℕ) :
  weight f k = ‖degree_part f k‖^2 := by
  unfold weight
  sorry

-- Section: densities and probability under a density
structure Density (n : ℕ) where
  phi : BooleanFunc n
  nonneg : ∀ x, 0 ≤ phi x
  norm : 𝐄 phi = 1

noncomputable def prob_under_density (n : ℕ) (d : Density n) (P : Cube n → Prop) [DecidablePred P] : ℝ :=
  𝐄 (fun x => if P x then d.phi x else 0)

theorem expectation_density (d : Density n) (f : BooleanFunc n) :
    -- This is often how we define the left hand side:
    𝐄 (fun x => f x * d.phi x) = ⟪f, d.phi⟫ := by
  unfold inner
  rfl



lemma expectation_equiv {n : ℕ} (e : Cube n ≃ Cube n) (f : BooleanFunc n) :
    𝐄 (fun x ↦ f (e x)) = 𝐄 f := by
  unfold expectation
  simp
  rw [Finset.sum_equiv e]
  all_goals simp


noncomputable def convolution (f g : BooleanFunc n) : BooleanFunc n :=
  fun x => 𝐄 (fun y => f y * g (x + y))

infixr:70 " ∗ " => convolution

@[simp]
lemma cube_add_self (x : Cube n) : x + x = 0 := by
  ext i
  simp [Pi.add_apply]
  rw [ZModModule.add_self]

-- Notation for convenience


theorem convolution_comm (f g : BooleanFunc n) : f ∗ g = g ∗ f := by
  ext x
  unfold convolution
  simp_rw [mul_comm (f _)]
  let e := Equiv.addLeft x
  rw [← expectation_equiv e]
  simp [e]
  simp_rw [← add_assoc, cube_add_self, zero_add]

lemma expectation_expectation {n : ℕ} (f : Cube n → Cube n → ℝ) :
    𝐄 (fun y ↦ 𝐄 (fun z ↦ f y z)) = 1 / (Fintype.card (Cube n) * Fintype.card (Cube n)) * ∑ y, ∑ z, f y z := by
  unfold expectation
  simp_rw [Finset.mul_sum]
  field_simp
  rw [Finset.sum_mul]
  simp_rw [← Finset.sum_div]
  field_simp [pow_ne_zero n (two_ne_zero : (2 : ℝ) ≠ 0)]
  simp_rw [← Finset.sum_div]
  rw [div_mul]
  field_simp
  rw [Finset.sum_mul] -- Why is this so complicated?


lemma expectation_swap {n : ℕ} (f : Cube n → Cube n → ℝ) :
    𝐄 (fun y => 𝐄 (fun z => f y z)) =
      𝐄 (fun z => 𝐄 (fun y => f y z)) := by
  classical
  have h1 := (expectation_expectation (f := f) : _)
  have h2 := (expectation_expectation (f := fun z y => f y z) : _)
  have hcomm : (∑ y : Cube n, ∑ z : Cube n, f y z) =
                (∑ z : Cube n, ∑ y : Cube n, f y z) := by
    simpa using (Finset.sum_comm : ∑ y : Cube n, ∑ z : Cube n, f y z = _)
  calc
    𝐄 (fun y => 𝐄 (fun z => f y z))
        = 1 / (Fintype.card (Cube n) * Fintype.card (Cube n)) *
            ∑ y, ∑ z, f y z := h1
    _ = 1 / (Fintype.card (Cube n) * Fintype.card (Cube n)) *
            ∑ z, ∑ y, f y z := by simp [hcomm]
    _ = 𝐄 (fun z => 𝐄 (fun y => f y z)) := by
          simp [h2]

lemma convolution_assoc (f g h : BooleanFunc n) : (f ∗ g) ∗ h = f ∗ (g ∗ h) := by
  sorry

lemma expectation_expectation_product {n : ℕ} (f : Cube n → Cube n → ℝ) (g : Cube n → ℝ) :
    (𝐄 fun x ↦ (𝐄 fun y ↦ f x y) * g x) = 𝐄 fun x ↦ 𝐄 fun y ↦ f x y * g x := by
  unfold expectation
  simp
  simp_rw [Finset.sum_div]
  field_simp
  simp_rw [← Finset.sum_div]
  field_simp
  simp_rw [← Finset.sum_div]
  field_simp
  rw [mul_assoc]
  field_simp
  simp_rw [← Finset.sum_mul]

lemma expectation_comm {n : ℕ} (f : Cube n → Cube n → ℝ) :
    (𝐄 fun x ↦ 𝐄 fun y ↦ f x y) = 𝐄 fun y ↦ 𝐄 fun x ↦ f x y := by
  unfold expectation; simp
  simp_rw [← Finset.sum_div, Finset.sum_div]
  rw [Finset.sum_comm]

lemma expectation_mul_separate {n : ℕ} (A B : Cube n → ℝ) :
    (𝐄 fun y ↦ 𝐄 fun x ↦ A y * B x) = (𝐄 A) * (𝐄 B) := by
  simp_rw [← smul_eq_mul]
  conv_lhs =>
    enter [2, y]
  have h_smul : ∀ y, (fun x ↦ A y • B x) = (A y) • B := by
    simp
    intro y
    ext x
    simp
  simp_rw [h_smul]
  conv_lhs =>
    enter [2, y]
    rw [map_smul 𝐄 (A y) B]
  simp
  sorry


-- TODO: simplify
lemma fourier_coeff_conv {S} : fourier_coeff S (f ∗ g) = fourier_coeff S f * fourier_coeff S g := by
  unfold fourier_coeff
  simp_rw [inner_eq_expect]; simp; unfold convolution
  change 𝐄 (fun x ↦ (𝐄 fun y ↦ f y * g (x + y)) * χₛ S x) = _ -- TODO
  rw [expectation_expectation_product, expectation_comm];
  conv_lhs =>
    enter [2]
    ext y
    rw [← expectation_equiv (Equiv.addRight y)]
    simp;
  simp_rw [add_assoc]; simp
  conv_lhs =>
    enter [2]
    ext y
    enter [2]
    ext x
    rw [chi_add', mul_assoc, mul_comm, ← mul_assoc, mul_assoc, mul_comm]
  simp_rw [← Pi.mul_apply]
  simp_rw [← expectation_mul_separate]
  simp_rw [mul_comm (χₛ S) f]




-- Chapter 2: Influences and derivations
-- def 2.25

def update_bit (x : Cube n) (i : Fin n) (b : ZMod 2) : Cube n :=
  fun j => if j = i then b else x j

lemma update_bit_same {b : ZMod 2} {x : Cube n} {i : Fin n} (h : x i = b) :
  update_bit x i b = x := by
  ext j; by_cases hj : j = i <;> simp [update_bit, hj, h]

def flip_bit (i : Fin n) (x : Cube n) : Cube n :=
  update_bit x i (1 - x i)

noncomputable
def Ddo (i : Fin n): BooleanFunc n →ₗ[ℝ] BooleanFunc n where
  toFun f := fun x => (f (update_bit x i 0) - f (update_bit x i 1)) / 2
  map_add' f g  := by
    ext x; simp [sub_add_sub_comm]; ring
  map_smul' c f := by
    ext x; simp [mul_sub]; ring

@[simp]
private lemma char_update_member (x : Cube n) (S : Finset (Fin n)) (i : Fin n) (hi : i ∈ S) (b : ZMod 2) :
    χₛ S (update_bit x i b) = χ b * χₛ (S.erase i) x := by
  rw [char_split (update_bit x i b) S i hi]
  congr 1
  . simp [update_bit]
  . unfold χₛ chi; simp [update_bit]; apply Finset.prod_congr rfl;
    intro x_1 hx_1
    have hne : x_1 ≠ i := Finset.ne_of_mem_erase hx_1
    rw [if_neg hne]

@[simp]
private lemma char_update_non_member (x : Cube n) (S : Finset (Fin n)) (i : Fin n) (hi : i ∉ S) (b : ZMod 2) :
    chi S (update_bit x i b) = chi S x := by
  unfold chi
  apply Finset.prod_congr rfl
  intro j hj
  have hne : j ≠ i := by
    intro h_eq
    rw [h_eq] at hj
    exact hi hj
  simp [update_bit, hne]

-- We can reasonably do this in one probably
lemma char_update (x : Cube n) (S : Finset (Fin n)) (i : Fin n) (b : ZMod 2) :
  chi S (update_bit x i b) = if i ∈ S then χ b * chi (S.erase i) x else chi S x := by
  split_ifs with h
  . simp [char_update_member _ _ _ h]
  . simp [char_update_non_member _ _ _ h]

lemma ddo_char (i : Fin n) (S : Finset (Fin n)) :
  Ddo i (chi S) = if i ∈ S then χₛ (S.erase i) else 0 := by
  funext
  simp [Ddo]
  simp [char_update, char_update, χ]
  split_ifs with hi <;> simp

lemma Ddo_eq_fourier_sum {i} :
  Ddo i f = ∑ S ∈ (univ : Finset (Fin n)).powerset.filter (fun S => i ∈ S), (fourier_coeff S f) • χₛ (S.erase i) := by
  simp
  rw [fourier_expansion f]
  rw [map_sum]
  simp_rw [map_smul, ddo_char]
  simp
  sorry

noncomputable
def expect_i (i : Fin n) (f : BooleanFunc n) : BooleanFunc n :=
  fun x => (f (update_bit x i 0) + f (update_bit x i 1)) / 2

lemma expect_i_linear (i : Fin n) : IsLinearMap ℝ (expect_i i) := by
  constructor
  · intros f g; ext x; unfold expect_i; simp; ring
  · intros c f; ext x; unfold expect_i; simp; ring

noncomputable
def Ei (i : Fin n) : BooleanFunc n →ₗ[ℝ] BooleanFunc n where
  toFun f := fun x => (f (update_bit x i 0) + f (update_bit x i 1)) / 2
  map_add' f g := by
    ext x; simp; ring
  map_smul' c f := by
    ext x; simp; ring



theorem decomposition (i : Fin n) (f : BooleanFunc n) (x : Cube n) :
    f x = (χ (x i)) * (Ddo i f x) + (Ei i f x) := by
  unfold Ddo Ei
  field_simp
  rw [mul_sub]
  let val := x i
  match h: x i with
  | 0 =>
      simp [χ, update_bit_same h]
      ring
  | 1 =>
      simp [χ, update_bit_same h]
      ring

noncomputable def Li (i : Fin n) : BooleanFunc n →ₗ[ℝ] BooleanFunc n where
  toFun f := fun x => f x - Ei i f x
  map_add' f g := by sorry
  map_smul' c f := by sorry

-- alternate definition
noncomputable
def Li' (i : Fin n) (f : BooleanFunc n) : BooleanFunc n :=
  fun x => (f x - f (flip_bit i x)) / 2

lemma Li_eq_chi_mul_Di (i : Fin n) (f : Cube n → ℝ) (x : Cube n) :
    Li i f x = χ (x i) * Ddo i f x := by
  unfold Li Ddo
  match h : x i with
  | 0 =>
    simp [h, χ]
    unfold Ei
    simp [update_bit_same h]
    ring
  | 1 =>
    simp [h, χ]
    unfold Ei
    simp [update_bit_same h]
    ring



lemma update_bit_idempotent (b : ZMod 2) (i : Fin n) (x : Cube n) :
  update_bit (update_bit x i b) i b = update_bit x i b := by
  unfold update_bit
  ext j
  simp
  intro h
  simp [h]

theorem Li_idempotent (i : Fin n) (f : BooleanFunc n) :
    Li i (Li i f) = Li i f := by
  ext x
  unfold Li
  simp
  unfold Ei
  match h : x i with
  | 0 =>
    simp [update_bit_same h]
    ring
    simp [update_bit_idempotent]
    ring
    unfold update_bit
    conv_lhs =>
      enter [2]
      enter [1]
      enter [1]
      ext j
      simp
    sorry
  | 1 => sorry
  /- flip_bit
  match h : x i with
  | 0 =>
    simp [h, update_bit_same h]
    unfold update_bit
    simp
    ring
    sorry
  | 1 =>
    sorry -/

lemma star_Li (i : Fin n) :
  star (Li i) = Li i := by
  ext f
  unfold Li
  simp
  sorry


lemma Li_self_adjoint (i : Fin n) : IsSelfAdjoint (Li i) := by
  rw [isSelfAdjoint_iff]
  sorry





def pivotal {α : Type*} [DecidableEq α] (f : Cube n → α) (i : Fin n) (x : Cube n) : Prop :=
  f x ≠ f (flip_bit i x)

noncomputable
instance (f : Cube n → ℝ) (i : Fin n) : DecidablePred (pivotal f i) :=
  fun x => inferInstanceAs (Decidable (f x ≠ f (flip_bit i x)))

--noncomputable def influence (i : Fin n) (f : Cube n → ℝ) : ℝ :=
--  (∑ x, if f x ≠ f (flip_bit i x) then (1 : ℝ) else 0) / (Fintype.card (Cube n))

noncomputable def influence (i : Fin n) (f : BooleanFunc n) : ℝ :=
  𝐄 ((Ddo i f) ^ 2)

--noncomputable def influence' (i : Fin n) (f : BooleanFunc n) : ℝ :=
--  ∑ S ∈ (univ : Finset (Fin n)).powerset.filter (fun S => i ∈ S), (fourier_coeff f S) ^ 2

notation "Inf" i "[" f "]" => influence i f

lemma influence_eq_prob_pivotal (i : Fin n) (f : Cube n → ℝ) :
    influence i f = Prob (pivotal f i) := by
  unfold influence Prob
  simp
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  simp [pivotal]
  unfold expectation
  field_simp
  unfold Ddo; simp
  sorry

lemma norm_sq_eq_inner : ‖f‖ ^ 2 = ⟪f, f⟫ := by
  rw [← RCLike.re_to_real (x := ⟪f, f⟫), ← InnerProductSpace.norm_sq_eq_inner]

lemma influence_eq_norm_ddo_sq :
  influence i f = ‖Ddo i f‖ ^ 2 := by
  rw [norm_sq_eq_inner]
  unfold influence
  rw [inner_eq_expect]
  ring_nf


lemma inner_prod_li_eq_infi :
  ⟪f, Li i f⟫ = influence i f := by
  unfold influence
  rw [← Li_idempotent]
  sorry

lemma influence_eq_fourier_sum :
  influence i f = ∑ S ∈ (univ : Finset (Fin n)).powerset.filter (fun S => i ∈ S), (fourier_coeff S f) ^ 2 := by
  rw [influence_eq_norm_ddo_sq]
  rw [norm_sq_eq_inner]
  rw [parseval]
  rw [Ddo_eq_fourier_sum]
  simp
  simp_rw [pow_two]
  simp_rw [mul_sum]
  sorry

noncomputable
abbrev total_influence (f : BooleanFunc n) : ℝ :=
  ∑ i, influence i f

notation "𝐈[" f "]" => total_influence f

lemma total_inf_eq_expectation_of_sum_Di_sq :
  𝐈[f] = 𝐄 (∑ i, (Ddo i f) ^ 2) := by
  simp [total_influence]
  simp_rw [influence_eq_norm_ddo_sq, norm_sq_eq_inner, inner_eq_expect, ← sq]

noncomputable
def Dgo : BooleanFunc n →ₗ[ℝ] (Cube n → EuclideanSpace ℝ (Fin n)) where
  toFun f := fun x => fun j => Ddo j f x
  map_add' f g := by sorry
  map_smul' c f := by sorry

notation "∇"f => Dgo f

-- prop 2.35
lemma total_inf_eq_expextation_of_norm_sq_of_gradient :
  𝐈[f] = 𝐄 (fun x => ‖((∇ f) x : EuclideanSpace ℝ (Fin n))‖ ^ 2) := by
  rw [total_inf_eq_expectation_of_sum_Di_sq, map_sum]
  simp_rw [← inner_eq_expect_left, ← sum_inner]
  congr 1
  ext y
  simp [Dgo]
  simp_rw [PiLp.norm_sq_eq_of_L2, Real.norm_eq_abs, sq_abs]


noncomputable
def Laplacian : BooleanFunc n →ₗ[ℝ] BooleanFunc n := {
  toFun f := fun x => ∑ i, Li i f x
  map_add' f g := by
    ext x
    simp [Finset.sum_add_distrib]
  map_smul' c f := by
    ext x
    simp [Finset.mul_sum]
}

variable {f g : BooleanFunc n}

lemma total_inf_eq_fourier_sum :
  𝐈[f] = ∑ S, #S * (fourier_coeff S f) ^ 2 := by
  unfold total_influence
  simp_rw [influence_eq_fourier_sum, Finset.sum_filter]
  rw [Finset.sum_comm]
  simp

lemma inner_prod_laplacian_eq_total_inf :
  ⟪f, Laplacian f⟫ = 𝐈[f] := by
  unfold Laplacian total_influence
  simp
  simp_rw [← Finset.sum_apply]
  simp
  have h_lift : (fun x ↦ ∑ c, (Li c) f x) = ∑ c, Li c f := by
    ext x
    simp
  simp_rw [h_lift, inner_sum, inner_prod_li_eq_infi]

lemma total_inf_eq_fourier_weight_sum :
  𝐈[f] = ∑ k : (Fin n), k * weight f k := by
  rw [total_inf_eq_fourier_sum]
  unfold weight



-- Poincare inequality
theorem var_leq_total_inf :
  Var f ≤ 𝐈[f] := by
  sorry


noncomputable
def ProbPair (P : Cube n × Cube n → Prop) [DecidablePred P] : ℝ :=
  (Finset.univ.filter P).card / (Fintype.card (Cube n × Cube n) : ℝ)

noncomputable def expectation_gen {α : Type*} [Fintype α] (g : α → ℝ) : ℝ :=
  (∑ x, g x) / (Fintype.card α : ℝ)

/-- The "Noise Weight" between two strings based on their correlation ρ -/
def noise_weight (ρ : ℝ) (x y : Cube n) : ℝ :=
  ∏ i, if y i = x i then (1 + ρ) else (1 - ρ)

noncomputable def Stab (ρ : ℝ) (f : BooleanFunc n) : ℝ :=
  expectation_gen (fun (pair : Cube n × Cube n) =>
    let (x, y) := pair
    (noise_weight ρ x y) * f x * f y
  )

noncomputable def noise_sensitivity (δ : ℝ) (f : BooleanFunc n) : ℝ :=
  (1/2 : ℝ) - (1/2 : ℝ) * Stab (1 - 2 * δ) f

noncomputable
def bit_weight (ρ : ℝ) (xi yi : ZMod 2) : ℝ :=
  if yi = xi then (1 + ρ) / 2 else (1 - ρ) / 2

noncomputable def T (ρ : ℝ) (f : BooleanFunc n) : BooleanFunc n :=
  fun x => ∑ y, (∏ i, bit_weight ρ (x i) (y i)) * f y


-- # Chapter 3 Spectral structure and learning

def f_plus_z (z : Cube n) : BooleanFunc n :=
  fun x => f (x + z)

-- Fact 3.25


-- def 3.28
def is_eps_concentrated (F : Finset (Finset (Fin n))) (f : BooleanFunc n) (ε : ℝ) : Prop :=
  ∑ S in (Finset.univ.filter fun S => S ∈ F), (fourier_coeff S f) ^ 2 ≤ ε
