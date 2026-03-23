import Mathlib.Data.Real.Basic
import Mathlib.Data.List.Sort
import Mathlib

open Finset BigOperators Matrix ENNReal

noncomputable section

variable {α : Type*} [DecidableEq α] [LinearOrder α] [AddCommMonoid α]

/-- x↓: The decreasing rearrangement using the order dual -/
def dec_rearrangement (x : Fin n → α) : Fin n → α :=
  let σ := Tuple.sort (OrderDual.toDual ∘ x)
  x ∘ σ

/-- x↑: The increasing rearrangement -/
def inc_rearrangement (x : Fin n → α) : Fin n → α :=
  let σ := Tuple.sort x
  x ∘ σ

def my_vec : Fin 5 → ℤ := ![3, 1, 4, 1, 5]

#eval List.ofFn (dec_rearrangement my_vec) -- Expected: [5, 4, 3, 1, 1]
#eval List.ofFn (inc_rearrangement my_vec) -- Expected: [1, 1, 3, 4, 5]

example (x : Fin n → ℤ) : Monotone (inc_rearrangement x) :=
  Tuple.monotone_sort x

example (x : Fin n → ℤ) : Antitone (dec_rearrangement x) :=
  Tuple.monotone_sort (OrderDual.toDual ∘ x)

notation:max x "↓" => dec_rearrangement x
notation:max x "↑" => inc_rearrangement x

--example (x : Fin n → ℝ) : ∑ i, dec_rearrangement' x i = ∑ i, x i :=
--  Fintype.sum_equiv (Tuple.sort (OrderDual.toDual ∘ x)) _ _ (λ _ => rfl)

omit [DecidableEq α] in
theorem sum_inc_rearrangement (x : Fin n → α) :
    ∑ i, inc_rearrangement x i = ∑ i, x i := by
  let σ := Tuple.sort x
  change ∑ i, x (σ i) = ∑ i, x i
  simp [Fintype.sum_equiv σ]

omit [DecidableEq α] in
theorem sum_dec_rearrangement (x : Fin n → α) :
    ∑ i, dec_rearrangement x i = ∑ i, x i := by
  let σ := Tuple.sort (OrderDual.toDual ∘ x)
  change ∑ i, x (σ i) = ∑ i, x i
  simp [Fintype.sum_equiv σ]

omit [DecidableEq α] in
lemma sum_inc_eq_sum_dec {n} (x : Fin n → α) :
    ∑ i, x↓ i = ∑ i, x↑ i := by
  rw [sum_inc_rearrangement, sum_dec_rearrangement]

omit [DecidableEq α] [AddCommMonoid α] in
lemma dec_rearrangement_eq_inc_rev (x : Fin n → α) (i : Fin n) :
    dec_rearrangement x i = inc_rearrangement x (Fin.rev i) := by
  set σ : Fin n ≃ Fin n := Tuple.sort (OrderDual.toDual ∘ x)
  set τ : Fin n ≃ Fin n := Tuple.sort x;
  set rev_perm : Equiv.Perm (Fin n) := Equiv.ofBijective Fin.rev ⟨Fin.rev_injective, Fin.rev_surjective⟩;
  have h_unique : x ∘ (σ * rev_perm) = x ∘ τ := by
    apply_rules [ Tuple.unique_monotone ];
    · intro i j hij;
      have := Tuple.monotone_sort ( OrderDual.toDual ∘ x ) ( Fin.rev_le_rev.mpr hij ) ; aesop;
    · exact Tuple.monotone_sort x;
  replace h_unique := congr_fun h_unique ( Fin.rev i ) ; aesop;

lemma h_split_sum {k : Fin n} (x : (Fin n → α)) : ∑ i, inc_rearrangement x i = ∑ i ∈ Finset.univ.filter (fun i => i.val < n - k.val), inc_rearrangement x i + ∑ i ∈ Finset.univ.filter (fun i => i.val ≥ n - k.val), inc_rearrangement x i := by
  sorry

/-- dec_rearrangement of a constant function is constant -/
lemma dec_rearrangement_const {n : ℕ} (c : ℝ) :
    dec_rearrangement (fun (_ : Fin n) => c) = fun _ => c := by
  ext i; simp [dec_rearrangement]

/-- dec_rearrangement is antitone -/
lemma dec_rearrangement_antitone {n : ℕ} (x : Fin n → ℝ) :
    Antitone (dec_rearrangement x) :=
  Tuple.monotone_sort (OrderDual.toDual ∘ x)

lemma dec_rearrangement_perm {n : ℕ} (x : Fin n → ℝ) :
    ∀ i, ∃ j, dec_rearrangement x j = x i := by
  intro i
  obtain ⟨j, hj⟩ : ∃ j : Fin n, (dec_rearrangement x) j = x i := by
    have h_sigma_perm : ∃ σ : Equiv.Perm (Fin n), ∀ j, (dec_rearrangement x) j = x (σ j) := by
      unfold dec_rearrangement; aesop;
    exact ⟨ h_sigma_perm.choose.symm i, by simpa using h_sigma_perm.choose_spec ( h_sigma_perm.choose.symm i ) ⟩
  use j

lemma dec_rearrangement_head_ge {n : ℕ} [NeZero n] (x : Fin n → ℝ) :
    ∀ i, x i ≤ dec_rearrangement x ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩ := by
  intro i
  obtain ⟨j, hj⟩ := dec_rearrangement_perm x i
  exact hj ▸ dec_rearrangement_antitone x ( Nat.zero_le _ )

lemma dec_inc_complement (x : Fin n → ℝ) (k : Fin n) :
    (∑ i : Fin k, (x↓) ⟨i.val, by omega⟩) +
    (∑ i : Fin (n - k) , (x↑) ⟨i.val, by omega⟩) = ∑ i, x i := by
  obtain ⟨σ, hσ⟩ : ∃ σ : Fin n ≃ Fin n, dec_rearrangement x = x ∘ σ := by
    aesop
  have h_inv : ∑ i ∈ Finset.univ.filter (fun i => i.val < k.val), dec_rearrangement x i + ∑ i ∈ Finset.univ.filter (fun i => i.val < n - k.val), inc_rearrangement x i = ∑ i, x i := by
    have h_split_sum : ∑ i, inc_rearrangement x i = ∑ i ∈ Finset.univ.filter (fun i => i.val < n - k.val), inc_rearrangement x i + ∑ i ∈ Finset.univ.filter (fun i => i.val ≥ n - k.val), inc_rearrangement x i := by
      rw [ Finset.sum_filter, Finset.sum_filter ];
      simpa only [ ← Finset.sum_add_distrib ] using Finset.sum_congr rfl fun i _ => by split_ifs <;> linarith;
    have h_rev_sum : ∑ i ∈ Finset.univ.filter (fun i => i.val ≥ n - k.val), inc_rearrangement x i = ∑ i ∈ Finset.univ.filter (fun i => i.val < k.val), dec_rearrangement x i := by
      apply Finset.sum_bij (fun i hi => Fin.rev i);
      · grind;
      · grind;
      · simp at *;
        grind;
      · simp [ dec_rearrangement_eq_inc_rev ];
    linarith [ sum_inc_rearrangement x ];
  convert h_inv using 1;
  refine' congrArg₂ ( · + · ) _ _;
  · refine' Finset.sum_bij ( fun i hi => ⟨ i, by linarith [ Fin.is_lt i, Fin.is_lt k ] ⟩ ) _ _ _ _ <;> simp [ Fin.ext_iff ];
    · exact fun a => Nat.lt_of_le_of_lt ( Nat.le_refl _ ) a.2;
    · exact fun b hb => ⟨ ⟨ b, by linarith [ Fin.is_lt b, Fin.is_lt k, show ( b : ℕ ) < k from hb ] ⟩, rfl ⟩;
  · refine' Finset.sum_bij ( fun i hi => ⟨ i, by omega ⟩ ) _ _ _ _ <;> simp +decide [ Fin.ext_iff ];
    exact fun b hb => ⟨ ⟨ b, by linarith [ Fin.is_lt b, Nat.sub_le n k ] ⟩, rfl ⟩

omit [DecidableEq α] [AddCommMonoid α] in
lemma inc_rearrangement_sorted (x : Fin n → α) :
    ∀ i j : Fin n, i ≤ j → inc_rearrangement x i ≤ inc_rearrangement x j := by
  intros i j hij
  simp only [inc_rearrangement] at *
  have h_sorted : List.Pairwise (fun a b => decide (a ≤ b)) (List.mergeSort (List.ofFn x) (fun a b => decide (a ≤ b))) := by
    convert List.pairwise_mergeSort _ _ _ using 1
    · grind
    · exact fun a b => by cases le_total a b <;> simp [*]
  generalize_proofs at *
  have := List.pairwise_iff_get.mp h_sorted
  simp_all
  cases lt_or_eq_of_le hij
  · sorry
  · simp [*]

omit [DecidableEq α] [AddCommMonoid α] in
/-- The first element of the increasing rearrangement is the minimum -/
lemma inc_rearrangement_first_le {n : ℕ} (x : Fin n → α) (h : 0 < n) (i : Fin n) :
    inc_rearrangement x ⟨0, h⟩ ≤ x i := by
  have h_perm : List.Perm (List.ofFn (inc_rearrangement x)) (List.ofFn x) :=
    sorry
  obtain ⟨j, hj⟩ : ∃ j : Fin n, inc_rearrangement x j = x i := by
    have := h_perm.symm.subset (List.mem_ofFn.mpr ⟨i, rfl⟩); aesop
  exact hj ▸ inc_rearrangement_sorted x ⟨0, h⟩ j (Nat.zero_le _)

def dec_sorting_matrix [One α] (x : Fin n → α) : Matrix (Fin n) (Fin n) α :=
  let σ := Tuple.sort (OrderDual.toDual ∘ x)
  Equiv.Perm.permMatrix α σ

def inc_sorting_matrix [One α] (x : Fin n → α) : Matrix (Fin n) (Fin n) α :=
  Equiv.Perm.permMatrix α (Tuple.sort x)

-- Example vector: [10, 30, 20]
def example_v : Fin 3 → ℕ := ![10, 30, 20]

-- The matrix that reorders [10, 30, 20] into [30, 20, 10]
#eval dec_sorting_matrix example_v

lemma row_sums_of_total_sum {n : ℕ} {P : Matrix (Fin n) (Fin n) ℝ}
    (h : ∀ y : Fin n → ℝ, ∑ i, (y ᵥ* P) i = ∑ i, y i) :
    ∀ j : Fin n, ∑ i, P j i = 1 := by
  intro j; specialize h (Pi.single j 1); aesop

--lemma vecMul_doublyStochastic_sum {n : ℕ} {P : Matrix (Fin n) (Fin n) ℝ}
--    (hP : P ∈ doublyStochastic ℝ (Fin n)) (y : Fin n → ℝ) :
--    ∑ i, (y ᵥ* P) i = ∑ i, y i := by
--  simp_rw [vecMul, dotProduct]
--  rw [Finset.sum_comm]
--  simp only [mem_doublyStochastic_iff_sum] at hP
--  simp only [← Finset.mul_sum _ _ _, hP.2.1, mul_one]

structure Majorizes {n : ℕ} (x y : Fin n → ℝ) : Prop where
  partial_sums : ∀ k : Fin n,
    ∑ i ∈ Finset.univ.filter (· ≤ k), (dec_rearrangement x) i ≤
    ∑ i ∈ Finset.univ.filter (· ≤ k), (dec_rearrangement y) i
  total_sum : ∑ i, x i = ∑ i, y i

infix:50 " ≺ " => Majorizes

structure majorizes_dec {n : ℕ} (x y : Fin n → ℝ) : Prop where
  partial_sums : ∀ k : Fin n,
    ∑ i ∈ Finset.univ.filter (· ≤ k), (inc_rearrangement x) i ≥
    ∑ i ∈ Finset.univ.filter (· ≤ k), (inc_rearrangement y) i
  total_sum : ∑ i, x i = ∑ i, y i

set_option trace.linarith true
lemma majorize_dec_eq_inc {x y : Fin n → ℝ} :
  x ≺ y ↔ majorizes_dec x y := by
  constructor
  · rintro ⟨h1, h2⟩
    refine' ⟨ fun k => _, h2 ⟩;
    by_cases hk: k.val = 0
    . sorry
    . have := dec_inc_complement x k; have := dec_inc_complement y k; simp_all
      have h4 := h1 ⟨ n-k , by omega⟩
      sorry
  . rintro ⟨hdec, hsum⟩
    refine' ⟨fun k => _, hsum⟩
    by_cases hk: k.val = 0
    . sorry
    . have h3 := dec_inc_complement y k; have h4 := dec_inc_complement x k; -- simp_all
      have h5 := hdec ⟨n-k, by omega⟩
      sorry

def schur_convex (φ : (Fin n → ℝ) → ℝ) : Prop :=
  ∀ x y, x ≺ y → φ x ≤ φ y

structure weakly_log_majorizes (x y : Fin n → ℝ≥0∞) : Prop where
  partial_prod : (∀ k : Fin n, (∏ i : Fin k, (x↓) ⟨i.val, by omega⟩) ≤ (∏ i : Fin k, (y↓) ⟨i.val, by omega⟩))

infix:50 " ≺ʷₗ " => weakly_log_majorizes

structure log_majorizes (x y : Fin n → ℝ≥0∞) : Prop extends weakly_log_majorizes x y  where
  total_prod : ∏ i : Fin n, (x↓) i = ∏ i : Fin n, (y↓) i

infix:50 " ≺ₗ " => log_majorizes

def e (n : ℕ) : Fin n → ℝ := fun _ => 1

lemma nonneg_of_majorizes {n : ℕ} {P : Matrix (Fin n) (Fin n) ℝ}
    (h : ∀ y : Fin n → ℝ, (y ᵥ* P) ≺ y) :
    ∀ i j : Fin n, 0 ≤ P i j := by
  intro i j;
  sorry

lemma le_one_of_majorized_by_ones {n : ℕ} [NeZero n] {z : Fin n → ℝ} (h : z ≺ e n) :
    ∀ i, z i ≤ 1 := by
  intro i;
  have h_sum : (dec_rearrangement z) ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩ ≤ 1 := by
    have := h.partial_sums ⟨ 0, Nat.pos_of_ne_zero ( NeZero.ne n ) ⟩;
    convert this using 1;
    · rw [ Finset.sum_eq_single_of_mem _ ] <;> aesop;
    · erw [ Finset.sum_eq_single ⟨ 0, Nat.pos_of_ne_zero ( NeZero.ne n ) ⟩ ] <;> aesop;
  exact le_trans ( dec_rearrangement_head_ge z i ) h_sum

theorem majorized_by_ones_eq {n : ℕ} [NeZero n] {z : Fin n → ℝ} (h : z ≺ e n) :
    z = e n := by
  have h_sum_eq : ∑ i, z i = n := by
    simpa using h.total_sum.trans ( by simp [ e ] );
  contrapose! h_sum_eq with h_sum_eq;
  exact ne_of_lt ( lt_of_lt_of_le ( Finset.sum_lt_sum ( fun i _ => le_one_of_majorized_by_ones h i ) ⟨ Classical.choose $ Function.ne_iff.mp h_sum_eq, Finset.mem_univ _, lt_of_le_of_ne ( le_one_of_majorized_by_ones h _ ) ( Classical.choose_spec $ Function.ne_iff.mp h_sum_eq ) ⟩ ) <| by norm_num )

lemma min_le_min_of_majorizes {n : ℕ} [NeZero n] (j : Fin n) {x y : Fin n → ℝ} (h : x ≺ y) :
  x↑ 0 ≤ y↑ 0 := by sorry

lemma max_le_max_of_majorizes (n : ℕ) [NeZero n] (x y : Fin n → ℝ) (h : x ≺ y) :
  x↓ 0 ≤ y↓ 0 := by sorry


lemma nonneg_of_dec_min_nonneg {n : ℕ} {x : Fin n → ℝ}
    (h : ∀ i, 0 ≤ dec_rearrangement x i) : ∀ i, 0 ≤ x i := by
  intro i; exact (by
  obtain ⟨j, hj⟩ : ∃ j, dec_rearrangement x j = x i := by
    exact dec_rearrangement_perm x i;
  exact hj ▸ h j);

def y := ![8,7,3,4]
#eval (Finset.univ.image y).max

lemma majorizes_implies_doubly_stochastic [NeZero n] (P : Matrix (Fin n) (Fin n) ℝ) (hM : ∀ (y : Fin n → ℝ), (y ᵥ* P) ≺ y) :
  P ∈ doublyStochastic ℝ (Fin n) := by
  have hMe := hM (e n)
  have h_eq : e n ᵥ* P = e n := majorized_by_ones_eq hMe
  let i : Fin n := ⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩
  have h_ei := hM (Pi.single i (1 : ℝ))
  rw [Matrix.single_vecMul] at h_ei
  simp at h_ei
  have h_ei_sum := h_ei.2
  simp at h_ei_sum
  simp_all
  sorry

/-- Theorem A.4: P is doubly stochastic iff yP ≺ y for all y -/
theorem doubly_stochastic_iff_majorizes {P : Matrix (Fin n) (Fin n) ℝ} :
  ∀ (y : Fin n → ℝ), (y ᵥ* P) ≺ y ↔ P ∈ doublyStochastic ℝ (Fin n) := by
  sorry

def t_transform {n} [DecidableEq n] (i j : n) (w : ℝ) : Matrix n n ℝ :=
  let Q := (Equiv.swap i j).toPEquiv.toMatrix
  w • (1 : Matrix n n ℝ) + (1 - w) • Q

lemma t_matrix_doubly_stochastic  (i j : Fin n) {w : ℝ} (hw : 0 ≤ w) (hw1 : w ≤ 1) :
    t_transform i j w ∈ doublyStochastic ℝ (Fin n) := by
  constructor
  · -- Part 1: Non-negativity
    intro a b
    simp [t_transform]
    sorry
  . simp [t_transform]
    simp_rw [vecMul_eq_sum]
    -- sum (λ I + (1-λ) Q) = λ(sum I) + (1-λ)(sum Q)
    sorry


/-- A single T-transform step: x = T y for some T-transform matrix T -/
def is_T_transform (x y : Fin n → ℝ) : Prop :=
  ∃ (i j : Fin n) (w : ℝ), 0 ≤ w ∧ w ≤ 1 ∧
    let Q := (Equiv.swap i j).toPEquiv.toMatrix
    let T := w • (1 : Matrix (Fin n) (Fin n) ℝ) + (1 - w) • Q
    x = T *ᵥ y

/-- The number of indices i where x i = y i -/
def count_equal (x y : Fin n → ℝ) : ℕ :=
  (Finset.univ.filter (fun i => x i = y i)).card

def reachable_by_T_transforms : (Fin n → ℝ) → (Fin n → ℝ) → Prop :=
  Relation.ReflTransGen is_T_transform

theorem muirhead_lemma {x y : Fin n → ℝ} :
  x ≺ y → reachable_by_T_transforms y x := by
  unfold reachable_by_T_transforms
  unfold is_T_transform
  sorry

variable {m n : ℕ}
variable (x : Fin m → (Fin n → ℝ))

theorem day_proposition_majorization :
    (∑ i, x i) ≺ (∑ i, (dec_rearrangement (x i))) := by
  sorry

/-- A.1.c. Proposition -/
lemma sum_maj_by_ordered_sum (x y : Fin n → ℝ) :
  x + y ≺ x↓ + y↓ := by
  constructor
  . sorry
  . simp_rw [Pi.add_apply, Finset.sum_add_distrib, sum_dec_rearrangement]
