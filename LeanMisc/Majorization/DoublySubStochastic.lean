import «LeanMisc».Majorization.Basic

open Finset BigOperators Matrix ENNReal

variable {n : ℕ}

/--
A square matrix is doubly substochastic iff all entries are nonnegative, and
the row sums and column sums are less than or equal to 1.
-/
def doublySubstochastic (R n : Type*) [Fintype n] [DecidableEq n] [Semiring R] [PartialOrder R]
  [IsOrderedRing R] :
    Submonoid (Matrix n n R) where
  carrier := {M | (∀ i j, 0 ≤ M i j) ∧ M *ᵥ 1 ≤ 1 ∧ 1 ᵥ* M ≤ 1}
  mul_mem' {M N} hM hN := by
    refine ⟨fun i j => sum_nonneg fun k _ => mul_nonneg (hM.1 i k) (hN.1 k j), ?_, ?_⟩
    . rw [← mulVec_mulVec]
      have h1 : M *ᵥ (N *ᵥ 1) ≤ M *ᵥ 1 := by
        intro i
        dsimp [mulVec]
        apply Finset.sum_le_sum
        intro j _
        apply mul_le_mul_of_nonneg_left (hN.2.1 j) (hM.1 i j)
      exact h1.trans hM.2.1
    . rw [← vecMul_vecMul]
      admit
  one_mem' := by
    refine ⟨fun i j => ?_, by simp, by simp⟩
    · rw [one_apply]
      split_ifs <;> simp [zero_le_one]

section MainTheorem
variable {n : ℕ} {P : Matrix (Fin n) (Fin n) ℝ}
/-- Extract nonneg, row sum ≤ 1, col sum ≤ 1 from membership in doublySubstochastic. -/
private lemma doublySubstochastic_mem (hP : P ∈ doublySubstochastic ℝ (Fin n)) :
    (∀ i j, 0 ≤ P i j) ∧ (∀ i, ∑ j, P i j ≤ 1) ∧ (∀ j, ∑ i, P i j ≤ 1) := by
  obtain ⟨hnn, hrow, hcol⟩ := hP
  refine ⟨hnn, fun i => ?_, fun j => ?_⟩
  · have := hrow i
    simp [mulVec, dotProduct] at this
    linarith
  · have := hcol j
    simp [vecMul, dotProduct] at this
    linarith

/-- Row deficiency -/
private noncomputable def rowDef (P : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) : ℝ :=
  1 - ∑ j, P i j

/-- Column deficiency -/
private noncomputable def colDef (P : Matrix (Fin n) (Fin n) ℝ) (j : Fin n) : ℝ :=
  1 - ∑ i, P i j

/-- Total deficiency -/
private noncomputable def totalDef (P : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∑ i, rowDef P i

private lemma totalDef_eq_sum_colDef (P : Matrix (Fin n) (Fin n) ℝ) :
    totalDef P = ∑ j, colDef P j := by
  simp only [totalDef, rowDef, colDef]
  simp [Finset.sum_sub_distrib, Finset.sum_comm (f := fun i j => P i j)]

private lemma rowDef_nonneg (hP : P ∈ doublySubstochastic ℝ (Fin n)) (i : Fin n) :
    0 ≤ rowDef P i := by
  have h := (doublySubstochastic_mem hP).2.1 i
  simp [rowDef]; linarith

private lemma colDef_nonneg (hP : P ∈ doublySubstochastic ℝ (Fin n)) (j : Fin n) :
    0 ≤ colDef P j := by
  have h := (doublySubstochastic_mem hP).2.2 j
  simp [colDef]; linarith

private lemma totalDef_nonneg (hP : P ∈ doublySubstochastic ℝ (Fin n)) :
    0 ≤ totalDef P :=
  Finset.sum_nonneg fun i _ => rowDef_nonneg hP i

private lemma doublyStochastic_of_totalDef_zero
    (hP : P ∈ doublySubstochastic ℝ (Fin n))
    (hS : totalDef P = 0) :
    P ∈ doublyStochastic ℝ (Fin n) := by
  have h_row : ∀ i, rowDef P i = 0 := by
    exact fun i => le_antisymm ( hS ▸ Finset.single_le_sum ( fun i _ => rowDef_nonneg hP i ) ( Finset.mem_univ i ) ) ( rowDef_nonneg hP i )
  have h_col : ∀ j, colDef P j = 0 := by
    have h_col_sum : ∑ j, colDef P j = 0 := by
      rw [ ← totalDef_eq_sum_colDef, hS ]
    have h_col_each : ∀ j, colDef P j = 0 := by
      exact fun j => le_antisymm ( h_col_sum ▸ Finset.single_le_sum ( fun i _ => colDef_nonneg hP i ) ( Finset.mem_univ j ) ) ( colDef_nonneg hP j )
    aesop
  simp_all [rowDef, colDef];
  constructor <;> simp_all [ sub_eq_zero ];
  · exact fun i j => hP.1 i j;
  · simp_all [ funext_iff, Matrix.mulVec, Matrix.vecMul ];
    simp_all [ dotProduct ]
    exact ⟨ fun i => h_row i ▸ rfl, fun j => h_col j ▸ rfl ⟩

/-- The correcting matrix Q_ij = s_i * t_j / S -/
private noncomputable def correctionMatrix (P : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => rowDef P i * colDef P j / totalDef P

/-- The dominating doubly stochastic matrix D = P + Q -/
private noncomputable def dominatingMatrix (P : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  P + correctionMatrix P

private lemma correctionMatrix_nonneg (hP : P ∈ doublySubstochastic ℝ (Fin n))
    (hS : 0 < totalDef P) (i j : Fin n) :
    0 ≤ correctionMatrix P i j := by
  exact div_nonneg ( mul_nonneg ( rowDef_nonneg hP i ) ( colDef_nonneg hP j ) ) hS.le

private lemma correctionMatrix_row_sum (hS : 0 < totalDef P) (i : Fin n) :
    ∑ j, correctionMatrix P i j = rowDef P i := by
  -- We can factor out `rowDef P i` from the sum, leaving `colDef P j` divided by `totalDef P`.
  have h_factor : ∑ j, (rowDef P i * colDef P j / totalDef P) = rowDef P i * (∑ j, colDef P j / totalDef P) := by
    simp only [ mul_div_assoc, Finset.mul_sum _ _ _ ];
  convert h_factor using 1;
  rw [ ← Finset.sum_div _ _ _, eq_comm ];
  rw [ ← totalDef_eq_sum_colDef, div_self hS.ne', mul_one ]

private lemma correctionMatrix_col_sum (hS : 0 < totalDef P) (j : Fin n) :
    ∑ i, correctionMatrix P i j = colDef P j := by
  simp +decide [ correctionMatrix ];
  rw [ ←Finset.sum_div _ _ _, ←Finset.sum_mul ] ; rw [ div_eq_iff hS.ne' ] ; ring;
  exact mul_comm _ _

private lemma dominatingMatrix_doublyStochastic
    (hP : P ∈ doublySubstochastic ℝ (Fin n))
    (hS : 0 < totalDef P) :
    dominatingMatrix P ∈ doublyStochastic ℝ (Fin n) := by
  refine' And.intro _ ( And.intro _ _ );
  · exact fun i j => add_nonneg ( hP.1 i j ) ( correctionMatrix_nonneg hP hS i j );
  · ext i; exact (by
    simp [ dominatingMatrix, Matrix.mulVec, dotProduct ];
    simp only [sum_add_distrib, correctionMatrix_row_sum hS i, rowDef];
    ring);
  · ext j; exact (by
    unfold dominatingMatrix; simp [ Matrix.vecMul, dotProduct ] ;
    rw [ Finset.sum_add_distrib, correctionMatrix_col_sum hS j ] ;
    unfold colDef; ring;);

private lemma dominatingMatrix_ge (hP : P ∈ doublySubstochastic ℝ (Fin n))
    (hS : 0 < totalDef P) (i j : Fin n) :
    P i j ≤ dominatingMatrix P i j := by
  exact le_add_of_nonneg_right ( correctionMatrix_nonneg hP hS i j )

/- Theorem C.1: Every doubly substochastic matrix is entry-wise bounded by a doubly stochastic matrix. -/
theorem exists_doublyStochastic_ge {n : ℕ} {P : Matrix (Fin n) (Fin n) ℝ}
  (hP : P ∈ doublySubstochastic ℝ (Fin n)) :
  ∃ D ∈ doublyStochastic ℝ (Fin n), ∀ i j, P i j ≤ D i j := by
  by_cases hS : 0 < totalDef P;
  · exact ⟨ _, dominatingMatrix_doublyStochastic hP hS, fun i j => dominatingMatrix_ge hP hS i j ⟩;
  · exact ⟨ P, doublyStochastic_of_totalDef_zero hP ( le_antisymm ( le_of_not_gt hS ) ( totalDef_nonneg hP ) ), fun i j => le_rfl ⟩

section Augmentation

variable {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]

def Dr (P : Matrix n n R) : Matrix n n R :=
  diagonal (P *ᵥ 1)

/-- The diagonal matrix of column sums: Dc = diag(c₁, ..., cₙ) -/
def Dc (P : Matrix n n R) : Matrix n n R :=
  diagonal (1 ᵥ* P)

def augmentingMatrix (P : Matrix n n R) : Matrix (Sum n n) (Sum n n) R :=
  fromBlocks P (1 - Dr P) (1 - Dc P) (Pᵀ)

theorem augmenting_mat_doublySubstochastic {P : Matrix n n ℝ}
  (hP : P ∈ doublySubstochastic ℝ n) :
  augmentingMatrix P ∈ doublyStochastic ℝ (n ⊕ n) := by
  unfold augmentingMatrix
  constructor
  · intro i j
    cases hi : i <;> cases hj : j <;>
    simp [fromBlocks_apply₁₁]
    . simp [hP.1]
    · unfold Dr; simp [Matrix.diagonal_apply];
      split_ifs with h_eq
      . rw [h_eq]; simp; apply hP.2.1
      aesop
    · unfold Dc; simp [Matrix.diagonal_apply];
      split_ifs with h_eq
      rw [h_eq]; simp; apply hP.2.2
      aesop
    · exact hP.1 _ _
  · simp [fromBlocks_mulVec]
    unfold Dr Dc
    constructor
    . simp [mulVec_one]
      ext j
      cases j with
      | inl j_old =>
        simp
        have h1 : ∑ x, (1 : Matrix n n ℝ) x j_old = 1 := by
          simp only [Matrix.one_apply]
          simp only [sum_ite_eq', mem_univ, ↓reduceIte]
        rw [h1]
        have h2 : ∑ x, (diagonal (P *ᵥ 1)) x j_old = (P *ᵥ 1) j_old := by
          simp [Matrix.diagonal]
        rw [← mulVec_one]
        rw [h2]
        have h3 : (P *ᵥ 1) j_old = ∑ c, P  j_old c := by
          rw [Matrix.mulVec_eq_sum]
          simp
        rw [h3]
        ring
      | inr j_new =>
        simp
        have h1 : ∑ x, (1 : Matrix n n ℝ) x j_new = 1 := by
          simp only [Matrix.one_apply]
          simp only [sum_ite_eq', mem_univ, ↓reduceIte]
        have h2 : ∑ x, (diagonal (1 ᵥ* P)) x j_new = (1 ᵥ* P) j_new := by
          simp [Matrix.diagonal]
        have h3 : (1 ᵥ* P) j_new = ∑ c, P c j_new := by
          rw [Matrix.vecMul_eq_sum]
          simp
        rw [h1, h2, h3]
        ring
    rw [one_vecMul]
    simp_rw [Fintype.sum_sum_type]
    ext j
    cases j with
    | inl j_n =>
      simp_rw [Pi.add_apply]
      simp_rw [Finset.sum_apply]
      simp only [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₁]
      have h2 : ∑ x, (diagonal (1 ᵥ* P)) x j_n = (1 ᵥ* P) j_n := by
        simp [Matrix.diagonal]
      simp
      rw [h2]
      rw [Matrix.vecMul_eq_sum]
      simp
      simp [Matrix.one_apply]
    | inr j_n =>
      simp_rw [Pi.add_apply, Finset.sum_apply, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₂]
      have h2 : ∑ x, (diagonal (P *ᵥ 1)) x j_n = (P *ᵥ 1) j_n := by
        simp [Matrix.diagonal]
      simp
      rw [h2, Matrix.mulVec_eq_sum]
      simp
      simp [Matrix.one_apply]

end Augmentation
