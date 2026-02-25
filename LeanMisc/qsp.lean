import Mathlib.Data.Matrix.Basic
-- import Mathlib.Data.Matrix.Notation
import Mathlib.Data.Complex.Exponential
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Eval.Defs

open Complex Matrix

abbrev QubitOp := Matrix (Fin 2) (Fin 2) ℂ

-- The Phase Rotation Operator Rz(θ) = exp(i * θ * Z)
noncomputable def Rz (θ : ℝ) : QubitOp :=
  let phase := exp (I * ↑θ)
  !![phase, 0; 0, phase⁻¹]

-- The Signal Operator W(x) for x in [-1, 1]
noncomputable def W (x : ℝ) : QubitOp :=
  let x_c : ℂ := ↑x
  let y_c : ℂ := ↑(Real.sqrt (1 - x^2))
  !![x_c, I * y_c;
     I * y_c, x_c]

noncomputable def qspSequence (x : ℝ) : List ℝ → QubitOp
  | [] => 1
  | [φ] => Rz φ
  | φ :: φs => Rz φ * W x * qspSequence x φs

structure QSPForm_ (d : ℕ) (x : ℝ) (M : QubitOp) : Type where
  P : Polynomial ℂ
  Q : Polynomial ℂ
  deg_P : P.natDegree ≤ d
  deg_Q : P.natDegree ≤ d - 1
  matrix_eq : M = !![P.eval ↑x, I * ↑(Real.sqrt (1 - x^2)) * Q.eval ↑x;
                     I * ↑(Real.sqrt (1 - x^2)) * (Q.map (starRingEnd ℂ)).eval ↑x, (P.map (starRingEnd ℂ)).eval ↑x]

def QSPForm (d : ℕ) (x : ℝ) (M : QubitOp) : Prop :=
  ∃ (P Q : Polynomial ℂ),
    P.natDegree ≤ d ∧
    Q.natDegree ≤ d - 1 ∧
    M = !![P.eval ↑x, I * ↑(Real.sqrt (1 - x^2)) * Q.eval ↑x;
                     I * ↑(Real.sqrt (1 - x^2)) * (Q.map (starRingEnd ℂ)).eval ↑x, (P.map (starRingEnd ℂ)).eval ↑x]

open Polynomial

variable {R : Type*} [Semiring R] {f : R[X]}

lemma map_comp_map_comp {Q : Polynomial ℂ} : Polynomial.map (starRingEnd ℂ) (Polynomial.map (starRingEnd ℂ) Q) = Q := by
  rw [Polynomial.map_map]; simp

theorem qsp_representation (x : ℝ) (hx : -1 ≤ x ∧ x ≤ 1) (φs : List ℝ) :
  QSPForm φs.length x (qspSequence x φs) := by
  induction φs with
  | nil =>
    simp [qspSequence]
    use Polynomial.C 1, 0
    constructor
    · simp
    · constructor
      · simp
      · simp; ext i j; fin_cases i <;> fin_cases j <;> rfl
  | cons φ φs ih =>
    cases h_φs : φs with
    | nil =>
      simp [qspSequence]
      let phase := Complex.exp (I * ↑φ)
      use Polynomial.C phase, 0
      constructor
      · simp
      · constructor
        · simp
        · ext i j; fin_cases i <;> fin_cases j
          · simp [Rz, phase]
          · simp [Rz]
          · simp [Rz]
          · simp [Rz]
            have h_phase_star : starRingEnd ℂ phase = phase⁻¹ := by
              dsimp [phase]; rw [← exp_conj]
              simp; rw [← Complex.exp_neg]
            rw [← h_phase_star]

    | cons θ tail =>
      rw [h_φs] at ih
      rcases ih with ⟨P, Q, hdegP, hdegQ, hmat⟩
      let phase := Complex.exp (I * ↑φ)
      have h_phase_star : starRingEnd ℂ phase = phase⁻¹ := by
        dsimp [phase]; rw [← exp_conj]
        simp; rw [← Complex.exp_neg]
      let P_star := P.map (starRingEnd ℂ)
      let Q_star := Q.map (starRingEnd ℂ)
      let P_next := Polynomial.C phase * (Polynomial.X * P - (1 - Polynomial.X^2) * Q_star)
      let Q_next := Polynomial.C phase * (Polynomial.X * Q + P_star)
      use P_next, Q_next

      have h_deg1X2 : (1 - Polynomial.X^2 : Polynomial ℂ).natDegree ≤ 2 := by
        refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ ?_)
        · rw [Polynomial.natDegree_one]; exact zero_le 2
        · rw [Polynomial.natDegree_pow, Polynomial.natDegree_X];
      constructor
      · -- Degree bound for P_next
        rw [List.length_cons]
        dsimp [P_next]
        refine (Polynomial.natDegree_mul_le).trans ?_
        rw [Polynomial.natDegree_C, zero_add]
        refine (Polynomial.natDegree_sub_le _ _).trans (max_le ?_ ?_)
        · refine (Polynomial.natDegree_mul_le).trans ?_
          rw [Polynomial.natDegree_X, add_comm]
          exact Nat.add_le_add_right hdegP 1
        · refine (Polynomial.natDegree_mul_le).trans ?_
          rw [Polynomial.natDegree_map]
          have h_step : (1 - Polynomial.X^2 : Polynomial ℂ).natDegree + Q.natDegree ≤ 2 + (tail.length + 1 - 1) :=
            Nat.add_le_add h_deg1X2 hdegQ
          exact h_step.trans (by omega)
      · constructor
        · -- Degree bound for Q_next
          rw [List.length_cons]
          dsimp [Q_next]
          refine (Polynomial.natDegree_mul_le).trans ?_
          rw [Polynomial.natDegree_C, zero_add]
          refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
          · refine (Polynomial.natDegree_mul_le).trans ?_
            rw [Polynomial.natDegree_X, add_comm]
            have h_step : 1 + Q.natDegree ≤ 1 + (tail.length + 1 - 1) := Nat.add_le_add_left hdegQ 1;
            simp at h_step
            simp; exact h_step
          · rw [Polynomial.natDegree_map]
            simp at hdegP
            exact hdegP
        ·
          rw [qspSequence, hmat]
          have h_sq_comp : (↑(Real.sqrt (1 - x^2)) : ℂ)^2 = ↑((1 : ℝ) - x^2) := by
            push_cast; norm_cast; rw [Real.sq_sqrt (by nlinarith [hx.1, hx.2])]
          have hphase : phase = cexp (I * φ) := by rfl
          have h_phase_star : starRingEnd ℂ phase = phase⁻¹ := by
              dsimp [phase]; rw [← exp_conj]
              simp; rw [← Complex.exp_neg]
          ext i j
          fin_cases i <;> fin_cases j
          ·
            dsimp [Rz, W, P_next, phase]
            simp;
            conv =>
              left
              ring
              rw [h_sq_comp]
            rw [Complex.I_sq]
            simp;
            rw [← hphase]; ring
          ·
            unfold Rz W P_next Q_next phase; simp; norm_cast; ring
          ·
            unfold Rz W P_next Q_next; simp; ring_nf; norm_cast; rw [hphase, ← exp_conj]; simp; rw [Complex.exp_neg]; rw [map_comp_map_comp]; norm_cast; ring
          ·
            unfold Rz W P_next; simp;
            conv =>
              lhs
              ring; rw [Complex.I_sq, h_sq_comp]
            simp
            ring
            simp
            rw [Polynomial.map_map, h_phase_star, hphase]; simp;
            ring
          intro h
          simp at h
