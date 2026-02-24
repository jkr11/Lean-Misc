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

theorem qsp_representation (x : ℝ) (hx : -1 ≤ x ∧ x ≤ 1) (φs : List ℝ) :
  QSPForm φs.length x (qspSequence x φs) := by
  induction φs with
  | nil =>
    -- Base Case: The empty list yields the Identity matrix
    simp [qspSequence]
    use Polynomial.C 1, 0
    constructor
    . simp
    . simp; ext i j; fin_cases i <;> fin_cases j <;> rfl
  | cons φ φs ih =>
    rcases ih with ⟨P, Q, hdegP, hdegQ, hmat⟩
    let phase := exp (I * φ)
    let P_star := P.map (starRingEnd ℂ)
    let Q_star := Q.map (starRingEnd ℂ)
    let P_next := Polynomial.C phase * (Polynomial.X * P - (1 - Polynomial.X^2) * Q_star)
    let Q_next := C phase * (X * Q + P_star)
    use P_next, Q_next
    constructor
    . rw [List.length_cons]
      unfold P_next
      apply (natDegree_mul_le).trans
      simp only [natDegree_C, zero_add]
      apply (natDegree_sub_le _ _).trans
      apply max_le
      . apply (natDegree_mul_le).trans; rw [natDegree_X, add_comm]; exact add_le_add_left hdegP 1
      . apply (natDegree_mul_le).trans
        have h_deg1X2 : (1 - X^2 : Polynomial ℂ).natDegree = 2 := by
          sorry
        have h_degQstar : Q_star.natDegree = Q.natDegree := by sorry -- check when natDegree_map or map_natDegree can be imported
        rw [h_deg1X2, add_comm]; rw [h_degQstar]; simp; sorry
    . constructor
      . simp
        unfold Q_next; apply (natDegree_mul_le).trans; simp only [natDegree_C, zero_add]; apply (natDegree_add_le _ _).trans
        apply max_le
        . apply (natDegree_mul_le).trans; simp only [natDegree_X]; rw [add_comm, Nat.add_one_le_iff]; sorry -- why cant apply hdegQ with simp?
        . sorry -- also map degree here
      . rw [qspSequence]
        rw [hmat];
        have h_sq_comp : (↑(Real.sqrt (1 - x^2)) : ℂ)^2 = ↑((1 : ℂ) - x^2) := by
          norm_cast
          rw [Real.sq_sqrt]
          nlinarith [hx.1, hx.2]
        ext i j
        fin_cases i <;> fin_cases j
        . simp
          unfold Rz W P_next; simp;
          conv =>
            lhs
            ring
            rw [h_sq_comp]
          simp; have hphase : phase = cexp (I * φ) := by rfl
          rw [← hphase]; ring
        . unfold Rz W P_next Q_next phase; simp; norm_cast; ring
        . unfold Rz W P_next; simp; sorry
        . unfold Rz W P_next; simp;
          conv =>
            lhs
            ring; rw [Complex.I_sq, h_sq_comp]
          have hphase : phase = cexp (I * φ) := by rfl
          rw [← hphase];
          simp
          ring
          simp
          rw [← exp_conj]
          have h_phase_inv : phase⁻¹ = cexp (-I * ↑φ) := by
            rw [hphase, ← Complex.exp_neg]; simp
          have h_phase_star : cexp ((starRingEnd ℂ) (I * ↑φ)) = cexp (-I * ↑φ) := by
            simp only [map_mul, conj_I, conj_ofReal, neg_mul]
          have h_Q_double_star : (Polynomial.map (starRingEnd ℂ) Q_star) = Q := by
            simp [Q_star]; sorry
          rw [h_phase_inv, h_phase_star, h_Q_double_star]
          simp only [neg_mul, ← Complex.ofReal_pow]
          ring



        sorry
