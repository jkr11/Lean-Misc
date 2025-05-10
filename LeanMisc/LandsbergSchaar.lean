import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Finset.Basic
import Mathlib.Analysis.Fourier.PoissonSummation
import Mathlib.Data.Complex.Exponential
import Mathlib.Data.Complex.Basic

noncomputable
def exp (t : ℝ) : ℂ :=
  Complex.exp (2 * ↑Real.pi * Complex.I * t)

noncomputable
def f (p q : ℕ) (x : ℕ) : ℂ :=
  exp ((x ^ 2) / (4 * p * q))

lemma f_periodic (t : ℕ) (p q : ℕ) :
  f p q (t + 2 * p * q) = f p q (t) :=
    by
    unfold f; unfold exp;
    field_simp; rw [add_sq, left_distrib, left_distrib];
    sorry

lemma exp_periodic : Function.Periodic (fun x => exp x) (2*Real.pi) := by
  unfold exp; intro s; simp; sorry

lemma ar {p q : ℕ} : (2 * ↑p * ↑q)^2 = p * q * (4 * p * q) :=   by ring

lemma f_periodic_ {p q : ℕ} : Function.Periodic (fun (x:ℕ) => f p q x) (2*p*q) := by
  rcases eq_or_ne (2*p*q) 0 with (hL | hT)
  . intro s; simp only [hL]; simp
  . intro s; unfold f; unfold exp; simp; rw [add_sq]; sorry

lemma exp_add (a b : ℝ) :
  exp (a) * exp (b) = exp (a + b) := by
  unfold exp;
  rw [← Complex.exp_add, ← left_distrib];
  congr;
  rw [Complex.ofReal_add]

lemma exp_sub (a b : ℝ) :
  exp (a - b) = exp (-b) * exp (a) := by
  unfold exp;
  rw [← Complex.exp_add, ← left_distrib]
  field_simp
  rw [sub_eq_add_neg, add_comm]

lemma sum_mul_left (c : ℂ) {n : ℕ} {f : ℕ → ℂ} :
  c * ∑ x ∈ Finset.range n, f x = ∑ x ∈ Finset.range n, c * f x := by
    rw [mul_comm, Finset.sum_mul]
    congr
    funext
    rw [mul_comm]

lemma sum_mul_right (c : ℂ) (n : ℕ) (f : ℕ → ℂ) :
  c * ∑ x ∈ Finset.range n, f x = ∑ x ∈ Finset.range n, f x * c := by
    rw [mul_comm, Finset.sum_mul]


noncomputable
def S' (a p : ℕ) : ℂ :=
  ∑ x ∈ Finset.range (p), Complex.exp ((a * x ^ 2) / p)

noncomputable
def S (n : ℕ) : ℂ :=
  ∑ x ∈ Finset.range n, Complex.exp ((x ^ 2) / (4 * n))

noncomputable
def fourier_series (n : ℕ) (fn : ℕ → ℂ): (ℕ → ℂ) :=
  λ x => ∑ k ∈ Finset.range n, fn k * exp ((k * x/ n))

noncomputable
def fourier_coefficients (n : ℕ) (f : ℕ → ℂ) : (ℕ → ℂ) :=
  λ k => (1/n) *  ∑ x ∈ Finset.range n, f x * exp (-( (k * x) / n))

noncomputable
def fourier_coefficients' (n : ℕ) (k : ℕ) (f : ℕ → ℂ) : ℂ :=
  (1/n) *  ∑ x ∈ Finset.range n, f x * exp (-( (k * x) / n))


/- theorem poisson_summation_theorem (p q : ℕ) :
  ∑ x ∈ Finset.range (2 * p * q), Complex.exp ((x ^ 2) / (4 * p * q)) =
  Complex.exp ( (- (p * q) ^ 2 / (4 * p * q))) * S (4 * p * q) := by sorry -/

noncomputable
def f_hat (p q : ℕ) (f : ℕ → ℂ) : (ℕ → ℂ) :=
  fourier_coefficients (2 * p * q) f

noncomputable
def f_hat' (p q : ℕ) (f : ℕ → ℂ) (x : ℕ) : ℂ :=
  fourier_coefficients (2 * p * q) f x


lemma canc (a b c : ℂ) (ha : a ≠ 0) (hc : c ≠ 0) :
  (a * b) / (a * c) = b / c := by
  rw [mul_div_assoc]
  ring_nf
  calc
    _ = (a * a⁻¹) * b * c⁻¹ := by ring
    _ = b * c⁻¹ := by field_simp

lemma step1 {k s : ℂ} {p q : ℂ} :
  ↑k * ↑s / ↑(2 * p * q) = (2 * k * s) / (4 * p * q) := by
  ring

lemma step2 {k p q : ℕ} {s : ℕ} :
  exp (s^2 / (4 * p * q) +  -(↑k * ↑s / ↑(2 * p * q))) = exp (s^2 / (4 * p * q) - 2*↑k * ↑s / ↑(4 * p * q)) := by
  unfold exp; field_simp; ring_nf

theorem step_one (p q : ℕ) (k : ℕ) (hp : p ≠ 0) (hq : q ≠ 0) (hpq : (2:ℂ)*p*q ≠ 0):
  f_hat' p q (f p q) k = 1/(2 * p * q) * (∑ x ∈ Finset.range (2 * p * q), exp ((x^2 - 2 * k * x)/(4 * p * q))):= by
    simp only [f_hat']
    unfold fourier_coefficients
    unfold f
    simp only [exp_add]
    simp only [step2]
    calc
      _ = 1/(2 * p * q) * (∑ x ∈ Finset.range (2 * p * q), exp ((x^2 - 2 * k * x) / (4 * p * q))) := by field_simp

theorem step_two (p q : ℕ) (k : ℕ) (hpq : (2:ℂ)*p*q ≠ 0):
  1/(2 * p * q) * (∑ x ∈ Finset.range (2 * p * q), exp ((x^2 - 2 * k * x)/(4 * p * q))) = 1/(2 * p * q) * (∑ x ∈ Finset.range (2 * p * q), exp (((x - k)^2 - k ^2 ) / (4 * p * q))) := by
    field_simp
    conv =>
      rhs
      simp only [sub_sq, mul_comm k _]
    field_simp
    simp only [mul_assoc]
    simp [mul_comm]

lemma _exp_sub(x k p q : ℕ) :
  exp ((((x - k)^2) - (k ^2)) / (4 * p * q)) = exp ((-k^2) / (4 * p * q)) * exp ((x-k)^2 / (4 * p * q)) := by
  rw [sub_div ((x-k :ℝ )^2) (k^2) (4 * p * q) ]
  rw [exp_sub]
  field_simp

theorem step_three (p q : ℕ) (k : ℕ):
  1/(2 * p * q) * (∑ x ∈ Finset.range (2 * p * q), exp ((((x - k :ℝ)^2) - (k ^2) ) / (4 * p * q))) = 1 / (2 * p * q) * exp (- k^2 / (4 * p * q)) * (∑ x ∈ Finset.range (2 * p * q), exp ((x-k)^2 / (4 * p * q))) := by
    field_simp
    congr
    simp [_exp_sub, sum_mul_left]

lemma translation_invariance (N : ℕ) (k : ℕ):
  ∑ x ∈ Finset.range (N), exp ((x-k)^2 / (2 * N)) = ∑ x ∈ Finset.range (N), exp ((- x^2) / (2*N)) := by
  sorry


theorem step_four (p q : ℕ) (k : ℕ) (hpq : p * q ≠ 0) :
  1/(2 * p * q) * (∑ x ∈ Finset.range (2 * p * q), (exp ((x - k)^2 / (4 * p * q)) * exp ((- k ^2 ) / (4 * p * q)))) = 1 / (2 * p * q) * exp (- k^2 / (4 * p * q)) * (∑ x ∈ Finset.range (2 * p * q), exp (- x^2 / (4 * p * q))) := by
    rw [← sum_mul_right]
    field_simp
    sorry
    --simp only [translation_invariance (2 * p * q)]
