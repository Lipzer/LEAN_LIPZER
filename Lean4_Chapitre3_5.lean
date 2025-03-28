--import MIL.Common
import Mathlib.Data.Real.Basic
import Mathlib

namespace C03S05

section

variable {x y : ℝ}

example (h : y > x ^ 2) : y > 0 ∨ y < -1 := by
  left
  linarith [pow_two_nonneg x]

example (h : -y > x ^ 2 + 1) : y > 0 ∨ y < -1 := by
  right
  linarith [pow_two_nonneg x]

example (h : y > 0) : y > 0 ∨ y < -1 :=
  Or.inl h
  

example (h : y < -1) : y > 0 ∨ y < -1 :=
  Or.inr h

example : x < |y| → x < y ∨ x < -y := by
  rcases le_or_gt 0 y with h | h
  · rw [abs_of_nonneg h]
    intro h; left; exact h
  · rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  case inl h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  case inr h =>
    rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  next h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  next h =>
    rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  match le_or_gt 0 y with
    | Or.inl h =>
      rw [abs_of_nonneg h]
      intro h; left; exact h
    | Or.inr h =>
      rw [abs_of_neg h]
      intro h; right; exact h

namespace MyAbs

theorem le_abs_self (x : ℝ) : x ≤ |x| := by
  rcases le_or_gt 0 x with h₁ | h₂
  · rw[abs_of_nonneg h₁] 
    linarith
  · rw[abs_of_neg h₂]
    linarith
  

theorem neg_le_abs_self (x : ℝ) : -x ≤ |x| := by
  sorry ------ Pareil ------------

theorem abs_add (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  rcases le_or_gt 0 (x+y) with h₁ | h₂
  · rw[abs_of_nonneg h₁]
    apply add_le_add 
    apply le_abs_self x
    apply le_abs_self y
  · rw[abs_of_neg,neg_add]
    apply add_le_add 
    apply neg_le_abs_self x
    apply neg_le_abs_self y
  

theorem lt_abs : x < |y| ↔ x < y ∨ x < -y := by
  sorry--- Déja fait -------------

theorem abs_lt : |x| < y ↔ -y < x ∧ x < y := by
  constructor
  · intro h
    constructor 
    rw[<-neg_neg x]
    apply neg_lt_neg
    apply lt_of_le_of_lt (neg_le_abs_self x) h 
    apply  lt_of_le_of_lt (le_abs_self x) h
  · intro h'
    rcases le_or_gt 0 x with h₂ | h₃
    have ⟨ h₀, h₁ ⟩ :=h'
    rw[abs_of_nonneg]
    exact h₁
    exact h₂
    rw[abs_of_neg h₃]
    exact h₀
    

end MyAbs

end

example {x : ℝ} (h : x ≠ 0) : x < 0 ∨ x > 0 := by
  rcases lt_trichotomy x 0 with xlt | xeq | xgt
  · left
    exact xlt
  · contradiction
  · right; exact xgt

example {m n k : ℕ} (h : m ∣ n ∨ m ∣ k) : m ∣ n * k := by
  rcases h with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · rw [mul_assoc]
    apply dvd_mul_right
  · rw [mul_comm, mul_assoc]
    apply dvd_mul_right

example {z : ℝ} (h : ∃ x y, z = x ^ 2 + y ^ 2 ∨ z = x ^ 2 + y ^ 2 + 1) : z ≥ 0 := by
  rcases h with ⟨ x, y, h'⟩ 
  rcases h' with  h1| h2  
  <;> linarith[pow_two_nonneg x , pow_two_nonneg y ]



example {x : ℝ} (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  sorry ----- Pareil ----------------

example {x y : ℝ} (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  sorry ----- Pareil---------------

section
variable {R : Type*} [CommRing R] [IsDomain R]
variable (x y : R)

example (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  sorry ----------Pareil ---------------

example (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  sorry  ----------Pareil ---------------

end

example (P : Prop) : ¬¬P → P := by
  intro h
  cases em P
  · assumption
  · contradiction

example (P : Prop) : ¬¬P → P := by
  intro h
  by_cases h' : P
  · assumption
  contradiction

example (P Q : Prop) : P → Q ↔ ¬P ∨ Q := by
  sorry  ----------Pareil ---------------

