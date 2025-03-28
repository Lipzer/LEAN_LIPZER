--import MIL.Common
import Mathlib.Data.Real.Basic
import Mathlib
namespace C03S06

def ConvergesTo (s : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

example : (fun x y : ℝ ↦ (x + y) ^ 2) = fun x y : ℝ ↦ x ^ 2 + 2 * x * y + y ^ 2 := by
  ext
  ring

example (a b : ℝ) : |a| = |a - b + b| := by
  ring_nf
  

example {a : ℝ} (h : 1 < a) : a < a * a := by
  convert (mul_lt_mul_right _).2 h
  · rw [one_mul]
  exact lt_trans zero_lt_one h

theorem convergesTo_const (a : ℝ) : ConvergesTo (fun x : ℕ ↦ a) a := by
  intro ε εpos
  use 0
  intro n nge
  rw [sub_self, abs_zero]
  apply εpos

-------- TRY THIS ----------------------
theorem convergesTo_add {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n + t n) (a + b) := by
  intro ε εpos
  dsimp -- this line is not needed but cleans up the goal a bit.

  have ε2pos : 0 < ε / 2 := by linarith
  rcases cs (ε / 2) ε2pos with ⟨Ns, hs⟩
  rcases ct (ε / 2) ε2pos with ⟨Nt, ht⟩
  use max Ns Nt
  intro N h
  rw [<- sub_sub,add_sub_assoc,<- neg_add_eq_sub a, <-add_assoc,<- sub_eq_add_neg]
  congr
  apply lt_of_le_of_lt 
  have NNs: N≥ Ns := by apply ge_trans h (le_max_left Ns Nt)
  have NNt : N≥ Nt := by apply ge_trans h (le_max_right Ns Nt) 
  apply abs_add ( s N -a ) (t N -b)

  have h' : |s N - a + t N - b| ≤|s N - a| + |t N - b| := by 
    apply abs_add_le s n - a 
  sorry 
/-
#check abs_triangle
#check lt_of_le_of_lt
#check neg_add_eq_sub
#check sub_eq_add_neg
#check sub_sub
#check add_sub_assoc
#check neg_add
#check le_of_max_le_left
#check abs_add_le
#check add_tsub
#check sub_add_sub_comm
-/


theorem convergesTo_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (cs : ConvergesTo s a) :
    ConvergesTo (fun n ↦ c * s n) (c * a) := by
  intro ε εpos
  dsimp 
  by_cases h : c = 0
  · convert convergesTo_const 0
    · rw [h]
      ring
    rw [h]
    ring
  have acpos : 0 < |c| := abs_pos.mpr h
  have epsc_pos : 0< (ε/|c|) := by apply div_pos εpos acpos 
  rcases cs (ε/|c|) epsc_pos  with ⟨ N₀, h' ⟩ 
  use N₀
  intro n h1
  rw[<- mul_sub c, abs_mul,<- div_mul_cancel₀ ε (abs_ne_zero.mpr h), mul_comm (ε /|c|) ]
  apply  mul_lt_mul_of_pos_left ( h' n h1 ) acpos

 
  
theorem exists_abs_le_of_convergesTo {s : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) :
    ∃ N b, ∀ n, N ≤ n → |s n| < b := by
  rcases cs 1 zero_lt_one with ⟨N, h⟩
  use N, |a| + 1
  intro n h'
  have h₁ : |s n|-|a| <1 := by 
    apply lt_of_le_of_lt (abs_sub_abs_le_abs_sub (s n) a ) (h n h')
  linarith 

  
#check abs_sub_abs_le_abs_sub
theorem aux {s t : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) (ct : ConvergesTo t 0) :
    ConvergesTo (fun n ↦ s n * t n) 0 := by
  intro ε εpos
  dsimp
  rcases exists_abs_le_of_convergesTo cs with ⟨N₀, B, h₀⟩
  have Bpos : 0 < B := lt_of_le_of_lt (abs_nonneg _) (h₀ N₀ (le_refl _))
  have pos₀ : ε / B > 0 := div_pos εpos Bpos
  rcases ct _ pos₀ with ⟨N₁, h₁⟩
  use max N₁ N₀ 
  intro n h₂ 
  rw[sub_zero,abs_mul,<- sub_zero (t n)] 
  have nN₀ : n≥ N₀ := by apply ge_trans h₂ (le_max_right N₁ N₀ )
  have nN₀ : n≥ N₁ := by apply ge_trans h₂ (le_max_left N₁ N₀ )  
  have h₄ :|s n| * |t n - 0| < B* (ε /B) := by 
    apply mul_lt_mul'' (h₀ n nN₀ ) (h₁ n nN₁) (abs_nonneg (s n)) (abs_nonneg (t n -0) )
  rw[mul_comm B, div_mul_cancel₀ ε (ne_of_gt Bpos)] at h₄
  exact h₄

#check ne_of_gt
#check mul_div_cancel
#check ge_trans
#check mul_lt_mul''
#check sub_ne_zero_of_ne
theorem convergesTo_mul {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n * t n) (a * b) := by
  have h₁ : ConvergesTo (fun n ↦ s n * (t n + -b)) 0 := by
    apply aux cs
    convert convergesTo_add ct (convergesTo_const (-b))
    ring
  have := convergesTo_add h₁ (convergesTo_mul_const b cs)
  convert convergesTo_add h₁ (convergesTo_mul_const b cs) using 1
  · ext; ring
  ring

theorem convergesTo_unique {s : ℕ → ℝ} {a b : ℝ}
      (sa : ConvergesTo s a) (sb : ConvergesTo s b) :
    a = b := by
  by_contra abne
  have : |a - b| > 0 := by apply abs_pos.mpr  (sub_ne_zero_of_ne abne)
  let ε := |a - b| / 2
  have εpos : ε > 0 := by
    change |a - b| / 2 > 0
    linarith
  rcases sa ε εpos with ⟨Na, hNa⟩
  rcases sb ε εpos with ⟨Nb, hNb⟩
  let N := max Na Nb
  have absa : |s N - a| < ε := by apply hNa N (le_max_left Na Nb )
  have absb : |s N - b| < ε := by apply hNb N (le_max_right Na Nb )
  have : |a - b| < |a - b| := by
    have h1: |a-b|=|(a- s N)+(s N - b)| := by
      congr
      linarith
    have h2 : |a-b|< 2*ε := by 
      rw[h1]
      apply lt_of_le_of_lt
      apply abs_add (a - s N) ( s N -b)
      rw[sub_eq_neg_add,<- neg_neg a,<-neg_add,<- sub_eq_add_neg, abs_neg]
      linarith
    change  |a-b|< 2*(|a-b|/2) at h2 
    rw[mul_comm, div_mul_cancel₀ (|a-b|) two_ne_zero] at h2
    exact h2
  exact lt_irrefl _ this

section
variable {α : Type*} [LinearOrder α]

def ConvergesTo' (s : α → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

end

