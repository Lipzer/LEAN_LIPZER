--import MIL.Common
import Mathlib.Data.Real.Basic

namespace C02S04

section
variable (a b c d : ℝ)

#check (min_le_left a b : min a b ≤ a)
#check (min_le_right a b : min a b ≤ b)
#check (le_min : c ≤ a → c ≤ b → c ≤ min a b)

#check (le_max_left a b :  max a b ≥ a)
#check (le_max_right a b : max a b ≥ b)
#check (max_le : c ≥ a → c ≥ b → c ≥ max a b)
#check le_antisymm
#check min_comm
#check add_neg_cancel_right
#check sub_eq_add_neg 
#check Nat.gcd_comm



example : min a b = min b a := by
  apply le_antisymm
  · show min a b ≤ min b a
    apply le_min
    apply min_le_right a b
    apply min_le_left a b
    
  · show min b a ≤ min a b
    apply le_min
    · apply min_le_right
    apply min_le_left

example : min a b = min b a := by
  have h : ∀ x y : ℝ, min x y ≤ min y x := by
    intro x y
    apply le_min 
    apply min_le_right x y
    apply min_le_left x y 
  apply le_antisymm
  apply h
  apply h

example : min a b = min b a := by
  apply le_antisymm
  repeat
    apply le_min
    apply min_le_right
    apply min_le_left
-- TRY THIS --
example : max a b = max b a := by
  have h : ∀ x y : ℝ, max x y ≥ max y x := by
    intro x y
    apply max_le 
    apply le_max_right x y
    apply le_max_left x y 
  apply le_antisymm
  apply h
  apply h 
example : min (min a b) c = min a (min b c) := by
  have h₁ :  ∀ x y z : ℝ, min (min x y) z ≤ x := by
    intro x y z
    apply le_trans
    apply min_le_left (min x y) z
    apply min_le_left x y
  have h₂ :  ∀ x y z : ℝ, min (min x y) z ≤ y := by
    intro x y z
    apply le_trans
    apply min_le_left (min x y) z
    apply min_le_right x y
  
  have h₃ :  ∀ x y z : ℝ, min (min x y) z ≤ z := by
    intro x y z
    apply min_le_right (min x y) z
  have h₄ :  ∀ x y z : ℝ, min (min x y) z ≤ min x (min y z) := by
    intro x y z
    apply le_min
    apply h₁
    apply le_min 
    apply h₂
    apply h₃
  
  apply le_antisymm
  apply h₄
  rw[min_comm, min_comm b c ]
  apply le_trans
  apply h₄
  rw[min_comm b a, min_comm]



  


    
     
      


  

theorem aux : min a b + c ≤ min (a + c) (b + c) := by
  sorry  -- Pareil que ci-dessus --
example : min a b + c = min (a + c) (b + c) := by
  apply le_antisymm
  apply aux
  rw[<- add_neg_cancel_right (min (a + c) (b + c)) c, add_assoc, add_comm c,<- add_assoc, <- sub_eq_add_neg]
  apply add_le_add_right
  -- Le reste évident --------

#check (abs_add : ∀ a b : ℝ, |a + b| ≤ |a| + |b|)

example : |a| - |b| ≤ |a - b| := by
/- trois ligne de codes-/
nth_rewrite 1[<-add_neg_cancel_right a b, add_assoc, add_comm b, <- add_assoc,<-sub_eq_add_neg, <- add_neg_cancel_right (|a - b|) (|b|)]
apply add_le_add_right
apply abs_add

end

section
variable (w x y z : ℕ)

example (h₀ : x ∣ y) (h₁ : y ∣ z) : x ∣ z :=
  dvd_trans h₀ h₁

example : x ∣ y * x * z := by
  apply dvd_mul_of_dvd_left
  apply dvd_mul_left

example : x ∣ x ^ 2 := by
  apply dvd_mul_left

example (h : x ∣ w) : x ∣ y * (x * z) + x ^ 2 + w ^ 2 := by
  sorry
end

section
variable (m n : ℕ)

#check (Nat.gcd_zero_right n : Nat.gcd n 0 = n)
#check (Nat.gcd_zero_left n : Nat.gcd 0 n = n)
#check (Nat.lcm_zero_right n : Nat.lcm n 0 = 0)
#check (Nat.lcm_zero_left n : Nat.lcm 0 n = 0)

example : Nat.gcd m n = Nat.gcd n m := by
  apply Nat.gcd_comm
end


