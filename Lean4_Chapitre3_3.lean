--import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S03

section
variable (a b : ℝ)

example (h : a < b) : ¬b < a := by
  intro h'
  have : a < a := lt_trans h h'
  apply lt_irrefl a this

def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ f x

def FnHasUb (f : ℝ → ℝ) :=
  ∃ a, FnUb f a

def FnHasLb (f : ℝ → ℝ) :=
  ∃ a, FnLb f a

variable (f : ℝ → ℝ)

example (h : ∀ a, ∃ x, f x > a) : ¬FnHasUb f := by
  intro fnub
  rcases fnub with ⟨ a, fnuba⟩ 
  rcases h a with ⟨x, hx⟩
  have : f x ≤ a := fnuba x
  linarith

example (h : ∀ a, ∃ x, f x < a) : ¬FnHasLb f := by
  intro fnhaslb
  rcases fnhaslb with ⟨ a, flb⟩ 
  rcases h a with ⟨ m, fmla⟩ 
  have h1: f m ≥  a :=  flb m
  have h2: a<a := by apply  gt_of_gt_of_ge fmla h1
  apply lt_irrefl a h2




example : ¬FnHasUb fun x ↦ x :=
  -- Pareil --------

#check (not_le_of_gt : a > b → ¬a ≤ b)
#check (not_lt_of_ge : a ≥ b → ¬a < b)
#check (lt_of_not_ge : ¬a ≥ b → a < b)
#check (le_of_not_gt : ¬a > b → a ≤ b)


#check Monotone f
example (h : Monotone f) (h' : f a < f b) : a < b := by
  apply lt_of_not_ge
  intro h1
  have h2: f b ≤  f a := by apply h h1
  have : f a <f a := lt_of_lt_of_le h' h2
  apply lt_irrefl (f a )  this


example (h : a ≤ b) (h' : f b < f a) : ¬Monotone f := by
  intro h1
  have : f a ≤ f b := by  apply h1 h
  have : f a < f a := by apply lt_of_le_of_lt this h'
  apply lt_irrefl (f a) this

------------ TRY THIS ---------------------------------
example : ¬∀ {f : ℝ → ℝ}, Monotone f → ∀ {a b}, f a ≤ f b → a ≤ b := by
  intro h
  let f := fun x : ℝ ↦ (0 : ℝ)
  have monof : Monotone f := by 
    intro a b h1
    have h2: f a =0 := by trivial
    have h3: f b =0 := by trivial
    trivial 
  have h' : f 1 ≤ f 0 := le_refl _
  have h'' : 1 ≤ 0  := by apply   h f monof 1 0 h'
  trivial
  
#check le_of_not_gt
example (x : ℝ) (h : ∀ ε > 0, x < ε) : x ≤ 0 := by
apply le_of_not_gt
intro h'
apply lt_irrefl x
apply h x
exact h'
end


section
variable {α : Type*} (P : α → Prop) (Q : Prop)

example (h : ¬∃ x, P x) : ∀ x, ¬P x := by
  intro x h'
  apply h 
  use x

example (h : ∀ x, ¬P x) : ¬∃ x, P x := by
  intro h'
  rcases h' with ⟨ x, h2⟩ 
  apply h x
  exact h2

example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  by_contra h'
  apply h
  intro x
  by_contra 
  apply h'
  use x



example (h : ∃ x, ¬P x) : ¬∀ x, P x := by
  sorry ------ Pareil ----------

example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
  by_contra h'
  apply h
  intro x
  show P x
  by_contra h''
  exact h' ⟨x, h''⟩

--------------- TRY THIS ---------------------
example (h : ¬¬Q) : Q := by
  by_contra h'
  apply h 
  exact h'

example (h : Q) : ¬¬Q := by
  intro h1
  apply h1 h

end

section
variable (f : ℝ → ℝ)
----- TRY THIS --------------------------------
example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  intro a 
  by_contra h'
  apply h
  use a 
  intro x
  by_contra h2
  have h3 : f x > a := by 
    apply lt_of_not_ge h2
  apply  h'
  use x



example (h : ¬∀ a, ∃ x, f x > a) : FnHasUb f := by
  push_neg at h
  exact h

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  dsimp only [FnHasUb, FnUb] at h
  push_neg at h
  exact h
---------------- TRY THIS -----------------------------
example (h : ¬Monotone f) : ∃ x y, x ≤ y ∧ f y < f x := by
  dsimp only [Monotone] at h
  push_neg at h
  exact h

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
  contrapose! h
  exact h

example (x : ℝ) (h : ∀ ε > 0, x ≤ ε) : x ≤ 0 := by
  contrapose! h
  use x / 2
  constructor <;> linarith

end

section
variable (a : ℕ)

example (h : 0 < 0) : a > 37 := by
  exfalso
  apply lt_irrefl 0 h

example (h : 0 < 0) : a > 37 :=
  absurd h (lt_irrefl 0)

example (h : 0 < 0) : a > 37 := by
  have h' : ¬0 < 0 := lt_irrefl 0
  contradiction

end

