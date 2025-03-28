--mport MIL.Common
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib

section

variable {α β : Type*}
variable (f : α → β)
variable (s t : Set α)
variable (u v : Set β)

open Function
open Set

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v := by
  ext x
  rfl

example : f '' (s ∪ t) = f '' s ∪ f '' t := by
  ext y; constructor
  · rintro ⟨x, xs | xt,rfl⟩
    · left
      use x, xs
    right
    use x, xt
  rintro (⟨x, xs, rfl⟩ | ⟨x, xt, rfl⟩)
  · use x
    exact ⟨ Or.inl xs, rfl ⟩  
  use x, Or.inr xt

example : s ⊆ f ⁻¹' (f '' s) := by
  intro x xs
  show f x ∈ f '' s
  use x, xs
-------------- TRY THIS --------------------------
example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
  constructor 
  intro h x xs
  apply h 
  use x, xs
  intro h' y yf
  rcases yf with ⟨ x, xs, xeq ⟩ 
  rw[<-xeq]
  apply h' xs


example (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := by
  intro x h'
  have h₁ : ∃ y, y ∈ s ∧  f y = f x := by 
    apply h'
  rcases h₁ with ⟨ y, h₂ ⟩ 
  have h₃ : y=x := by apply h (h₂.right) 
  rw[<-h₃] ; exact h₂.left



example : f '' (f ⁻¹' u) ⊆ u := by
  sorry

example (h : Surjective f) : u ⊆ f '' (f ⁻¹' u) := by
  sorry

example (h : s ⊆ t) : f '' s ⊆ f '' t := by
  sorry

example (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v := by
  sorry

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := by
  sorry

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t := by
  sorry

example (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by
  sorry

example : f '' s \ f '' t ⊆ f '' (s \ t) := by
  sorry

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) := by
  sorry

example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) := by
  sorry

example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∩ u := by
  sorry

example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) := by
  sorry

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) := by
  sorry

variable {I : Type*} (A : I → Set α) (B : I → Set β)

example : (f '' ⋃ i, A i) = ⋃ i, f '' A i := by
  sorry

example : (f '' ⋂ i, A i) ⊆ ⋂ i, f '' A i := by
  sorry

example (i : I) (injf : Injective f) : (⋂ i, f '' A i) ⊆ f '' ⋂ i, A i := by
  sorry

example : (f ⁻¹' ⋃ i, B i) = ⋃ i, f ⁻¹' B i := by
  sorry

example : (f ⁻¹' ⋂ i, B i) = ⋂ i, f ⁻¹' B i := by
  sorry

example : InjOn f s ↔ ∀ x₁ ∈ s, ∀ x₂ ∈ s, f x₁ = f x₂ → x₁ = x₂ := by
  Iff.refl_

end

section

open Set Real

example : InjOn log { x | x > 0 } := by
  intro x xpos y ypos
  intro e
  -- log x = log y
  calc
    x = exp (log x) := by rw [exp_log xpos]
    _ = exp (log y) := by rw [e]
    _ = y := by rw [exp_log ypos]


example : range exp = { y | y > 0 } := by
  ext y; constructor
  · rintro ⟨x, rfl⟩
    apply exp_pos
  intro ypos
  use log y
  rw [exp_log ypos]


----------------TRY THIS ---------------------------- 
example : InjOn sqrt { x | x ≥ 0 } := by
  intro x xpos y ypos
  intro h
  rw[<- sq_sqrt xpos, <- sq_sqrt ypos , h]


---------------- TRY THIS --------------------------------
example : InjOn (fun x ↦ x ^ 2) { x : ℝ | x ≥ 0 } := by
  intro x xpos y ypos
  dsimp at *
  intro h
  rw[<- sqrt_sq xpos, <- sqrt_sq ypos, h]



------------- TRY THIS --------------------------------
example : sqrt '' { x | x ≥ 0 } = { y | y ≥ 0 } := by
  ext  y
  constructor
  dsimp at *
  intro h
  rcases h with  ⟨ x, xpos, yeq⟩  
  rw[<- yeq]
  exact sqrt_nonneg x
  dsimp at *
  intro h'
  rw[<-sqrt_sq h']
  use y^2 , pow_two_nonneg y 

  
-------------------------- TRY THIS -----------------------
example : (range fun x ↦ x ^ 2) = { y : ℝ | y ≥ 0 } := by
  ext y
  constructor
  dsimp at *
  intro h
  rcases h with ⟨ x, xr, yeq ⟩
  dsimp
  exact pow_two_nonneg x
  intro h' ; dsimp at h'
  rw[<- sq_sqrt h' ]
  use ( sqrt y )


end

section
variable {α β : Type*} [Inhabited α]

#check (default : α)

variable (P : α → Prop) (h : ∃ x, P x)

#check Classical.choose h

example : P (Classical.choose h) :=
  Classical.choose_spec h

noncomputable section

open Classical
#check choose_spec
def inverse (f : α → β) : β → α := fun y : β ↦
  if h : ∃ x, f x = y then Classical.choose h else default

theorem inverse_spec {f : α → β} (y : β) (h : ∃ x, f x = y) : f (inverse f y) = y := by
  rw [inverse, dif_pos h]
  exact Classical.choose_spec h

variable (f : α → β)

open Function
#check LeftInverse
#check dif_pos


--------------- TRY THIS --------------------------
example : Injective f ↔ LeftInverse (inverse f) f := by
  constructor
  dsimp  
  intro h y
  have h' : ∃ x, f x = f y := by use y 
  let x:= inverse f (f y) 
  have h1 : f ( inverse f (f y) )= f y := by 
    rw[inverse,dif_pos h']
    exact Classical.choose_spe h'
  apply h h1
  dsimp 
  intro h x y h'
  rw[<- h x, <- h y, h']


------------------ TRY THIS ------------------------------
example : Surjective f ↔ RightInverse (inverse f) f := by
  constructor
  intro h y 
  have h' : ∃ x, f x = y :=by 
    apply h y 
 -- rcases h' with ⟨ x , yeq ⟩ 
  exact inverse_spec y h'
  intro h y
  use (inverse f) y , h y



end

section
variable {α : Type*}
open Function
----------- TRY THIS --------------------------------
theorem Cantor : ∀ f : α → Set α, ¬Surjective f := by
  intro f surjf
  let S := { i | i ∉ f i }
  rcases surjf S with ⟨j, h⟩
  have h₁ : j ∉ f j := by
    intro h'
    have : j ∉ f j := by rwa [h] at h'
    contradiction
  have h₂: j∈ S := by 
    exact h₁
  have h₃ : j ∉ S := by
    rw [h] at h₂
    exact h₂
  contradiction

-- COMMENTS: TODO: improve this
end
