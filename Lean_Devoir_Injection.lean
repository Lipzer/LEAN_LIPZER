import Mathlib
import Mathlib.Data.Set.Lattice
import Mathlib.Data.Set.Function
import Mathlib.Analysis.SpecialFunctions.Log.Basic

section


open Function
open Set

------------- Définition l'ensemble des entiers pairs et de la fonction + 2 sur les entiers pairs  ------------
def evens : Set ℕ := { n | ∃ k, n=2*k } 

def f (x : { n : ℕ  | ∃ k, n=2*k }) : { n : ℕ | ∃ k, n=2*k } := 
  ⟨x.1 + 2, by 
    obtain ⟨k, hk⟩ := x.2  
    use k + 1              
    simp [hk]
    linarith
    ⟩
----------------      Résolution de l'exercice -------------------
example : InjOn (fun x : ℕ ↦ x + 2)  evens  := by 
  intro x xev y yev h
  dsimp at *                   -- Simplifier les définitions ---
  linarith
  
 /- ---------- Autre preuve -----------------
    intro x xe y ye h
    simp at *
    exact h

-/

end
 