--import Mathlib.RingTheory.Subring.Basic
--import Mathlib.Algebra.Adjoin.Basic
--import Mathlib.Data.Polynomial.Basic
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.Rat
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.Algebra.Algebra.Basic
import Mathlib
import Mathlib.Algebra.GroupWithZero.Units.Basic
import Mathlib.Data.Complex.Exponential
import Mathlib.RingTheory.Ideal.Basic

open Units
open Subgroup
open Complex
variable (p m n: ℕ) (hp : Nat.Prime p) (hm : 1 ≤ m) {hn: n≠ 0} (hn1 : n=p^m) (x : ℂˣ)

-- Définition de n
--noncomputable def n : ℕ := p ^ m

-- Définition de ζₙ, une racine primitive n-ième de l'unité
noncomputable def ζ (n:ℕ): ℂ := exp ((2 *Complex.I * Real.pi )/ n)

-- Définition de K = ℚ(ζₙ)
noncomputable def K : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ ( {ζ n} : Set ℂ )

-- Définition du groupe des unités cyclotomiques Vₙ
noncomputable def Vₙ : Subgroup ℂˣ :=
  Subgroup.closure (
    { (-1 : ℂˣ) } ∪ {Units.mk0 (ζ n) (exp_ne_zero _)} ∪
    { x : ℂˣ | ∃ a : ℕ, 1 ≤ a ∧ a ≤ n ∧ (a,p)=1 ∧  x = (1 - (ζ n) ^ a) }
  )

--Défintion de Z(ζ)
noncomputable def Z (n:ℕ): Subalgebra ℤ ℂ :=
 Algebra.adjoin ℤ ({ζ n} : Set ℂ )
-- Définition de η :
noncomputable def η (a:ℕ) : ℂ := (ζ n)^((1-a)/2)*((1-(ζ n)^a)/(1-(ζ n)))



lemma my_lem1 :  ∀ j:ℕ , 1<j-> j<n-1 -> (1:ℂ)-(ζ n)^j ∉ (Z n)ˣ :=by
  sorry
lemma my_lem2 : ∀ j:ℕ , 1<j-> j<n-1 -> ((1:ℂ)-(ζ n)^j)/((1:ℂ )-(ζ n)) ∈ (Z n)ˣ :=by sorry

lemma my_lem3 {a:ℕ } (hn: n≠ 0) (h0: (ζ n )=exp ((2 *Complex.I * Real.pi) / n) )(h1: 1 ≤ a ∧ a ≤ n) (h2:(a,p)=1) : 1-(ζ n)^a=-(ζ n)^a*(1-(ζ n)^(n-a)) :=by
  have h3: ζ n ^n=1 :=by
    simp[h0]
    rw [<-Complex.exp_nat_mul (2 *Complex.I * Real.pi/n) n,mul_assoc,<- mul_div_assoc,mul_comm,mul_assoc,mul_assoc I,<-mul_assoc, <-mul_assoc, mul_div_cancel_right₀,mul_assoc,mul_comm I , <- mul_assoc]
    simp[exp_add_mul_I]
    exact Nat.cast_ne_zero.mpr hn
  field_simp[h3]
  rw[mul_sub_left_distrib,mul_one,<- pow_add, add_comm, Nat.sub_add_cancel, h3,neg_sub]
  exact h1.right

lemma my_lem4: ∀ j:ℕ , 1<j-> j<n-1-> Ideal.span ({1-ζ}:set Z ) =Ideal.span ({1-ζ^j}: set Z ):= by sorry

lemma my_lem5 {n p :ℕ }: Vₙ p n =
  Subgroup.closure (
    { (-1 : ℂˣ) } ∪ {Units.mk0 (ζ n) (exp_ne_zero _)} ∪
    { x : ℂˣ | ∃ a : ℕ, 1 ≤ a ∧ a ≤ n/2 ∧ (a,p)=1 ∧  x = (1 - (ζ n) ^ a) }
  ) := by sorry

def S : Set ℕ := {y: ℕ | 1<y ∧ y≤ (n/2) }
lemma principal {x:ℂˣ } {k:ℤ}   (h1: x∈ Vₙ p n ) (h2: (x.val) ∈ Z): ∃ k l: ℤ , ∃ c : (ℕ -> ℤ ), x=(-1)^k*(ζ n)^l* ∏ a in (S n), (η n a)^(c a)
:=by  sorry
