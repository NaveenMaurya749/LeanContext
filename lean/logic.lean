/-
# Logic in Lean  

Unlike ZFC set theory, which assumes first-order logic as a prerequisite,
the logic of type theory is built alonside the rest of the foundational
system.

Lean uses a version of 'dependently-types lambda calculus'
for its logic
-/

-- `Prop` is a special class in Lean whose terms are 'mere propositions'
#check Prop
#check Sort
#check Sort 4

-- Terms of `Prop` are propositions.
def one_plus_one_two    : Prop := 1 + 1 = 2
def two_plus_three_nine : Prop := 2 + 3 = 9
def sum_equal_thrice    : Prop := ∀ n : Nat, n + n = 3*n 
def Nat.assoc           : Prop := ∀ m n k : Nat, (m + n) + k = m + (n + k) 

#check one_plus_one_two
#check two_plus_three_nine
#check sum_equal_thrice
#check Nat.assoc

-- Function Types logically encode implication 
def MyImplication (n : Nat) : Prop := n = 2 → n * n = n + n

theorem proof_of_my_implication (n : Nat) : MyImplication n := by
  intro h
  rw[h]

def m := 1 + 1
theorem proof_of_m_equals_2 : m = 2 := rfl

#check proof_of_my_implication m 
#check proof_of_my_implication m proof_of_m_equals_2

-- `False` encodes False, `True` encodes True
#print False 
#print True 

universe u v

-- False is initial
theorem falsity_to (p : Prop) : False → p := by
  intro h
  exact False.elim h 

-- True is terminal 
theorem to_truth (p : Prop) : p → True := by 
  intro h 
  exact True.intro 

-- We can prove facts about Logic
-- Modus Ponens
theorem modus_ponens (p q : Prop) : p → (p → q) → q := by
  intro a f 
  exact f a

-- A proposition and its negation imply contradiction
theorem contradiction (P : Prop) : P → ¬ P → False := by
  intro a f 
  exact f a 

-- Law of Excluded Middle is not assumed by default
def LEM := (p : Prop) → p ∨ ¬ p  
#print LEM

theorem classical_proof_LEM : LEM := by
  exact Classical.em

theorem lem_implies_dne
    (lem : LEM)
    (p : Prop) : ¬¬p → p := by
  intro h
  cases lem p with
  | inl hp => exact hp
  | inr hnp => exact False.elim (h hnp)

-- De Morgan's Laws
theorem de_morgan_not_or (p q : Prop) :
    ¬ (p ∨ q) ↔ (¬ p ∧ ¬ q) := by
  constructor
  · intro h
    constructor
    · intro hp
      exact h (Or.inl hp)
    · intro hq
      exact h (Or.inr hq)
  · intro h hpq
    cases hpq with
    | inl hp => exact h.1 hp
    | inr hq => exact h.2 hq

-- Not provable by default 
def de_morgan_not_and :=
    (p q : Prop) → (¬ (p ∧ q) ↔ ¬p ∨ ¬q)

/-
# Equalities: Definitional & Propositional

Lean maintains two distinct notions of equality.
- `Definitional Equality`, an equality of terms within the setup of 
the foundational system itself.
(Stronger)

- `Propositional Equality`, an equality of terms *proven*
from theorems in the math defined in the system. 
(Weaker, but more important to the math)
-/

example (n : Nat) : n + 0 = n := by
  omega

