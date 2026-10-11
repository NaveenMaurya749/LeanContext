/-
# Inductive Types in Lean

An inductive type is described via a number of constructors
-/

inductive MyNat where
| zero : MyNat
| succ : MyNat → MyNat

#print MyNat
#print MyNat.rec

def iterSucc : Nat → Nat
| 0     => 0
| m + 1 => Nat.succ (iterSucc m)

theorem nat_is_iterated_succ (n : Nat) :
    n = 0 ∨ ∃ m : Nat, n = iterSucc m := by
  induction n with
  | zero =>
      exact Or.inl rfl
  | succ n ih =>
      rcases ih with h | ⟨m, hm⟩
      · right
        exact ⟨1, by rw [iterSucc]; exact congrArg Nat.succ h⟩
      · right
        exact ⟨m + 1, by rw [iterSucc]; exact congrArg Nat.succ hm⟩


#print Empty

#print Unit

-- The Empty (0) Type having no constructors
inductive MyEmpty where

#print MyEmpty
#print MyEmpty.rec 

-- The Empty type has the `universal property` that for any α : Type, 
-- we have a canonical map Empty → α

def imp {α : Type} : Empty → α := by
  intro empty
  exact Empty.rec (fun _ ↦ α) empty

-- The Unit (1) Type, which is the contractible type
inductive MyUnit where
| unit : MyUnit

#print MyUnit

-- The Unit type has the `universal property` that for any α : Type, 
-- we have a canonical map α → Unit
-- Canonical in the sense that this map arises from the internal construction of
-- the unit type itself, and does not depend on the type α : Type

def universal_property_unit (α : Type) : α → MyUnit := 
  fun _ ↦ MyUnit.unit

-- The Boolean (2) Type, given by constructors 0_2 : 2 and 1_2 : 2
inductive MyBool where
| zero : MyBool
| one  : MyBool

#print MyBool
/--
# Product Type

Given types α : Type u and β : Type v, we can form the product type
α × β : Type (max u v), which is `defined` as follows:

- An element of α × β is specified by an element of α and an element of β
- To prove a property for all z : α × β, it suffices to prove the property 

# Coproduct Type

Given types α : Type u and β : Type v, we can form their coproduct type
α + β : Type (max u v), which is defined as follows:

- An element of α + β is either an element of α or an element of β
- To prove a property for all z : α + β, it suffices to prove the property
  separately for the cases restricting to α or β respectively 
--/

-- We can define our own Coproduct
inductive Coprod.{u} (α β : Sort u) where
| inl : α → Coprod α β 
| inr : β → Coprod α β 

#print Coprod
#print Coprod.rec

def Coprod.ind.{u,v} {α β : Sort u} 
  (Property : Coprod α β → Sort v) :
  ((a : α) → Property (Coprod.inl a)) →  
  ((b : β) → Property (Coprod.inr b)) → 
  ((z : Coprod α β) → Property z) := by
  intro left right z
  match z with
  | inl a => exact left a 
  | inr b => exact right b

