/-
# Terms and Types in Lean

  Objects in Lean are organized as `Types` and `Terms`.
  Very vaguely speaking, a type is a container for terms.

  A mathematical theory, on paper, consists of various objects
  which are defined in relation to each other,
  and statements/theorems about them. 

  In Lean, any object is a `term` and each `term` has a unique
  `type` associated to it.
  Such a relationship is denoted as `a : α` which stands for 
  `a` is a term of type `α`.
  We also say `a` is an instance of the type `α`.

-/

def MyNumber : Nat := 14123489

-- The `check` command tests the type of a given term
#check MyNumber
#print MyNumber 

-- `Nat` is the type of Natural Numbers
#print Nat

-- Interestingly, `2 + 3 = 5` may be treated as a type.
-- We will see later what this means.
def MyFoo : 2 + 3 = 5 := rfl

#check MyFoo

/-
# Type Universes

Types are organized into an infinite cumulative heirarchy

`Type = Type 0 ⊆ Type 1 ⊆ Type 2 ⊆ ⋯ ⊆ Type n ⊆ ⋯ `

-/

#check 0
-- Outputs `Nat` since `0` is a term of type `Nat`
#check 42 
-- Outputs `Nat` since `42` is a term of type `Nat`

-- What if we check the type of Nat?
#check Nat
-- Outputs `Type` since `Nat` is a type

#check Type

#check Type 1

#check Type 2

#check Type 32
