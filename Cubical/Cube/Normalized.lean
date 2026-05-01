import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Union
import Mathlib.Data.Sum.Order

import Cubical.Cube.Normalized.Clause

namespace NormalizedStuff
open ClauseStuff

-- this is the normalized implementation
-- thus no need for a quotient
-- downstream should use this

@[ext, grind]
structure DMN (n : ℕ) where
  clauses : Finset (Clause n)
  antichain : ∀ x ∈ clauses, ∀ y ∈ clauses, x ≤ y → x = y
  deriving DecidableEq

instance : PartialOrder (DMN n) where
  le := fun x y => ∀ cx ∈ x.clauses, ∃ cy ∈ y.clauses, cy ≤ cx
  le_refl := by grind only
  le_trans := by grind only
  le_antisymm := by grind only [DMN.ext_iff]

@[simp]
def dmnMeet (x y : DMN n) : DMN n :=
  DMN.mk ⌊ x.clauses ⊗ y.clauses ⌋ (by grind only [clauseAntichain, = Finset.mem_filter])

@[simp]
def dmnTrue : DMN n := DMN.mk ⌊ {Clause.mk ∅ ∅} ⌋ (by grind only [clauseAntichain, = Finset.mem_filter, = Finset.mem_singleton])

@[simp]
def dmnFalse : DMN n := DMN.mk ∅ (fun _ h => by contradiction)

@[simp]
lemma dmnTrue_clauses : (dmnTrue : DMN n).clauses = {Clause.mk ∅ ∅} := by
  grind only [dmnTrue, clauseAntichain, = Finset.mem_filter, = Finset.mem_singleton]

@[simp]
lemma DMN.antichain_self (x : DMN n) : ⌊ x.clauses ⌋ = x.clauses := clauseAntichain_eq_self x.antichain

instance : CommMonoid (DMN n) where
  one := dmnTrue
  mul := dmnMeet

  one_mul := by
    intro a
    change dmnMeet dmnTrue a = a
    ext
    simp only [dmnMeet, dmnTrue, Finset.mem_singleton, forall_eq, Std.le_refl, imp_self, clauseAntichain_eq_self, clauseProduct_comm, clauseProduct_one_right, DMN.antichain_self]

  mul_one := by
    intro a
    change dmnMeet a dmnTrue = a
    ext
    simp only [dmnMeet, dmnTrue, Finset.mem_singleton, forall_eq, Std.le_refl, imp_self, clauseAntichain_eq_self, clauseProduct_one_right, DMN.antichain_self]

  mul_assoc := by
    intros a b c
    change dmnMeet (dmnMeet a b) c = dmnMeet a (dmnMeet b c)
    ext
    simp only [dmnMeet, clauseAntichain_clauseProduct_left, clauseProduct_assoc, clauseAntichain_clauseProduct_right]

  mul_comm := by
    intros a b
    change dmnMeet a b = dmnMeet b a
    ext
    simp only [dmnMeet, clauseProduct_comm]

def dmnJoin (x y : DMN n) : DMN n :=
  let unioned := x.clauses ∪ y.clauses
  DMN.mk ⌊ unioned ⌋ (by grind only [clauseAntichain, = Finset.mem_filter])

scoped infixl:80 " ⊔ " => dmnJoin

@[simp]
lemma dmnJoin_assoc (a b c : DMN n) : (a ⊔ b) ⊔ c = a ⊔ (b ⊔ c) := by
  ext
  unfold dmnJoin
  simp only [clauseAntichain_union_left, clauseAntichain_union_right, Finset.union_assoc]

instance : AddCommMonoid (DMN n) where
  add := dmnJoin
  zero := dmnFalse
  nsmul := by sorry

  add_assoc := dmnJoin_assoc
  zero_add := by sorry
  add_zero := by sorry
  add_comm := by sorry
  nsmul_zero := by sorry
  nsmul_succ := by sorry

-- TODO: implement a more efficient data structure that isn't O(2^n) :skull:
def clauseInv (c : Clause n) : DMN n :=
  let pos_inv := c.pos.image (fun p => Clause.mk ∅ {p})
  let neg_inv := c.neg.image (fun n => Clause.mk {n} ∅)
  DMN.mk ⌊pos_inv ∪ neg_inv ⌋ (by grind only [clauseAntichain, = Finset.mem_filter])

def dmnInv (x : DMN n) : DMN n := x.clauses.prod clauseInv

def dmnEval (f : Fin n → DMN n) (x : DMN n) : DMN n :=
  x.clauses.sum fun c => (c.pos.prod f) * (c.neg.prod fun i => dmnInv (f i))

end NormalizedStuff
