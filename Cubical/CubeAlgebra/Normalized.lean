import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Union
import Mathlib.Data.Sum.Order

import Cubical.CubeAlgebra.Normalized.Clause

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

@[grind]
def dmnMeet (x y : DMN n) : DMN n :=
  DMN.mk (clauseAntichain (clauseProduct x.clauses y.clauses)) (by grind only [clauseAntichain, = Finset.mem_filter])

@[grind]
def dmnTrue : DMN n := DMN.mk (clauseAntichain {Clause.mk ∅ ∅}) (by grind only [clauseAntichain, = Finset.mem_filter, = Finset.mem_singleton])

@[simp]
lemma dmnTrue_clauses : (dmnTrue : DMN n).clauses = {Clause.mk ∅ ∅} := by
  grind only [dmnTrue, clauseAntichain, = Finset.mem_filter, = Finset.mem_singleton]

instance : CommMonoid (DMN n) where
  one := dmnTrue
  mul := dmnMeet

  one_mul := by
    intros a
    ext x
    change x ∈ (dmnMeet dmnTrue a).clauses ↔ x ∈ a.clauses
    unfold dmnMeet clauseAntichain clauseProduct
    simp only [dmnTrue_clauses, Finset.singleton_biUnion, Finset.empty_union, Finset.image_id', Finset.mem_filter, and_iff_left_iff_imp]
    grind only

  mul_one := by
    intros a
    ext x
    change x ∈ (dmnMeet a dmnTrue).clauses ↔ x ∈ a.clauses
    unfold dmnMeet clauseAntichain clauseProduct
    simp only [dmnTrue_clauses, Finset.image_singleton, Finset.union_empty, Finset.mem_biUnion, Finset.mem_singleton, exists_eq_right', Finset.mem_filter, and_iff_left_iff_imp]
    grind only

  mul_assoc := by
    intros a b c
    change dmnMeet (dmnMeet a b) c = dmnMeet a (dmnMeet b c)
    ext x
    unfold dmnMeet
    simp only [clauseAntichain_clauseProduct_left, clauseProduct_assoc, clauseAntichain_clauseProduct_right]

  mul_comm := by
    intros a b
    change dmnMeet a b = dmnMeet b a
    ext
    unfold dmnMeet clauseProduct
    simp only
    grind

def dmnJoin (x y : DMN n) : DMN n :=
  let unioned := x.clauses ∪ y.clauses
  DMN.mk (clauseAntichain unioned) (by grind only [clauseAntichain, = Finset.mem_filter])

-- TODO: implement a more efficient data structure that isn't O(2^n) :skull:
def clauseInv (c : Clause n) : DMN n :=
  let pos_inv := c.pos.image (fun p => Clause.mk ∅ {p})
  let neg_inv := c.neg.image (fun n => Clause.mk {n} ∅)
  DMN.mk (clauseAntichain (pos_inv ∪ neg_inv)) (by grind only [clauseAntichain, = Finset.mem_filter])

def dmnInv (x : DMN n) : DMN n := x.clauses.prod clauseInv
