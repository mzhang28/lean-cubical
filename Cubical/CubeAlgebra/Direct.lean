import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Union
import Mathlib.Data.Sum.Order

-- this is the direct-style implementation
-- this needs to be quotiented by the equivalence relation (below)
-- which spells out all the demorgan laws
section

inductive DM (n : ℕ) where
  | zero : DM n
  | one : DM n
  | var : Fin n → DM n
  | meet : DM n → DM n → DM n
  | join : DM n → DM n → DM n
  | inv : DM n → DM n

inductive DMRel : DM n → DM n → Prop where
  | refl (x : DM n) : DMRel x x
  | symm {x y : DM n} : DMRel x y → DMRel y x
  | trans {x y z : DM n} : DMRel x y → DMRel y z → DMRel x z

def DMRelEquiv : @Equivalence (DM n) DMRel := {
  refl := DMRel.refl,
  symm := DMRel.symm,
  trans := DMRel.trans,
}

instance DMSetoid : Setoid (DM n) where
  r := DMRel
  iseqv := DMRelEquiv

end section


-- def toNF (t : DM n) : DMN n :=
--   match t with
--   | .zero => DMN.mk ∅ (fun _ h => by contradiction)
--   | .one => DMN.mk
--     {Clause.mk ∅ ∅}
--     (fun x hx y hy p => by simp at hx hy; grind only)
--   | .var n => DMN.mk
--     {Clause.mk {n} ∅}
--     (by simp only [Finset.mem_singleton, forall_eq, Std.le_refl, imp_self])
--   | .meet x y => dmnMeet (toNF x) (toNF y)
--   | .join x y => dmnJoin (toNF x) (toNF y)
--   | .inv t => dmnInv (toNF t)
