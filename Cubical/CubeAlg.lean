import Mathlib

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

-- this is the normalized implementation
-- thus no need for a quotient
-- downstream should use this

section

@[ext, grind]
structure Clause (n : ℕ) where
  pos : Finset (Fin n)
  neg : Finset (Fin n)
  deriving DecidableEq

instance : PartialOrder (Clause n) where
  le := fun x y => x.pos ⊆ y.pos ∧ x.neg ⊆ y.neg
  le_refl := by grind only [= Finset.subset_iff]
  le_trans := by grind only [= Finset.subset_iff]
  le_antisymm := by grind [Finset.Subset.antisymm]

instance (x y : Clause n) : Decidable (x ≤ y) :=
  inferInstanceAs (Decidable (x.pos ⊆ y.pos ∧ x.neg ⊆ y.neg))

def Clause.weight (c : Clause n) : ℕ := c.pos.card + c.neg.card

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

-- filters out everything that isn't minimal
-- aka simplifieds stuff like (x AND y) OR x into just x
@[grind]
def clauseAntichain (s : Finset (Clause n)) : Finset (Clause n) :=
  s.filter (fun x => ∀ y ∈ s, y ≤ x → x = y)

@[grind]
def clauseProduct (x y : Finset (Clause n)) : Finset (Clause n) :=
  x.biUnion (fun xx => y.image (fun yy => Clause.mk (xx.pos ∪ yy.pos) (xx.neg ∪ yy.neg)))

@[simp]
lemma clauseProduct_assoc (a b c : Finset (Clause n)) : clauseProduct (clauseProduct a b) c = clauseProduct a (clauseProduct b c) := by
  ext x
  unfold clauseProduct
  simp only [Finset.mem_biUnion, Finset.mem_image, exists_exists_and_exists_and_eq_and, Finset.union_assoc]

@[simp]
lemma Clause.union_le_union_right (a b c : Clause n) (h : a ≤ b) : Clause.mk (a.pos ∪ c.pos) (a.neg ∪ c.neg) ≤ Clause.mk (b.pos ∪ c.pos) (b.neg ∪ c.neg) :=
  ⟨Finset.union_subset_union h.1 (fun _ hx => hx), Finset.union_subset_union h.2 (fun _ hx => hx)⟩

lemma Clause.exists_minimal_le (s : Finset (Clause n)) (x : Clause n) (hx : x ∈ s) : ∃ y ∈ s, y ≤ x ∧ ∀ z ∈ s, z ≤ y → y = z := by
  let f : Clause n → ℕ := fun c => c.pos.card + c.neg.card
  let S := s.filter (· ≤ x)
  have hS_nonempty : S.Nonempty := ⟨x, Finset.mem_filter.mpr ⟨hx, le_refl x⟩⟩
  obtain ⟨y, hyS, hy_min⟩ := S.exists_min_image f hS_nonempty
  rw [Finset.mem_filter] at hyS
  refine ⟨y, hyS.1, hyS.2, fun z hzs hzy => ?_⟩
  have hz_le_x : z ≤ x := le_trans hzy hyS.2
  have hzS : z ∈ S := Finset.mem_filter.mpr ⟨hzs, hz_le_x⟩
  have h_f_le : y.pos.card + y.neg.card ≤ z.pos.card + z.neg.card := hy_min z hzS
  have h_pos_sub : z.pos ⊆ y.pos := hzy.1
  have h_neg_sub : z.neg ⊆ y.neg := hzy.2
  have h_pos_card : z.pos.card ≤ y.pos.card := Finset.card_le_card h_pos_sub
  have h_neg_card : z.neg.card ≤ y.neg.card := Finset.card_le_card h_neg_sub
  have h_pos_eq : y.pos.card ≤ z.pos.card := by grind only
  have h_neg_eq : y.neg.card ≤ z.neg.card := by grind only
  ext
  repeat constructor <;> grind only [Finset.eq_of_subset_of_card_le]

@[simp]
lemma clauseAntichain_smaller : clauseAntichain s ⊆ s := by
  grind only [= Finset.subset_iff, clauseAntichain, = Finset.mem_filter]

lemma exists_antichain_le (s : Finset (Clause n)) (x : Clause n) (hx : x ∈ s) : ∃ y ∈ clauseAntichain s, y ≤ x := by
  obtain ⟨y, hys, hle, hmin⟩ := Clause.exists_minimal_le s x hx
  use y
  grind only [clauseAntichain, = Finset.mem_filter]

@[simp]
lemma clauseAntichain_clauseProduct_left (a b : Finset (Clause n)) : clauseAntichain (clauseProduct (clauseAntichain a) b) = clauseAntichain (clauseProduct a b) := by
  ext x
  simp only [clauseAntichain, Finset.mem_filter]
  constructor
  · rintro ⟨hx, hmin⟩
    have hx_in : x ∈ clauseProduct a b := by
      simp only [clauseProduct, Finset.mem_biUnion, Finset.mem_image] at hx ⊢
      rcases hx with ⟨ca, hca, cb, hcb, rfl⟩
      exact ⟨ca, clauseAntichain_smaller hca, cb, hcb, rfl⟩
    refine ⟨hx_in, fun y hy hyx => ?_⟩
    have hy_copy := hy
    simp only [clauseProduct, Finset.mem_biUnion, Finset.mem_image] at hy_copy
    rcases hy_copy with ⟨ya, hya, yb, hyb, rfl⟩
    obtain ⟨ya_min, hya_min, hya_le⟩ := exists_antichain_le a ya hya
    have h_y_min_in : Clause.mk (ya_min.pos ∪ yb.pos) (ya_min.neg ∪ yb.neg) ∈ clauseProduct (clauseAntichain a) b := by
      simp only [clauseProduct, Finset.mem_biUnion, Finset.mem_image]
      exact ⟨ya_min, hya_min, yb, hyb, rfl⟩
    have h_y_min_le_y : Clause.mk (ya_min.pos ∪ yb.pos) (ya_min.neg ∪ yb.neg) ≤ Clause.mk (ya.pos ∪ yb.pos) (ya.neg ∪ yb.neg) :=
      Clause.union_le_union_right ya_min ya yb hya_le
    have h_y_min_le_x : Clause.mk (ya_min.pos ∪ yb.pos) (ya_min.neg ∪ yb.neg) ≤ x := le_trans h_y_min_le_y hyx
    have h_eq := hmin _ h_y_min_in h_y_min_le_x
    have h_y_le_y_min : Clause.mk (ya.pos ∪ yb.pos) (ya.neg ∪ yb.neg) ≤ Clause.mk (ya_min.pos ∪ yb.pos) (ya_min.neg ∪ yb.neg) := by grind only
      -- rw [h_eq]
      -- exact hyx
    grind only
  · rintro ⟨hx, hmin⟩
    have hx_copy := hx
    simp only [clauseProduct, Finset.mem_biUnion, Finset.mem_image] at hx_copy
    rcases hx_copy with ⟨ca, hca, cb, hcb, rfl⟩
    obtain ⟨ca_min, hca_min, hca_le⟩ := exists_antichain_le a ca hca
    have h_min_in : Clause.mk (ca_min.pos ∪ cb.pos) (ca_min.neg ∪ cb.neg) ∈ clauseProduct a b := by
      simp only [clauseProduct, Finset.mem_biUnion, Finset.mem_image]
      exact ⟨ca_min, clauseAntichain_smaller hca_min, cb, hcb, rfl⟩
    have h_le_x : Clause.mk (ca_min.pos ∪ cb.pos) (ca_min.neg ∪ cb.neg) ≤ Clause.mk (ca.pos ∪ cb.pos) (ca.neg ∪ cb.neg) :=
      Clause.union_le_union_right ca_min ca cb hca_le
    have h_eq := hmin _ h_min_in h_le_x
    have hx_anti : Clause.mk (ca.pos ∪ cb.pos) (ca.neg ∪ cb.neg) ∈ clauseProduct (clauseAntichain a) b := by
      -- rw [← h_eq]
      simp only [clauseProduct, Finset.mem_biUnion, Finset.mem_image]
      grind only
    refine ⟨hx_anti, fun y hy hyx => ?_⟩
    have hy_prod : y ∈ clauseProduct a b := by
      have hy_copy := hy
      simp only [clauseProduct, Finset.mem_biUnion, Finset.mem_image] at hy_copy
      rcases hy_copy with ⟨ya, hya, yb, hyb, rfl⟩
      simp only [clauseProduct, Finset.mem_biUnion, Finset.mem_image]
      exact ⟨ya, clauseAntichain_smaller hya, yb, hyb, rfl⟩
    exact hmin y hy_prod hyx

@[simp]
lemma Clause.union_le_union_left (a b c : Clause n) (h : b ≤ c) : Clause.mk (a.pos ∪ b.pos) (a.neg ∪ b.neg) ≤ Clause.mk (a.pos ∪ c.pos) (a.neg ∪ c.neg) :=
  ⟨Finset.union_subset_union (fun _ hx => hx) h.1, Finset.union_subset_union (fun _ hx => hx) h.2⟩

@[simp]
lemma clauseAntichain_clauseProduct_right (a b : Finset (Clause n)) : clauseAntichain (clauseProduct a (clauseAntichain b)) = clauseAntichain (clauseProduct a b) := by
  ext x
  simp only [clauseAntichain, Finset.mem_filter]
  constructor
  · rintro ⟨hx, hmin⟩
    have hx_in : x ∈ clauseProduct a b := by
      simp only [clauseProduct, Finset.mem_biUnion, Finset.mem_image] at hx ⊢
      rcases hx with ⟨ca, hca, cb, hcb, rfl⟩
      exact ⟨ca, hca, cb, clauseAntichain_smaller hcb, rfl⟩
    refine ⟨hx_in, fun y hy hyx => ?_⟩
    have hy_copy := hy
    simp only [clauseProduct, Finset.mem_biUnion, Finset.mem_image] at hy_copy
    rcases hy_copy with ⟨ya, hya, yb, hyb, rfl⟩
    obtain ⟨yb_min, hyb_min, hyb_le⟩ := exists_antichain_le b yb hyb
    have h_y_min_in : Clause.mk (ya.pos ∪ yb_min.pos) (ya.neg ∪ yb_min.neg) ∈ clauseProduct a (clauseAntichain b) := by
      simp only [clauseProduct, Finset.mem_biUnion, Finset.mem_image]
      exact ⟨ya, hya, yb_min, hyb_min, rfl⟩
    have h_y_min_le_y : Clause.mk (ya.pos ∪ yb_min.pos) (ya.neg ∪ yb_min.neg) ≤ Clause.mk (ya.pos ∪ yb.pos) (ya.neg ∪ yb.neg) :=
      Clause.union_le_union_left ya yb_min yb hyb_le
    have h_y_min_le_x : Clause.mk (ya.pos ∪ yb_min.pos) (ya.neg ∪ yb_min.neg) ≤ x := le_trans h_y_min_le_y hyx
    have h_eq := hmin _ h_y_min_in h_y_min_le_x
    have h_y_le_y_min : Clause.mk (ya.pos ∪ yb.pos) (ya.neg ∪ yb.neg) ≤ Clause.mk (ya.pos ∪ yb_min.pos) (ya.neg ∪ yb_min.neg) := by grind only
    grind only
  · rintro ⟨hx, hmin⟩
    have hx_copy := hx
    simp only [clauseProduct, Finset.mem_biUnion, Finset.mem_image] at hx_copy
    rcases hx_copy with ⟨ca, hca, cb, hcb, rfl⟩
    obtain ⟨cb_min, hcb_min, hcb_le⟩ := exists_antichain_le b cb hcb
    have h_min_in : Clause.mk (ca.pos ∪ cb_min.pos) (ca.neg ∪ cb_min.neg) ∈ clauseProduct a b := by
      simp only [clauseProduct, Finset.mem_biUnion, Finset.mem_image]
      exact ⟨ca, hca, cb_min, clauseAntichain_smaller hcb_min, rfl⟩
    have h_le_x : Clause.mk (ca.pos ∪ cb_min.pos) (ca.neg ∪ cb_min.neg) ≤ Clause.mk (ca.pos ∪ cb.pos) (ca.neg ∪ cb.neg) :=
      Clause.union_le_union_left ca cb_min cb hcb_le
    have h_eq := hmin _ h_min_in h_le_x
    have hx_anti : Clause.mk (ca.pos ∪ cb.pos) (ca.neg ∪ cb.neg) ∈ clauseProduct a (clauseAntichain b) := by
      simp only [clauseProduct, Finset.mem_biUnion, Finset.mem_image]
      grind only
    refine ⟨hx_anti, fun y hy hyx => ?_⟩
    have hy_prod : y ∈ clauseProduct a b := by
      have hy_copy := hy
      simp only [clauseProduct, Finset.mem_biUnion, Finset.mem_image] at hy_copy
      rcases hy_copy with ⟨ya, hya, yb, hyb, rfl⟩
      simp only [clauseProduct, Finset.mem_biUnion, Finset.mem_image]
      exact ⟨ya, hya, yb, clauseAntichain_smaller hyb, rfl⟩
    exact hmin y hy_prod hyx


@[grind]
def dmnMeet (x y : DMN n) : DMN n :=
  DMN.mk (clauseAntichain (clauseProduct x.clauses y.clauses)) (by grind only [clauseAntichain, = Finset.mem_filter])

@[grind]
def dmnTrue : DMN n := DMN.mk (clauseAntichain {Clause.mk ∅ ∅}) (by grind only [clauseAntichain, = Finset.mem_filter, = Finset.mem_singleton])

@[simp]
lemma dmnTrue_clauses : (dmnTrue : DMN n).clauses = {Clause.mk ∅ ∅} := by
  grind only [dmnTrue, clauseAntichain, = Finset.mem_filter, = Finset.mem_singleton]

@[simp]
lemma clauseAntichain_eq_self {s : Finset (Clause n)} (h : ∀ x ∈ s, ∀ y ∈ s, x ≤ y → x = y) : clauseAntichain s = s := by
  grind only [clauseAntichain, = Finset.mem_filter]

def Clause.toLex (c : Clause n) : List (Fin n ⊕ Fin n) :=
  (c.pos.sort (· ≤ ·)).map Sum.inl ++ (c.neg.sort (· ≤ ·)).map Sum.inr

def clauseLexLe (x y : Clause n) : Prop := x.toLex ≤ y.toLex

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

end

def toNF (t : DM n) : DMN n :=
  match t with
  | .zero => DMN.mk ∅ (fun _ h => by contradiction)
  | .one => DMN.mk
    {Clause.mk ∅ ∅}
    (fun x hx y hy p => by simp at hx hy; grind only)
  | .var n => DMN.mk
    {Clause.mk {n} ∅}
    (by simp only [Finset.mem_singleton, forall_eq, Std.le_refl, imp_self])
  | .meet x y => dmnMeet (toNF x) (toNF y)
  | .join x y => dmnJoin (toNF x) (toNF y)
  | .inv t => dmnInv (toNF t)
