import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Union
import Mathlib.Data.Sum.Order

namespace ClauseStuff

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

-- filters out everything that isn't minimal
-- aka simplifieds stuff like (x AND y) OR x into just x
@[grind]
def clauseAntichain (s : Finset (Clause n)) : Finset (Clause n) :=
  s.filter (fun x => ∀ y ∈ s, y ≤ x → x = y)

@[grind]
def clauseProduct (x y : Finset (Clause n)) : Finset (Clause n) :=
  x.biUnion (fun xx => y.image (fun yy => Clause.mk (xx.pos ∪ yy.pos) (xx.neg ∪ yy.neg)))

scoped infixl:70 " ⊗ " => clauseProduct
scoped notation:max "⌊" s "⌋" => clauseAntichain s

@[simp]
lemma clauseProduct_assoc (a b c : Finset (Clause n)) : (a ⊗ b) ⊗ c = a ⊗ (b ⊗ c) := by
  ext x
  unfold clauseProduct
  simp only [Finset.mem_biUnion, Finset.mem_image, exists_exists_and_exists_and_eq_and, Finset.union_assoc]

@[simp]
lemma clauseProduct_one_left (A : Finset (Clause n)) :
    {Clause.mk ∅ ∅} ⊗ A = A := by
  ext x
  simp only [clauseProduct, Finset.singleton_biUnion, Finset.empty_union, Finset.image_id']

@[simp]
lemma clauseProduct_one_right (A : Finset (Clause n)) :
    A ⊗ {Clause.mk ∅ ∅} = A := by
  ext x
  simp only [clauseProduct, Finset.image_singleton, Finset.union_empty, Finset.mem_biUnion, Finset.mem_singleton, exists_eq_right']

@[simp]
lemma clauseProduct_comm (A B : Finset (Clause n)) :
    A ⊗ B = B ⊗ A := by
  ext x
  simp only [clauseProduct, Finset.mem_biUnion, Finset.mem_image]
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨b, hb, a, ha, by ext <;> simp only [Finset.union_comm, Finset.mem_union]⟩
  · rintro ⟨b, hb, a, ha, rfl⟩
    exact ⟨a, ha, b, hb, by ext <;> simp only [Finset.union_comm, Finset.mem_union]⟩

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
lemma clauseAntichain_smaller : ⌊ s ⌋ ⊆ s := by
  grind only [= Finset.subset_iff, clauseAntichain, = Finset.mem_filter]

lemma exists_antichain_le (s : Finset (Clause n)) (x : Clause n) (hx : x ∈ s) : ∃ y ∈ clauseAntichain s, y ≤ x := by
  obtain ⟨y, hys, hle, hmin⟩ := Clause.exists_minimal_le s x hx
  use y
  grind only [clauseAntichain, = Finset.mem_filter]

lemma clauseAntichain_eq_of_dominate (A B : Finset (Clause n))
    (h_sub : A ⊆ B)
    (h_dom : ∀ b ∈ B, ∃ a ∈ A, a ≤ b) :
    ⌊ A ⌋ = ⌊ B ⌋ := by
  ext x
  repeat constructor <;> grind only [= Finset.subset_iff, clauseAntichain, = Finset.mem_filter]

lemma clauseProduct_subset_left (A B C : Finset (Clause n)) (h : A ⊆ B) :
    A ⊗ C ⊆ B ⊗ C := by
  grind only [= Finset.subset_iff, clauseProduct, = Finset.mem_biUnion]

lemma clauseProduct_dominate_left (A C : Finset (Clause n)) :
    ∀ p ∈ A ⊗ C, ∃ p' ∈ ⌊ A ⌋ ⊗ C, p' ≤ p := by
  intros p hp
  unfold clauseProduct at hp ⊢
  simp only [Finset.mem_biUnion, Finset.mem_image] at hp ⊢
  rcases hp with ⟨a, ha, c, hc, rfl⟩
  obtain ⟨a_min, ha_min, h_le⟩ := exists_antichain_le A a ha
  use Clause.mk (a_min.pos ∪ c.pos) (a_min.neg ∪ c.neg)
  constructor
  · exact ⟨a_min, ha_min, c, hc, rfl⟩
  · exact Clause.union_le_union_right a_min a c h_le

@[simp]
lemma clauseAntichain_clauseProduct_left (a b : Finset (Clause n)) : clauseAntichain (clauseProduct (clauseAntichain a) b) = clauseAntichain (clauseProduct a b) := by
  apply clauseAntichain_eq_of_dominate
  · exact clauseProduct_subset_left _ _ _ clauseAntichain_smaller
  · exact clauseProduct_dominate_left a b

@[simp]
lemma Clause.union_le_union_left (a b c : Clause n) (h : b ≤ c) : Clause.mk (a.pos ∪ b.pos) (a.neg ∪ b.neg) ≤ Clause.mk (a.pos ∪ c.pos) (a.neg ∪ c.neg) :=
  ⟨Finset.union_subset_union (fun _ hx => hx) h.1, Finset.union_subset_union (fun _ hx => hx) h.2⟩

lemma clauseProduct_subset_right (A B C : Finset (Clause n)) (h : B ⊆ C) :
    A ⊗ B ⊆ A ⊗ C := by
  intro p hp
  unfold clauseProduct at hp ⊢
  simp only [Finset.mem_biUnion, Finset.mem_image] at hp ⊢
  rcases hp with ⟨a, ha, b, hb, rfl⟩
  have hc : b ∈ C := h hb
  exact ⟨a, ha, b, hc, rfl⟩

lemma clauseProduct_dominate_right (A C : Finset (Clause n)) :
    ∀ p ∈ A ⊗ C, ∃ p' ∈ A ⊗ ⌊ C ⌋, p' ≤ p := by
  intros p hp
  unfold clauseProduct at hp ⊢
  simp only [Finset.mem_biUnion, Finset.mem_image] at hp ⊢
  rcases hp with ⟨a, ha, c, hc, rfl⟩
  obtain ⟨c_min, hc_min, h_le⟩ := exists_antichain_le C c hc
  use Clause.mk (a.pos ∪ c_min.pos) (a.neg ∪ c_min.neg)
  constructor
  · exact ⟨a, ha, c_min, hc_min, rfl⟩
  · exact Clause.union_le_union_left a c_min c h_le

@[simp]
lemma clauseAntichain_clauseProduct_right (a b : Finset (Clause n)) : clauseAntichain (clauseProduct a (clauseAntichain b)) = clauseAntichain (clauseProduct a b) := by
  apply clauseAntichain_eq_of_dominate
  · exact clauseProduct_subset_right _ _ _ clauseAntichain_smaller
  · exact clauseProduct_dominate_right a b

@[simp]
lemma clauseAntichain_eq_self {s : Finset (Clause n)} (h : ∀ x ∈ s, ∀ y ∈ s, x ≤ y → x = y) : clauseAntichain s = s := by
  grind only [clauseAntichain, = Finset.mem_filter]

def Clause.toLex (c : Clause n) : List (Fin n ⊕ Fin n) :=
  (c.pos.sort (· ≤ ·)).map Sum.inl ++ (c.neg.sort (· ≤ ·)).map Sum.inr

def clauseLexLe (x y : Clause n) : Prop := x.toLex ≤ y.toLex

end ClauseStuff
