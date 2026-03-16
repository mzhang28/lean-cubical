import Mathlib
import Cubical.CubeAlg

open CategoryTheory

-----------------------------------------------------------------------
-- cube category

@[ext]
structure CubeHom (n1 n2 : ℕ) where
  map : Fin n1 → Sum (Fin n2) Bool
  inj : ∀ (x y : Fin n1), (map x = map y) → (x = y) ∨ (map x).isRight

@[grind]
def idCubeHom : CubeHom n n := {
  map := fun x => .inl x
  inj := fun _ _ => by simp
}

@[grind]
def compCubeHom (f : CubeHom n1 n2) (g : CubeHom n2 n3) : CubeHom n1 n3 := {
  map := fun x => match f.map x with
    | .inl y => g.map y
    | .inr z => .inr z
  inj := fun x y p => by
    cases hx : f.map x with
    | inr z => simp only [Sum.isRight_inr, or_true]
    | inl fx =>
      cases hy : f.map y with
      | inr z =>
        simp [hx, hy] at p
        exact .inr (by grind only [= Sum.isRight_inr])
      | inl fy =>
        simp [hx, hy] at p
        cases g.inj fx fy p with
        | inr z => exact .inr z
        | inl ginj =>
          cases f.inj x y (by grind only) with
          | inr z => grind only [= Sum.isRight_inl]
          | inl finj => grind only
}

theorem compIdL_CubeHom (f : CubeHom n1 n2) : compCubeHom idCubeHom f = f := by
  apply CubeHom.ext
  unfold compCubeHom
  ext x
  cases hx : f.map x with
  | inr z =>
    unfold idCubeHom
    grind only
  | inl fx =>
    unfold idCubeHom
    grind only

theorem compIdR_CubeHom (f : CubeHom A B) : compCubeHom f idCubeHom = f := by
  apply CubeHom.ext
  unfold compCubeHom
  ext x
  cases hx : f.map x with
  | inr z =>
    unfold idCubeHom
    grind only
  | inl fx =>
    unfold idCubeHom
    grind only

theorem compAssoc_CubeHom (f : CubeHom A B) (g : CubeHom B C) (h : CubeHom C D) : compCubeHom (compCubeHom f g) h = compCubeHom f (compCubeHom g h) := by
  apply CubeHom.ext
  unfold compCubeHom
  funext x
  grind only

instance CubeCat : Category ℕ where
  Hom := CubeHom
  id := fun _ => idCubeHom
  comp := compCubeHom

  id_comp := compIdL_CubeHom
  comp_id := compIdR_CubeHom
  assoc := compAssoc_CubeHom

-----------------------------------------------------------------------
-- cubical set

def CubicalSet : Functor _ _ := by sorry
