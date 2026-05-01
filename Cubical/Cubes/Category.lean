-- import Mathlib.CategoryTheory.Category.Basic
import Mathlib
import Cubical.Cubes.Normalized

open CategoryTheory

def Cube : Type := ℕ

def CubeHom (m n : ℕ) : Type := Fin m → DMN n

def idCubeHom : ∀ N, CubeHom N N := fun _ i => {
  clauses := {ClauseStuff.Clause.mk {i} ∅},
  antichain := by grind only [= Finset.mem_singleton]
}

def compCubeHom : CubeHom X Y → CubeHom Y Z → CubeHom X Z :=
  fun f g x =>
    let fx := f x
    _

instance CubeCategory : Category Cube where
  Hom := CubeHom
  id := idCubeHom
  comp := by sorry

def CubicalSet : CategoryTheory.Functor Cubeᵒᵖ (Set n) := {
  obj := by sorry
  map := by sorry
}
