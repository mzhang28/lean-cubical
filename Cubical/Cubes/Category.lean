import Mathlib.CategoryTheory.Category.Basic
-- import Mathlib
import Cubical.Cubes.Normalized

open CategoryTheory

def Cube : Type := ℕ

def CubeHom (m n : ℕ) : Type := Fin m → DMN n

def idCubeHom : ∀ n, CubeHom n n := fun n i => {
  clauses := {ClauseStuff.Clause.mk {i} ∅},
  antichain := by grind only [= Finset.mem_singleton]
}

instance CubeCategory : Category Cube where
  Hom := CubeHom
  id := idCubeHom
