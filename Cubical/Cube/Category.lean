-- import Mathlib.CategoryTheory.Category.Basic
import Mathlib
import Cubical.Cube.Normalized

open CategoryTheory
open NormalizedStuff

def Cube : Type := ℕ

def CubeHom (m n : ℕ) : Type := Fin m → DMN n

@[ext]
lemma CubeHom.ext {f g : CubeHom m n} (h : ∀ i, f i = g i) : f = g := funext h

def idCubeHom : ∀ N, CubeHom N N := fun _ i => {
  clauses := {ClauseStuff.Clause.mk {i} ∅},
  antichain := by grind only [= Finset.mem_singleton]
}

def compCubeHom (f : CubeHom X Y) (g : CubeHom Y Z) : CubeHom X Z :=
  fun x => dmnEval g (f x)

@[simp]
lemma cubeHomCompId : ∀ (f : CubeHom X Y), compCubeHom f (idCubeHom _) = f := by
  intros f
  unfold compCubeHom
  unfold dmnEval
  ext x cl

@[simp]
lemma cubeHomIdComp : ∀ (f : CubeHom X Y), compCubeHom (idCubeHom _) f = f := by
  intros f

@[simp]
lemma cubeHomAssoc : ∀ (f : CubeHom X Y) (g : CubeHom Y Z) (h : CubeHom Z W) ,
    compCubeHom (compCubeHom f g) h = compCubeHom f (compCubeHom g h)  := by
  sorry

instance CubeCategory : Category Cube where
  Hom := CubeHom
  id := idCubeHom
  comp := compCubeHom

  comp_id := cubeHomCompId
  id_comp := cubeHomIdComp
  assoc := cubeHomAssoc

def CubicalSet := CategoryTheory.Functor Cubeᵒᵖ (Type _)
