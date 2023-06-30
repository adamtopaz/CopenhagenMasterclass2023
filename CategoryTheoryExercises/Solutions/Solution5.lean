import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Mathlib.CategoryTheory.Preadditive.Biproducts
set_option autoImplicit false
/-!
We prove that binary and finite biproducts (direct sums) are preserved by any 
additive functor.
-/

noncomputable section

open CategoryTheory
open CategoryTheory.Limits

namespace CategoryTheory

universe u v

variable {C : Type u} [Category C] [Preadditive C]
variable {D : Type v} [Category D] [Preadditive D]

variable [HasBinaryBiproducts C] [HasBinaryBiproducts D]

def Functor.Additive.preservesBinaryBiproducts (F : C ⥤ D) [Additive F] (X Y : C) :
  F.obj (X ⊞ Y) ≅ F.obj X ⊞ F.obj Y where
    hom := (F.map biprod.fst) ≫ biprod.inl + F.map biprod.snd ≫ biprod.inr
    inv := biprod.fst ≫ F.map biprod.inl + biprod.snd ≫ F.map biprod.inr
    hom_inv_id := by
      simp
      rw [← F.map_comp, ← F.map_comp]
      rw [← map_add]
      simp
      done
    inv_hom_id := by
      simp
      rw [← Category.assoc (F.map biprod.inl), ← F.map_comp]
      simp
      rw [← Category.assoc (F.map biprod.inr), ← F.map_comp]
      simp
      rw [← Category.assoc (F.map biprod.inl), ← F.map_comp]
      simp
      rw [← Category.assoc (F.map biprod.inr), ← F.map_comp]
      simp
      done

-- Challenge problem:
-- In fact one could prove a better result,
-- not requiring chosen biproducts in D,
-- asserting that `F.obj (X ⊞ Y)` is a biproduct of `F.obj X` and `F.obj Y`.

def Functor.Additive.preservesFiniteBiproducts (F : C ⥤ D) [Additive F] :
  PreservesFiniteBiproducts F := inferInstance

example (F : C ⥤ D) [F.Additive] :
  PreservesFiniteBiproducts F := inferInstance

variable (F : C ⥤ D) [F.Additive] in
#synth PreservesFiniteBiproducts F 

variable (F : C ⥤ D) [F.Additive] in
#synth PreservesBinaryBiproducts F -- oops!

def Functor.Additive.preservesBinaryBiproducts' (F : C ⥤ D) [Additive F] (X Y : C) :
  F.obj (X ⊞ Y) ≅ F.obj X ⊞ F.obj Y := 
  mapBiprod F X Y


end CategoryTheory

end section