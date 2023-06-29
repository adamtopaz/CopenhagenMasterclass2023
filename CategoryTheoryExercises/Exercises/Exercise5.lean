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
  F.obj (X ⊞ Y) ≅ F.obj X ⊞ F.obj Y := sorry

-- Variant:
-- In fact one could prove a better result,
-- not requiring chosen biproducts in D,
-- asserting that `F.obj (X ⊞ Y)` is a biproduct of `F.obj X` and `F.obj Y`.

-- Note that the version for all finite biproducts is already in mathlib!
example (F : C ⥤ D) [F.Additive] :
  PreservesFiniteBiproducts F := inferInstance

-- but the below is missing!

instance (F : C ⥤ D) [F.Additive] :
  PreservesBinaryBiproducts F := sorry -- `inferInstance` fails!

example (F : C ⥤ D) [F.Additive] (X Y : C) :
  F.obj (X ⊞ Y) ≅ F.obj X ⊞ F.obj Y := 
Functor.mapBiprod F X Y -- works given the instance above

end CategoryTheory