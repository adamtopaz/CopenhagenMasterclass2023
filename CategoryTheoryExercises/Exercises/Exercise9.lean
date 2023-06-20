import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Mathlib.CategoryTheory.Preadditive.Basic
import Mathlib.CategoryTheory.Preadditive.Biproducts
import Mathlib.Data.Fintype.Sigma
/-!
Let's show that every preadditive category embeds into a preadditive category with biproducts,
and identify a good universal property.

This is a more advanced exercise, for which I've indicated a suggested structure,
but not written a full solution. I hope this structure will work out!
-/

noncomputable section

universe w v u

variable (C : Type u)

structure AdditiveEnvelope :=
(ι : Type)
[fintype : Fintype ι]
[decidable_eq : DecidableEq ι]
(val : ι → C)

attribute [instance] AdditiveEnvelope.fintype AdditiveEnvelope.decidable_eq

variable {C}

def Dmatrix {X Y : AdditiveEnvelope C} (Z : X.ι → Y.ι → Type w) := ∀ (i : X.ι) (j : Y.ι), Z i j
-- You may need to develop some API for `Dmatrix`, parallel to that in `data.matrix.basic`.
-- One thing you'll certainly need is an "extensionality" lemma,
-- showing that you can prove two `Dmatrix`s are equal by checking componentwise.

open CategoryTheory

variable [Category C] [Preadditive C]

namespace family

def Hom (X Y : AdditiveEnvelope C) := Dmatrix (fun i j ↦ X.val i ⟶ Y.val j)

open BigOperators

instance : Category (AdditiveEnvelope C) :=
{ Hom := Hom,
  id := fun X i j ↦ if h : i = j then eqToHom (by subst h ; rfl) else 0,
  comp := @fun X Y Z f g i k ↦ ∑ j : Y.ι, f i j ≫ g j k,
  id_comp := sorry,
  comp_id := sorry,
  assoc := sorry, }

variable (C)

@[simps]
def embedding : C ⥤ AdditiveEnvelope C :=
{ obj := fun X ↦ ⟨Unit, fun _ ↦ X⟩,
  map := λ f _ _ ↦ f,
  map_id := sorry,
  map_comp := sorry, }

lemma embedding.faithful : Faithful (embedding C) :=
sorry

instance : Preadditive (AdditiveEnvelope C) :=
sorry -- probably best to go back and make `dmatrix` an `add_comm_group` first.

open Limits

instance : HasFiniteBiproducts (AdditiveEnvelope C) :=
{ out := fun n ↦
  { has_biproduct := fun F ↦ HasBiproduct.mk (
    { bicone :=
      { pt :=
        { ι := Σ (j : Fin n), (F j).ι,
          val := fun p ↦ (F p.1).val p.2 },
        ι := sorry,
        π := sorry,
        ι_π := sorry, },
      isBilimit := sorry } : LimitBicone _)}}

variable {C}

def factor {D : Type u} [Category.{v} D] [Preadditive D] [HasFiniteBiproducts D]
  (F : C ⥤ D) : AdditiveEnvelope C ⥤ D :=
{ obj := fun X ↦ ⨁ (fun i ↦ F.obj (X.val i)),
  map := sorry,
  map_id := sorry,
  map_comp := sorry, }

def factor_factorisation {D : Type u} [Category D] [Preadditive D] [HasFiniteBiproducts D]
  (F : C ⥤ D) : F ≅ embedding C ⋙ factor F :=
sorry

end family

end section
