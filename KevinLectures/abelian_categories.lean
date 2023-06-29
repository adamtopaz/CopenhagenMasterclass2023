import Mathlib.CategoryTheory.Abelian.Basic -- definition and basic properties of abelian categories

import Mathlib.CategoryTheory.Limits.Preserves.Filtered -- definition and basic properties of 
-- filtered colimits and cofiltered limits

/-

## An abelian category tutorial

-/

open CategoryTheory

-- let `𝒞` be an abelian category

variable {𝒞 : Type u} [Category.{v} 𝒞] [Abelian 𝒞]
/- 

Note: `Abelian 𝒞` is *data*, because e.g. it contains the group structure
on `A ⟶ B` for all `A`, `B`. 

-/

-- Let A, B be objects of 𝒞

variable (A B : 𝒞)

example : AddCommGroup (A ⟶ B) := inferInstance

#synth AddCommGroup (A ⟶ B)

variable (f g : A ⟶ B) in
#check f + g

variable (f g : A ⟶ B) (C : 𝒞) (h : B ⟶ C) in
example : (f + g) ≫ h = f ≫ h + g ≫ h := by exact Preadditive.add_comp A B C f g h

variable (C : 𝒞) (h : B ⟶ C) in
example : (A ⟶ B) →+ (A ⟶ C) := by exact Preadditive.rightComp A h

-- exercise
example : Ring (A ⟶ A) :=
{ Preadditive.homGroup A A with
  mul := sorry
  left_distrib := sorry
  right_distrib := sorry
  zero_mul := sorry
  mul_zero := sorry
  mul_assoc := sorry
  one := 𝟙 A
  one_mul := sorry
  mul_one := sorry
  add_left_neg := sorry
}

open Limits

noncomputable section

variable (f : A ⟶ B)


#check kernel f
example : kernel f ⟶ A := by exact kernel.ι f
#check cokernel f
example : B ⟶ cokernel f := by exact cokernel.π f -- it's epi, and composition is zero

#synth Mono (kernel.ι f)

example : kernel.ι f ≫ f = 0 := by exact kernel.condition f

example (g : C ⟶ A) (hg : g ≫ f = 0) : C ⟶ kernel f := by exact kernel.lift f g hg

example (g : C ⟶ A) (hg : g ≫ f = 0) : kernel.lift f g hg ≫ kernel.ι f = g := by exact kernel.lift_ι f g hg

example (g : B ⟶ C) (hg : f ≫ g = 0) : cokernel.π f ≫ cokernel.desc f g hg = g := sorry

example [Mono f] [Epi f] : IsIso f := by exact isIso_of_mono_of_epi f

#synth Balanced 𝒞

open Abelian
#check image f -- WARNING!
#check Abelian.image f -- WARNING!
#check Abelian.coimage f

noncomputable example : Abelian.image f ⟶ B := by exact Abelian.image.ι f
noncomputable example : A ⟶ Abelian.image f := by exact Abelian.factorThruImage f

example : Abelian.factorThruImage f ≫ Abelian.image.ι f = f := sorry

-- coimage is cokernel of kernel
noncomputable example : A ⟶ Abelian.coimage f := sorry
noncomputable example : Abelian.coimage f ⟶ B := sorry

example : coimage.π f ≫ Abelian.factorThruCoimage f = f := sorry

noncomputable example : Abelian.coimage f ⟶ Abelian.image f := by exact coimageImageComparison f

#synth  IsIso (coimageImageComparison f)

/-

# Preserving Filtered Colimits (AB5)

-/
open Limits

-- Let J be a (small) filtered category

variable {J : Type v} [SmallCategory J] (K : J ⥤ 𝒞)

variable (𝒟 : Type _) [Category 𝒟] (F : 𝒞 ⥤ 𝒟)

example (h : ∀ {c : Cocone K}, IsColimit c → IsColimit (F.mapCocone c)) : PreservesColimit K F :=
⟨h⟩   


example (h : ∀ K : J ⥤ 𝒞, PreservesColimit K F) : PreservesColimitsOfShape J F := ⟨@h⟩ 

example (h : ∀ (J : Type v) [SmallCategory J] [IsFiltered J], PreservesColimitsOfShape J F) :
  PreservesFilteredColimits F := ⟨h⟩







#check PreservesFilteredColimits