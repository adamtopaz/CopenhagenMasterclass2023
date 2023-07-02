import Mathlib.Condensed.Basic
import Mathlib.CategoryTheory.Sites.Whiskering
set_option autoImplicit false

--universe x v₁ u₁ v₂ u₂ v u

--universe aa bb cc dd

namespace CategoryTheory

open Limits

section working

universe v₁ v₂ u₁ u₂ 
variable {C : Type u₁} [Category.{v₁} C]
  {D : Type u₂} [Category.{v₂} D]
  (F : C ⥤ D)
  [Limits.PreservesLimits F]
  {J : GrothendieckTopology CompHaus.{0}}
  (P : CompHaus.{0}ᵒᵖ ⥤ C)
  {X : CompHaus.{0}}
  (S : J.Cover X)

def GrothendieckTopology.Cover.index' :
    Limits.MulticospanIndex C where
  L := S.Arrow
  R := S.Relation
  fstTo I := I.fst
  sndTo I := I.snd
  left I := P.obj (Opposite.op I.Y)
  right I := P.obj (Opposite.op I.Z)
  fst I := P.map I.g₁.op
  snd I := P.map I.g₂.op


/-
variable {C : Type u₁} [Category.{v₁} C]
  {X : C}
  {J : GrothendieckTopology C}
  {D : Type u₂} [Category.{v₂} D]

-- **TODO** universe broken in CategoryTheory.Limits.Multifork

/-
CategoryTheory.GrothendieckTopology.Cover.multifork.{w, v, u} {C : Type u} [inst✝ : Category C] {X : C}
  {J : GrothendieckTopology C} {D : Type w} [inst✝¹ : Category D] (S : Cover J X) (P : Cᵒᵖ ⥤ D) :
  Limits.Multifork (index S P)
  -/
-/

#check CategoryTheory.GrothendieckTopology.Cover.multifork

abbrev GrothendieckTopology.Cover.multifork' :--
    Limits.Multifork (S.index' P) :=
  Limits.Multifork.ofι _ (P.obj (Opposite.op X)) (fun I => P.map I.f.op)
    (by
      intro I
      dsimp [CategoryTheory.GrothendieckTopology.Cover.index']
      simp only [← P.map_comp, ← op_comp, I.w])

open Opposite

noncomputable
def Presheaf.IsSheaf.amalgamate' {J : GrothendieckTopology C} {E : D} {X : C} {P : Cᵒᵖ ⥤ D}
    (hP : Presheaf.IsSheaf J P) (S : J.Cover X) (x : ∀ I : S.Arrow, E ⟶ P.obj (op I.Y))
    (hx : ∀ I : S.Relation, x I.fst ≫ P.map I.g₁.op = x I.snd ≫ P.map I.g₂.op) : E ⟶ P.obj (op X) :=
  (hP _ _ S.condition).amalgamate (fun Y f hf => x ⟨Y, f, hf⟩) fun Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ w =>
    hx ⟨Y₁, Y₂, Z, g₁, g₂, f₁, f₂, h₁, h₂, w⟩

@[reassoc (attr := simp)]
theorem Presheaf.IsSheaf.amalgamate'_map {J : GrothendieckTopology C} {E : D} {X : C} {P : Cᵒᵖ ⥤ D}
    (hP : Presheaf.IsSheaf J P) (S : J.Cover X) (x : ∀ I : S.Arrow, E ⟶ P.obj (op I.Y))
    (hx : ∀ I : S.Relation, x I.fst ≫ P.map I.g₁.op = x I.snd ≫ P.map I.g₂.op) (I : S.Arrow) :
    hP.amalgamate' S x hx ≫ P.map I.f.op = x _ := by
  rcases I with ⟨Y, f, hf⟩
  apply
    @Presieve.IsSheafFor.valid_glue _ _ _ _ _ _ (hP _ _ S.condition) (fun Y f hf => x ⟨Y, f, hf⟩)
      (fun Y₁ Y₂ Z g₁ g₂ f₁ f₂ h₁ h₂ w => hx ⟨Y₁, Y₂, Z, g₁, g₂, f₁, f₂, h₁, h₂, w⟩) f hf


end working

section more_working


universe v₂ u₂ v u 
variable {C : Type u} [Category.{v} C]
variable {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology CompHaus.{0}}
variable (F : C ⥤ D)
  {P : CompHaus.{0}ᵒᵖ ⥤ C}
  {X : CompHaus.{0}}
  (S : J.Cover X)

open Opposite

#check Presheaf.IsSheaf.hom_ext

theorem Presheaf.IsSheaf.hom_ext' {E : C}
    (hP : Presheaf.IsSheaf J P) (S : J.Cover X) (e₁ e₂ : E ⟶ P.obj (op X))
    (h : ∀ I : S.Arrow, e₁ ≫ P.map I.f.op = e₂ ≫ P.map I.f.op) : e₁ = e₂ :=
  (hP _ _ S.condition).isSeparatedFor.ext fun Y f hf => h ⟨Y, f, hf⟩

variable (J) (P)

#check CategoryTheory.Presheaf.isLimitOfIsSheaf

noncomputable
def Presheaf.isLimitOfIsSheaf' {X : CompHaus.{0}} (S : J.Cover X) (hP : IsSheaf J P) : IsLimit (S.multifork' P) where
  lift := fun E : Multifork _ => hP.amalgamate' S (fun I => E.ι _) fun I => E.condition _
  fac := by
    rintro (E : Multifork _) (a | b)
    · apply hP.amalgamate'_map
    · rw [← E.w (WalkingMulticospan.Hom.fst b),
        ← (S.multifork' P).w (WalkingMulticospan.Hom.fst b), ← Category.assoc]
      congr 1
      apply hP.amalgamate'_map
  uniq := by
    rintro (E : Multifork _) m hm
    apply hP.hom_ext' S
    intro I
    erw [hm (WalkingMulticospan.left I)]
    symm
    apply hP.amalgamate'_map


set_option pp.universes true in
theorem Presheaf.isSheaf_iff_multifork' :
    IsSheaf J P ↔ ∀ (X : CompHaus.{0}) (S : J.Cover X), Nonempty (IsLimit (S.multifork' P)) := by
  refine' ⟨fun hP X S => ⟨isLimitOfIsSheaf' _ _ _ hP⟩, _⟩
  intro h E X S hS x hx
  let T : J.Cover X := ⟨S, hS⟩
  obtain ⟨hh⟩ := h _ T
  let K : Multifork (T.index' P) := Multifork.ofι _ E (fun I => x I.f I.hf) fun I => hx _ _ _ _ I.w
  use hh.lift K
  dsimp; constructor
  · intro Y f hf
    apply hh.fac K (WalkingMulticospan.left ⟨Y, f, hf⟩)
  · intro e he
    apply hh.uniq K
    rintro (a | b)
    · apply he
    · rw [← K.w (WalkingMulticospan.Hom.fst b), ←
        (T.multifork' P).w (WalkingMulticospan.Hom.fst b), ← Category.assoc]
      congr 1
      apply he



variable {U : CompHaus.{0}} (R : Presieve U)


namespace GrothendieckTopology.Cover

variable {X : CompHaus.{0}} (S : J.Cover X)

-- `def multicospan : WalkingMulticospan I.fstTo I.sndTo ⥤ C where` -- needs a .{w}

variable {J}

/-
CategoryTheory.GrothendieckTopology.Cover.multicospanComp.{v₁, u₁, u₂, u₃} {C : Type u₁} [inst✝ : Category.{v₁, u₁} C]
  {A : Type u₂} [inst✝¹ : Category.{max v₁ u₁, u₂} A] {B : Type u₃} [inst✝² : Category.{max v₁ u₁, u₃} B]
  {J : GrothendieckTopology.{v₁, u₁} C} (F : Functor.{max u₁ v₁, max u₁ v₁, u₂, u₃} A B)
  (P : Functor.{v₁, max u₁ v₁, u₁, u₂} (Opposite.{u₁ + 1} C) A) {X : C} (S : Cover.{v₁, u₁} J X) :
  -/
/-- The multicospan associated to a cover `S : J.Cover X` and a presheaf of the form `P ⋙ F`
is isomorphic to the composition of the multicospan associated to `S` and `P`,
composed with `F`. -/
def multicospanComp' : (S.index' (P ⋙ F)).multicospan ≅ (S.index' P).multicospan ⋙ F :=
  NatIso.ofComponents
    (fun t =>
      match t with
      | WalkingMulticospan.left a => eqToIso rfl
      | WalkingMulticospan.right b => eqToIso rfl)
    (by
      rintro (a | b) (a | b) (f | f | f)
      all_goals aesop_cat)

@[simp]
theorem multicospanComp'_hom_app_left (a) :
    (S.multicospanComp' F P).hom.app (WalkingMulticospan.left a) = eqToHom rfl :=
  rfl

@[simp]
theorem multicospanComp'_hom_app_right (b) :
    (S.multicospanComp' F P).hom.app (WalkingMulticospan.right b) = eqToHom rfl :=
  rfl

def mapMultifork' :
    F.mapCone (S.multifork' P) ≅
      (Limits.Cones.postcompose (S.multicospanComp' F P).hom).obj (S.multifork' (P ⋙ F)) :=
  Cones.ext (eqToIso rfl)
    (by
      rintro (a | b)
      · dsimp
        erw [Category.id_comp, multicospanComp'_hom_app_left, eqToHom_refl, Category.comp_id]
      · dsimp
        erw [Functor.map_comp, Category.assoc, Category.id_comp,
          multicospanComp'_hom_app_right, eqToHom_refl, Category.comp_id]
        rfl)

end GrothendieckTopology.Cover

set_option pp.universes true in
#print CategoryTheory.sheafCompose
variable [PreservesLimitsOfSize.{1,1} F]

variable {J}

#check Presheaf.IsSheaf.comp

set_option pp.universes true in
theorem Presheaf.IsSheaf.comp' {P : CompHaus.{0}ᵒᵖ ⥤ C} (hP : Presheaf.IsSheaf J P) :
    Presheaf.IsSheaf J (P ⋙ F) := by
  rw [Presheaf.isSheaf_iff_multifork'] at hP⊢
  intro X S
  obtain ⟨h⟩ := hP X S
  replace h := isLimitOfPreserves F h
  replace h := Limits.IsLimit.ofIsoLimit h (S.mapMultifork' F P)
  exact ⟨Limits.IsLimit.postcomposeHomEquiv (S.multicospanComp' F P) _ h⟩

#check CategoryTheory.sheafCompose

variable (J)

def sheafCompose' : Sheaf J C ⥤ Sheaf J D where
  obj G := ⟨G.val ⋙ F, Presheaf.IsSheaf.comp' _ G.2⟩
  map η := ⟨whiskerRight η.val _⟩
  map_id _ := Sheaf.Hom.ext _ _ <| whiskerRight_id _
  map_comp _ _ := Sheaf.Hom.ext _ _ <| whiskerRight_comp _ _ _

end more_working

section main_results

universe v₂ v₁ u₂ u₁

variable {C : Type u₁} [Category.{v₁} C]
  {D : Type u₂} [Category.{v₂} D]
  (F : C ⥤ D)
  {J : GrothendieckTopology CompHaus.{0}}

/-
set_option pp.universes true in
example [PreservesLimitsOfSize F] : Condensed.{0} C ⥤ Condensed.{0} D := 
  sheafCompose J F -- fails

type mismatch
  sheafCompose.{0, 1, ?u.52605, ?u.52604} J ?m.52914
has type
  Functor.{1, 1, max ?u.52605 1, max ?u.52604 1} (Sheaf.{0, 1, 1, ?u.52605} J ?m.52610)
    (Sheaf.{0, 1, 1, ?u.52604} J ?m.52612) : Type (max 1 (max ?u.52605 1) ?u.52604 1)
but is expected to have type
  Functor.{max 1 v₁, max 1 v₂, max (max 1 v₁) u₁, max (max 1 v₂) u₂} (Condensed.{0, u₁, v₁} C)
    (Condensed.{0, u₂, v₂} D) : Type (max (max 1 v₁) (max 1 v₂) (max (max 1 v₁) u₁) (max 1 v₂) u₂)
-/

set_option pp.universes true in
def foobar [PreservesLimitsOfSize F] :
    Sheaf J C ⥤ 
    Sheaf J D :=
  sheafCompose' J F
/-
CategoryTheory.foobar.{v₂, v₁, u₂, u₁} {C : Type u₁} [inst✝ : Category.{v₁, u₁} C] {D : Type u₂}
  [inst✝¹ : Category.{v₂, u₂} D] (F : Functor.{v₁, v₂, u₁, u₂} C D) {J : GrothendieckTopology.{0, 1} CompHaus.{0}}
  [inst✝² : PreservesLimitsOfSize.{1, 1, v₁, v₂, u₁, u₂} F] :
  Functor.{max 1 v₁, max 1 v₂, max (max u₁ 1) v₁, max (max u₂ 1) v₂} (Sheaf.{0, v₁, 1, u₁} J C)
    (Sheaf.{0, v₂, 1, u₂} J D)
-/

example [PreservesLimitsOfSize F] : Condensed.{0} C ⥤ Condensed.{0} D := 
  sheafCompose' _ F -- works

end main_results

/-
inst✝² : PreservesLimitsOfSize.{1, 1, v₁, v₂, u₁, u₂} F
-/