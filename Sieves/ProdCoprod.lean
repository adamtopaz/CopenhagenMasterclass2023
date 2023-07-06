import Mathlib.CategoryTheory.Limits.Preserves.Opposites

open CategoryTheory Opposite Limits

section ProdToCoprod

variable {C : Type _} [Category C] {α : Type} [Finite α]
  (Z : α → C) [HasFiniteProducts C]

@[simps!]
noncomputable
def oppositeCofan : Cofan (fun z => op (Z z)) :=
  Cofan.mk (op <| ∏ Z) fun i => (Pi.π _ i).op

@[simps]
noncomputable
def isColimitOppositeCofan : IsColimit (oppositeCofan Z) where
  desc := fun S =>
    let e : S.pt.unop ⟶ ∏ Z := Pi.lift fun j => (S.ι.app _).unop
    e.op
  fac := fun S j => by
    dsimp only [oppositeCofan_pt, Functor.const_obj_obj,
      oppositeCofan_ι_app, Discrete.functor_obj]
    simp only [← op_comp, limit.lift_π,
      Fan.mk_pt, Fan.mk_π_app, Quiver.Hom.op_unop]
  uniq := fun S m hm => by
    rw [← m.op_unop]
    congr 1
    apply limit.hom_ext
    intro j
    simpa using congr_arg Quiver.Hom.unop (hm j)

@[simp]
noncomputable
def ProdToCoprod : op (∏ Z) ≅ ∐ (fun z => op (Z z)) :=
  isColimitOppositeCofan Z |>.coconePointUniqueUpToIso <| colimit.isColimit _

end ProdToCoprod

section CoprodToProd

variable {C : Type _} [Category C] {α : Type} [Finite α]
  (Z : α → C) [HasFiniteCoproducts C]

@[simps!]
noncomputable
def oppositeFan : Fan (fun z => op (Z z)) := by
  refine' Fan.mk (op <| ∐ Z) fun i => (Sigma.ι _ i).op

@[simps!]
noncomputable
def isLimitOppositeFan : IsLimit (oppositeFan Z) where
  lift := fun S =>
    let e : ∐ Z ⟶ S.pt.unop := Sigma.desc fun j => (S.π.app _).unop
    e.op
  fac := fun S j => by
    dsimp only [oppositeFan_pt, Functor.const_obj_obj,
      oppositeFan_π_app, Discrete.functor_obj]
    simp only [← op_comp, colimit.ι_desc,
      Cofan.mk_pt, Cofan.mk_ι_app, Quiver.Hom.op_unop]
  uniq := fun S m hm => by
    rw [← m.op_unop]
    congr 1
    apply colimit.hom_ext
    intro j
    simpa using congr_arg Quiver.Hom.unop (hm j)

@[simp]
noncomputable
def CoprodToProd : op (∐ Z) ≅ ∏ (fun z => op (Z z)) :=
  isLimitOppositeFan Z |>.conePointUniqueUpToIso <| limit.isLimit _

lemma CoprodToProdInvComp.ι (b : α) : ((CoprodToProd Z).inv ≫ (Sigma.ι (fun a => Z a) b).op) =
    Pi.π (fun a => op (Z a)) b :=
  IsLimit.conePointUniqueUpToIso_inv_comp (isLimitOppositeFan Z) (limit.isLimit _) ⟨b⟩

variable {X : C} (π : (a : α) → Z a ⟶ X)

lemma descOpCompCoprodToProd {X : C} (π : (a : α) → Z a ⟶ X) :
    (Sigma.desc π).op ≫ (CoprodToProd Z).hom = Pi.lift (fun a => Quiver.Hom.op (π a)) := by
  refine' limit.hom_ext (fun a => _)
  simp only [CoprodToProd, Category.assoc, limit.conePointUniqueUpToIso_hom_comp, oppositeFan_pt, 
    oppositeFan_π_app, limit.lift_π, Fan.mk_pt, Fan.mk_π_app, ← op_comp, colimit.ι_desc]
  rfl

end CoprodToProd