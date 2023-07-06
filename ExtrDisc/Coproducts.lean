import ExtrDisc.Basic

open CategoryTheory Limits

universe u

namespace ExtrDisc

variable {α : Type u} (X : α → ExtrDisc.{u})

abbrev mkHom {X Y : ExtrDisc.{u}} (f : X.compHaus ⟶ Y.compHaus) :
  X ⟶ Y := f

@[simps]
noncomputable
def coproductCocone : Cofan X where
  pt := {
    compHaus := ∐ fun i => (X i).compHaus
    extrDisc := by
      rw [← CompHaus.Gleason]
      infer_instance
  }
  ι := Discrete.natTrans fun ⟨i⟩ => Sigma.ι 
    (fun i => (X i).compHaus) i
    
@[simps]
noncomputable
def isColimitCoproductCocone :  
    IsColimit (coproductCocone X) where
      desc := fun S =>  
        mkHom <| Sigma.desc fun _ => S.ι.app _ 
      fac := fun S ⟨i⟩ => 
        colimit.ι_desc (toCompHaus.mapCocone S) ⟨i⟩ 
      uniq := fun S _ hm => 
        (colimit.isColimit _).uniq (toCompHaus.mapCocone S) _ hm

noncomputable
instance {α : Type u} : 
    PreservesColimitsOfShape (Discrete α) toCompHaus := by
  constructor ; unfold autoParam ; intro K 
  let e : K ≅ Discrete.functor (fun i => K.obj ⟨i⟩) := 
    Discrete.natIsoFunctor 
  suffices PreservesColimit 
      (Discrete.functor (fun i => K.obj ⟨i⟩)) toCompHaus from 
    preservesColimitOfIsoDiagram (h := e.symm) (F := toCompHaus)
  apply preservesColimitOfPreservesColimitCocone    
    (h := isColimitCoproductCocone _)
  exact colimit.isColimit _

noncomputable
instance {α : Type u} :
    CreatesColimitsOfShape (Discrete α) toCompHaus where
  CreatesColimit := by
    intro K
    let e : K ≅ Discrete.functor (fun i => K.obj ⟨i⟩) := 
      Discrete.natIsoFunctor 
    suffices CreatesColimit 
        (Discrete.functor <| fun i => K.obj ⟨i⟩) toCompHaus by
      apply createsColimitOfIsoDiagram (h := e.symm) (F := toCompHaus)
    apply createsColimitOfFullyFaithfulOfIso 
      (X := coproductCocone (fun i => K.obj ⟨i⟩) |>.pt)
    exact Iso.refl _

noncomputable
example {α : Type u} :
  PreservesColimitsOfShape (Discrete α) toCompHaus := 
    inferInstance

end ExtrDisc