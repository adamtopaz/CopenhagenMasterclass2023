import Mathlib.Topology.Category.CompHaus.ExplicitLimits

open CategoryTheory Limits

namespace CompHaus

variable {X Y Z : CompHaus.{u}} (f : X ⟶ Z) (i : Y ⟶ Z) 

section Isos

noncomputable
def toExplicit : Limits.pullback f i ⟶ CompHaus.pullback f i :=
  pullback.lift f i Limits.pullback.fst Limits.pullback.snd Limits.pullback.condition

noncomputable
def fromExplicit : CompHaus.pullback f i ⟶ Limits.pullback f i :=
  Limits.pullback.lift (pullback.fst _ _) (pullback.snd _ _) (pullback.condition f i)

@[simp]
theorem toExplicitCompFromExcplict :
    (toExplicit f i ≫ fromExplicit f i) = 𝟙 _ := by
  refine' Limits.pullback.hom_ext (k := (toExplicit f i ≫ fromExplicit f i)) _ _
  · simp [toExplicit, fromExplicit]
  · rw [Category.id_comp, Category.assoc, fromExplicit, Limits.pullback.lift_snd,
      toExplicit, pullback.lift_snd]
    
@[simp]
theorem fromExcplictComptoExplicit :
    (fromExplicit f i ≫ toExplicit f i) = 𝟙 _ :=
  pullback.hom_ext f i _ _ (by simp [toExplicit, fromExplicit]) (by simp [toExplicit, fromExplicit])

@[simps]
noncomputable
def fromExplicitIso : CompHaus.pullback f i ≅ Limits.pullback f i where
  hom := fromExplicit f i
  inv := toExplicit f i
  hom_inv_id := fromExcplictComptoExplicit f i
  inv_hom_id := toExplicitCompFromExcplict f i

end Isos

section Commutativity

theorem fst_comp_fromExplicit : 
    CompHaus.pullback.fst f i = fromExplicit f i ≫ Limits.pullback.fst := by  
  dsimp [fromExplicit] 
  simp only [limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app]

theorem snd_comp_fromExplicit : 
    CompHaus.pullback.snd f i = fromExplicit f i ≫ Limits.pullback.snd := by  
  dsimp [fromExplicit] 
  simp only [limit.lift_π, PullbackCone.mk_pt, PullbackCone.mk_π_app]

end Commutativity

end CompHaus