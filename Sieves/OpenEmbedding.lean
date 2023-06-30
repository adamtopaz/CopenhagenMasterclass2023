import ExtrDisc.Epi

universe u

open CategoryTheory CategoryTheory.Limits

namespace ExtrDisc

variable {α : Type} [Fintype α] (Z : α → ExtrDisc.{u})

section Iso

noncomputable
def toFiniteCoproduct : ∐ Z ⟶ finiteCoproduct Z :=
  Sigma.desc <| fun a => finiteCoproduct.ι Z a ≫ (𝟙 _)

noncomputable
def fromFiniteCoproduct : finiteCoproduct Z ⟶ ∐ Z :=
  finiteCoproduct.desc Z <| fun a => (Sigma.ι Z a)
  
@[simp]
theorem toFiniteCoproductCompFromFiniteCoproduct :
  (toFiniteCoproduct Z ≫ fromFiniteCoproduct Z) = 𝟙 _ := by
  ext
  simp [toFiniteCoproduct, fromFiniteCoproduct]

@[simp]
theorem FromFiniteCoproductComptToFiniteCoproduct :
  (fromFiniteCoproduct Z ≫ toFiniteCoproduct Z) = 𝟙 _ := by
  refine' finiteCoproduct.hom_ext _ _ _ (fun a => _)
  simp [toFiniteCoproduct, fromFiniteCoproduct]

theorem Sigma.ιCompToFiniteCoproduct (a : α) :
    (Sigma.ι Z a) ≫ toFiniteCoproduct Z = finiteCoproduct.ι Z a := by
  simp [toFiniteCoproduct]
  
@[simps] noncomputable
def toFiniteCoproductHomeo : (∐ Z : _) ≃ₜ finiteCoproduct Z where
  toFun := toFiniteCoproduct Z
  invFun := fromFiniteCoproduct Z
  left_inv := fun x => by
    change (toFiniteCoproduct Z ≫ fromFiniteCoproduct Z) x = x
    simp
    rfl
  right_inv := fun x => by
    change (fromFiniteCoproduct Z ≫ toFiniteCoproduct Z) x = x
    simp
    rfl
  continuous_toFun := (toFiniteCoproduct Z).continuous_toFun
  continuous_invFun := (fromFiniteCoproduct Z).continuous_toFun

theorem toFiniteCoproduct.OpenEmbedding : OpenEmbedding (toFiniteCoproductHomeo Z) :=
  Homeomorph.openEmbedding (toFiniteCoproductHomeo Z)

end Iso

section OpenEmbedding

lemma finiteCoproduct.ιOpenEmbedding {α : Type} [Fintype α] (Z : α → ExtrDisc.{u}) (a : α) :
    OpenEmbedding (finiteCoproduct.ι Z a) := by
  exact openEmbedding_sigmaMk (σ := fun a => (Z a))

lemma DagurOpenEmbedding {α : Type} [Fintype α] (Z : α → ExtrDisc.{u}) (a : α) :
    OpenEmbedding (Sigma.ι Z a) := by
  refine' OpenEmbedding.of_comp _ (toFiniteCoproduct.OpenEmbedding Z) _
  convert finiteCoproduct.ιOpenEmbedding Z a
  ext x
  change ((Sigma.ι Z a) ≫ toFiniteCoproduct Z) x = _
  rw [Sigma.ιCompToFiniteCoproduct]


end OpenEmbedding

end ExtrDisc