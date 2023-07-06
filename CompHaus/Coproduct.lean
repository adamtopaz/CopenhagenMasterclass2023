import Mathlib.Topology.Category.CompHaus.ExplicitLimits

universe u

open CategoryTheory CategoryTheory.Limits

namespace CompHaus

variable {α : Type} [Fintype α] (Z : α → CompHaus.{u})

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

@[simps]
noncomputable
def FromFiniteCoproductIso : finiteCoproduct Z ≅ ∐ Z where
  hom := fromFiniteCoproduct Z
  inv := toFiniteCoproduct Z
  hom_inv_id := FromFiniteCoproductComptToFiniteCoproduct Z
  inv_hom_id := toFiniteCoproductCompFromFiniteCoproduct Z

@[simps]
noncomputable
def ToFiniteCoproductIso : ∐ Z ≅ finiteCoproduct Z where
  hom := toFiniteCoproduct Z
  inv := fromFiniteCoproduct Z
  hom_inv_id := toFiniteCoproductCompFromFiniteCoproduct Z
  inv_hom_id := FromFiniteCoproductComptToFiniteCoproduct Z

theorem IsIsotoFiniteCoproduct :
    IsIso (toFiniteCoproduct Z) :=
  ⟨fromFiniteCoproduct Z, by simp, by simp⟩

theorem IsIsofromFiniteCoproduct :
    IsIso (fromFiniteCoproduct Z) :=
  ⟨toFiniteCoproduct Z, by simp, by simp⟩

@[simp]
theorem Sigma.ιCompToFiniteCoproduct (a : α) :
    (Sigma.ι Z a) ≫ toFiniteCoproduct Z = finiteCoproduct.ι Z a := by
  simp [toFiniteCoproduct]
  
@[simp]
theorem finiteCoproduct.ιCompFromFiniteCoproduct (a : α) :
    (finiteCoproduct.ι Z a) ≫ fromFiniteCoproduct Z = Sigma.ι Z a := by
  simp [fromFiniteCoproduct]

@[simps] noncomputable
def toFiniteCoproductHomeo : (∐ Z : _) ≃ₜ finiteCoproduct Z where
  toFun := toFiniteCoproduct Z
  invFun := fromFiniteCoproduct Z
  left_inv := fun x => by
    change (toFiniteCoproduct Z ≫ fromFiniteCoproduct Z) x = x
    simp only [toFiniteCoproductCompFromFiniteCoproduct, id_apply]
  right_inv := fun x => by
    change (fromFiniteCoproduct Z ≫ toFiniteCoproduct Z) x = x
    simp only [FromFiniteCoproductComptToFiniteCoproduct, id_apply]
  continuous_toFun := (toFiniteCoproduct Z).continuous_toFun
  continuous_invFun := (fromFiniteCoproduct Z).continuous_toFun

theorem toFiniteCoproduct.OpenEmbedding : OpenEmbedding (toFiniteCoproductHomeo Z) :=
  Homeomorph.openEmbedding (toFiniteCoproductHomeo Z)

end Iso

lemma finiteCoproduct.ι_injective {α : Type} [Fintype α] {Z : α → CompHaus.{u}} 
    (a : α) : Function.Injective (finiteCoproduct.ι Z a) := by
  intro x y hxy 
  exact eq_of_heq (Sigma.ext_iff.mp hxy).2

lemma finiteCoproduct.ι_jointly_surjective {α : Type} [Fintype α] {Z : α → CompHaus.{u}} 
    (R : finiteCoproduct Z) : ∃ (a : α) (r : Z a), R = finiteCoproduct.ι Z a r := by
  exact ⟨R.fst, R.snd, rfl⟩

lemma finiteCoproduct.ι_desc_apply {α : Type} [Fintype α] {X : CompHaus.{u}}
    {Z : α → CompHaus.{u}} {π : (a : α) → Z a ⟶ X} (a : α) : 
    ∀ x, finiteCoproduct.desc Z π (finiteCoproduct.ι Z a x) = π a x := by
  intro x 
  change (ι Z a ≫ desc Z π) _ = _ 
  simp only [ι_desc]

lemma finiteCoproduct.range_eq {α : Type} [Fintype α] {Z : α → CompHaus.{u}} 
    {a b : α} (h : a = b) : Set.range (ι Z a) = Set.range (ι Z b) := by
  rw [h]

end CompHaus