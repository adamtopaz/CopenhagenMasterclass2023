import ExtrDisc.Basic
import Mathlib.Topology.Category.CompHaus.EffectiveEpi

import Profinite.Epi

open CategoryTheory Limits

namespace ExtrDisc

universe u

variable {α : Type} [Fintype α] (X : α → ExtrDisc.{u})

variable {B : ExtrDisc.{u}}
  {X : α → ExtrDisc.{u}} (π : (a : α) → (X a ⟶ B))
  (surj : ∀ b : B, ∃ (a : α) (x : X a), π a x = b)

/-- Construct a term of `Profinite` from a type endowed with the structure of a
compact, Hausdorff and totally disconnected topological space.
-/
def of (X : Type _) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [ExtremallyDisconnected X] : ExtrDisc :=
  ⟨⟨⟨X, inferInstance⟩⟩⟩

instance {π : ι → Type _} [∀ i, TopologicalSpace (π i)] [∀ i, ExtremallyDisconnected (π i)] :
    ExtremallyDisconnected (Σi, π i) := by
  sorry

section FiniteCoproducts

variable {α : Type} [Fintype α] (X : α → ExtrDisc.{u})

/--
The coproduct of a finite family of objects in `ExtrDisc`, constructed as the disjoint
union with its usual topology.
-/
def finiteCoproduct : ExtrDisc := ExtrDisc.of <| Σ (a : α), X a

/--
The inclusion of one of the factors into the explicit finite coproduct.
-/
def finiteCoproduct.ι (a : α) : X a ⟶ finiteCoproduct X where
  toFun := fun x => ⟨a,x⟩
  continuous_toFun := continuous_sigmaMk (σ := fun a => X a)

/--
To construct a morphism from the explicit finite coproduct, it suffices to
specify a morphism from each of its factors.
This is essentially the universal property of the coproduct.
-/
def finiteCoproduct.desc {B : ExtrDisc.{u}} (e : (a : α) → (X a ⟶ B)) :
    finiteCoproduct X ⟶ B where
  toFun := fun ⟨a,x⟩ => e a x
  continuous_toFun := by
    apply continuous_sigma
    intro a ; exact (e a).continuous

@[reassoc (attr := simp)]
lemma finiteCoproduct.ι_desc {B : ExtrDisc.{u}} (e : (a : α) → (X a ⟶ B)) (a : α) :
  finiteCoproduct.ι X a ≫ finiteCoproduct.desc X e = e a := rfl

lemma finiteCoproduct.hom_ext {B : ExtrDisc.{u}} (f g : finiteCoproduct X ⟶ B)
    (h : ∀ a : α, finiteCoproduct.ι X a ≫ f = finiteCoproduct.ι X a ≫ g) : f = g := by
  ext ⟨a,x⟩
  specialize h a
  apply_fun (fun q => q x) at h
  exact h

/--
The coproduct cocone associated to the explicit finite coproduct.
-/
@[simps]
def finiteCoproduct.cocone : Limits.Cocone (Discrete.functor X) where
  pt := finiteCoproduct X
  ι := Discrete.natTrans fun ⟨a⟩ => finiteCoproduct.ι X a

/--
The explicit finite coproduct cocone is a colimit cocone.
-/
@[simps]
def finiteCoproduct.isColimit : Limits.IsColimit (finiteCoproduct.cocone X) where
  desc := fun s => finiteCoproduct.desc _ fun a => s.ι.app ⟨a⟩
  fac := fun s ⟨a⟩ => finiteCoproduct.ι_desc _ _ _
  uniq := fun s m hm => finiteCoproduct.hom_ext _ _ _ fun a => by
    specialize hm ⟨a⟩
    ext t
    apply_fun (fun q => q t) at hm
    exact hm

end FiniteCoproducts

#check CompHaus.epi_iff_surjective

abbrev F := ExtrDisc.toCompHaus

lemma epi_iff_surjective {X Y : ExtrDisc.{u}} (f : X ⟶ Y) :
    Epi f ↔ Function.Surjective f := by
  sorry

namespace EffectiveEpiFamily

#check ExtrDisc.toCompHaus
#check profiniteToCompHaus
#check ExtrDisc.toProfinite
#check Full

lemma helper {W : ExtrDisc} {e : (a : α) → X a ⟶ W}
    (h : ∀ {Z : ExtrDisc} (a₁ a₂ : α) (g₁ : Z ⟶ X a₁) (g₂ : Z ⟶ X a₂),
      g₁ ≫ π a₁ = g₂ ≫ π a₂ → g₁ ≫ e a₁ = g₂ ≫ e a₂)
    : ∀ {Z : CompHaus} (a₁ a₂ : α) (g₁ : Z ⟶ F.obj (X a₁)) (g₂ : Z ⟶ F.obj (X a₂)),
        g₁ ≫ (π a₁) = g₂ ≫ (π a₂) → g₁ ≫ e a₁ = g₂ ≫ e a₂ := by
  intro Z a₁ a₂ g₁ g₂ hg
  -- apply h
  let βZ := Z.presentation
  let g₁' := F.preimage (Z.presentationπ ≫ g₁ : F.obj βZ ⟶ F.obj (X a₁))
  let g₂' := F.preimage (Z.presentationπ ≫ g₂ : F.obj βZ ⟶ F.obj (X a₂))
  have d := @h βZ a₁ a₂ g₁' g₂'
  apply Epi.left_cancellation (f := Z.presentationπ)
  change g₁' ≫ e a₁ = g₂' ≫ e a₂
  apply d
  change CompHaus.presentationπ Z ≫ g₁ ≫ π a₁ = CompHaus.presentationπ Z ≫ g₂ ≫ π a₂
  simp [hg]

noncomputable
def struct : EffectiveEpiFamilyStruct X π where
  desc := fun {W} e h => ExtrDisc.toCompHaus.preimage <|
    (CompHaus.effectiveEpiFamily_of_jointly_surjective (fun (a : α) => F.obj (X a)) π surj).desc
    (fun (a : α) => F.map (e a)) (helper π h)
  fac := by
    intro W e he a

    have : EffectiveEpiFamily (fun a => F.obj (X a)) π :=
      CompHaus.effectiveEpiFamily_of_jointly_surjective (fun a => F.obj (X a)) π surj

    have q := EffectiveEpiFamily.fac (fun (a : α) => F.obj (X a)) π e (helper π he) a

    change F.map (π a ≫ _) = F.map (e a) at q
    replace q := Faithful.map_injective q
    assumption
  uniq := by
    intro W e he m hm

    have Fhm : ∀ (a : α), π a ≫ F.map m = e a
    · aesop_cat

    have : EffectiveEpiFamily (fun a => F.obj (X a)) π :=
      CompHaus.effectiveEpiFamily_of_jointly_surjective (fun a => F.obj (X a)) π surj

    have q := EffectiveEpiFamily.uniq (fun (a : α) => F.obj (X a)) π e (helper π he) (F.map m) Fhm
    change F.map m = F.map _ at q
    replace q := Faithful.map_injective q
    assumption

end EffectiveEpiFamily

#check Faithful

theorem effectiveEpiFamily_of_jointly_surjective
    {α : Type} [Fintype α] {B : ExtrDisc.{u}}
    (X : α → ExtrDisc.{u}) (π : (a : α) → (X a ⟶ B))
    (surj : ∀ b : B, ∃ (a : α) (x : X a), π a x = b) :
    EffectiveEpiFamily X π :=
  ⟨⟨ExtrDisc.EffectiveEpiFamily.struct π surj⟩⟩

open List in
theorem effectiveEpiFamily_tfae {α : Type} [Fintype α] {B : ExtrDisc.{u}}
    (X : α → ExtrDisc.{u})
    (π : (a : α) → (X a ⟶ B)) :
    TFAE [
      EffectiveEpiFamily X π,
      Epi (Limits.Sigma.desc π),
      ∀ (b : B), ∃ (a : α) (x : X a), π a x = b
    ] := by
  tfae_have 1 → 2
  · intro ; infer_instance
  tfae_have 1 → 2
  · intro ; infer_instance
  tfae_have 2 → 3
  · intro e
    rw [epi_iff_surjective] at e
    let i : ∐ X ≅ finiteCoproduct X :=
      (colimit.isColimit _).coconePointUniqueUpToIso (finiteCoproduct.isColimit _)
    intro b
    obtain ⟨t,rfl⟩ := e b
    let q := i.hom t
    refine ⟨q.1,q.2,?_⟩
    have : t = i.inv (i.hom t) := show t = (i.hom ≫ i.inv) t by simp only [i.hom_inv_id] ; rfl
    rw [this]
    show _ = (i.inv ≫ Sigma.desc π) (i.hom t)
    suffices i.inv ≫ Sigma.desc π = finiteCoproduct.desc X π by
      rw [this] ; rfl
    rw [Iso.inv_comp_eq]
    apply colimit.hom_ext
    rintro ⟨a⟩
    simp only [Discrete.functor_obj, colimit.ι_desc, Cofan.mk_pt, Cofan.mk_ι_app,
      colimit.comp_coconePointUniqueUpToIso_hom_assoc]
    ext ; rfl
  tfae_have 3 → 1
  · apply effectiveEpiFamily_of_jointly_surjective
  tfae_finish

end ExtrDisc
