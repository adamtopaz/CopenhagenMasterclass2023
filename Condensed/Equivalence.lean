/-
Copyright (c) 2023 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz
-/
import Profinite.Coherent
import ExtrDisc.Coherent
import ExtrDisc.Topologies
import Mathlib.Condensed.Basic
import Mathlib.CategoryTheory.Sites.DenseSubsite
import Mathlib.CategoryTheory.Sites.InducedTopology
import Mathlib.CategoryTheory.Sites.Closed
import FindWithGpt
/-!
# Sheaves on CompHaus are equivalent to sheaves on ExtrDisc

The forgetful functor from extremally disconnected spaces `ExtrDisc` to compact
Hausdorff spaces `CompHaus` has the marvellous property that it induces an equivalence of categories
between sheaves on these two sites. With the terminology of nLab, `ExtrDisc` is a
*dense subsite* of `CompHaus`: see https://ncatlab.org/nlab/show/dense+sub-site

Mathlib has isolated three properties called `CoverDense`, `CoverPreserving` and `CoverLifting`,
which between them imply that `ExtrDisc` is a dense subsite, and it also has the
construction of the equivalence of the categories of sheaves, given these three properties.

## Main theorems

* `Condensed.coverDense`, `Condensed.coverPreserving`, `Condensed.coverLifting`: the
three conditions needed to guarantee the equivalence of the categories of sheaves
on the two sites.

## TODO

Prove the three main theorems!
-/


























open CategoryTheory Limits

namespace Condensed

universe u w

namespace ExtrDiscCompHaus

#check Sieve.coverByImage
lemma coverDense :
    CoverDense (coherentTopology _) ExtrDisc.toCompHaus := by
  constructor
  intro B
  let T := Presieve.singleton B.presentationπ
  let S := Sieve.generate T
  have hS : S ∈ coherentTopology CompHaus B := by
    apply Coverage.saturate.of
    change ∃ _, _
    refine ⟨Unit, inferInstance,
      fun _ => B.presentation.compHaus, fun _ => B.presentationπ, ?_ , ?_⟩
    · funext X f
      ext
      constructor
      · rintro ⟨⟩
        refine ⟨()⟩
      · rintro ⟨⟩
        simp
    · have := CompHaus.effectiveEpiFamily_tfae
        (fun (_ : Unit) => B.presentation.compHaus)
        (fun (_ : Unit) => B.presentationπ)
      apply (this.out 0 2).mpr
      intro b
<<<<<<< HEAD
      refine ⟨(), ?_⟩ 
      have hπ : 
        Function.Surjective B.presentationπ := sorry
      exact hπ b
  convert hS
  sorry
=======
      refine ⟨(), ?_⟩
      have hπ :
        Function.Surjective B.presentationπ := by
          rw [← CompHaus.epi_iff_surjective B.presentationπ]
          exact CompHaus.epiPresentπ B
      exact hπ b
  convert hS
  ext Y f
  constructor
  · rintro ⟨⟨obj, lift, map, fact⟩⟩
    obtain ⟨obj_factors⟩ : Projective obj.compHaus := by
      infer_instance
    obtain ⟨p, p_factors⟩ := obj_factors map B.presentationπ
    refine ⟨(CompHaus.presentation B).compHaus ,?_⟩
    refine ⟨lift ≫ p, ⟨ B.presentationπ
        , {
        left := Presieve.singleton.mk
        right := by
          rw [Category.assoc, p_factors, fact]
      } ⟩
      ⟩
  · rintro ⟨Z, h, g, hypo1, ⟨_⟩⟩
    cases hypo1
    constructor
    refine
    { obj := CompHaus.presentation B
      lift := h
      map := CompHaus.presentationπ B
      fac := rfl }
>>>>>>> master

theorem coverDense.inducedTopology_Sieve_iff_EffectiveEpiFamily (X : ExtrDisc) (S : Sieve X) :
    (∃ (α : Type) (_ : Fintype α) (Y : α → ExtrDisc) (π : (a : α) → (Y a ⟶ X)),
        EffectiveEpiFamily Y π ∧ (∀ a : α, (S.arrows) (π a)) ) ↔
          (S ∈ coverDense.inducedTopology X) := by
  constructor
  · rintro ⟨α, _, Y, π, ⟨H₁, H₂⟩⟩
    unfold CoverDense.inducedTopology
    unfold LocallyCoverDense.inducedTopology
    simp only [ExtrDisc.toCompHaus_obj]
    change _ ∈ GrothendieckTopology.sieves _ _
    apply (coherentTopology.Sieve_iff_hasEffectiveEpiFamily (Sieve.functorPushforward _ S)).mp
    use α, inferInstance
    use fun i => ExtrDisc.toCompHaus.obj (Y i)
    use fun i => ExtrDisc.toCompHaus.map (π i)
    constructor
    · simp only [ExtrDisc.toCompHaus_obj, ExtrDisc.toCompHaus_map]
      -- Show that an `effectiveEpiFamily` pushes forward to one
      simp only [(ExtrDisc.effectiveEpiFamily_tfae _ _).out 0 2] at H₁
      exact CompHaus.effectiveEpiFamily_of_jointly_surjective
          (fun i => (Y i).compHaus) (fun i => π i) H₁
    · exact fun a => Sieve.image_mem_functorPushforward ExtrDisc.toCompHaus S (H₂ a)
  · intro hS
    unfold CoverDense.inducedTopology at hS
    unfold LocallyCoverDense.inducedTopology at hS
    simp only [ExtrDisc.toCompHaus_obj] at hS
    change _ ∈ GrothendieckTopology.sieves _ _ at hS
    replace hS := (coherentTopology.Sieve_iff_hasEffectiveEpiFamily _).mpr hS
    rcases hS with ⟨α, _, Y, π, ⟨H₁, H₂⟩⟩
    use α, inferInstance
    change ∀ a, ∃ (Y₀: ExtrDisc) (π₀ : Y₀⟶ X) (f₀: Y a ⟶ Y₀.compHaus), S.arrows π₀ ∧
        π a = f₀ ≫ ExtrDisc.toCompHaus.map π₀  at H₂
    rw [Classical.skolem] at H₂
    rcases H₂ with ⟨Y₀, H₂⟩
    rw [Classical.skolem] at H₂
    rcases H₂ with ⟨π₀, H₂⟩
    rw [Classical.skolem] at H₂
    rcases H₂ with ⟨f₀, H₂⟩
    use Y₀ , π₀
    constructor
    · simp only [(ExtrDisc.effectiveEpiFamily_tfae _ _).out 0 2]
      simp only [(CompHaus.effectiveEpiFamily_tfae _ _).out 0 2] at H₁
      intro b
      replace H₁ := H₁ b
      rcases H₁ with ⟨i, x, H₁⟩
      use i, f₀ i x
      aesop_cat
    · intro i
      exact (H₂ i).1

lemma coherentTopology_is_induced :
    coherentTopology ExtrDisc.{u} = coverDense.inducedTopology := by
  ext X S
  rw [← coverDense.inducedTopology_Sieve_iff_EffectiveEpiFamily X]
  rw [← coherentTopology.Sieve_iff_hasEffectiveEpiFamily S]


lemma coverPreserving :
  CoverPreserving
    (coherentTopology _)
    (coherentTopology _)
    ExtrDisc.toCompHaus := by
  rw [coherentTopology_is_induced]
  exact LocallyCoverDense.inducedTopology_coverPreserving (CoverDense.locallyCoverDense coverDense)

lemma coverLifting :
  CoverLifting
    (coherentTopology _)
    (coherentTopology _)
    ExtrDisc.toCompHaus := by
  rw [coherentTopology_is_induced]
  exact LocallyCoverDense.inducedTopology_coverLifting (CoverDense.locallyCoverDense coverDense)

noncomputable
def equivalence (A : Type _) [Category.{u+1} A] [HasLimits A] :
    Sheaf (coherentTopology ExtrDisc) A ≌ Condensed.{u} A :=
CoverDense.sheafEquivOfCoverPreservingCoverLifting
  coverDense coverPreserving coverLifting

end ExtrDiscCompHaus

end Condensed